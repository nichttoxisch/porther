#[cfg(test)] mod test;

use std::{
  collections::HashMap,
  fmt, fs,
  io::{self, Write},
  process,
};

#[derive(Clone, Debug)]
pub struct Loc {
  pub source_path: String,
  pub row:         usize,
  pub col:         usize,
}

impl fmt::Display for Loc {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(
      f,
      "{source_path}:{row}:{col}",
      source_path = self.source_path,
      row = self.row,
      col = self.col
    )?;

    Ok(())
  }
}

#[derive(Clone, Debug)]
pub struct Token {
  pub loc:     Loc,
  pub literal: String,

  pub from: Option<Box<Token>>,
}

impl fmt::Display for Token {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{loc} '{literal}'", loc = self.loc, literal = self.literal)
  }
}

#[derive()]
pub struct Error {
  token: Option<Token>,
  msg:   String,
}

impl fmt::Display for Error {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    if let Some(tok) = &self.token {
      write!(f, "[ERROR] {tok}: {msg}", msg = self.msg)?;
    } else {
      write!(f, "[ERROR]: {msg}", msg = self.msg)?;
    }

    Ok(())
  }
}

impl fmt::Debug for Error {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    if let Some(tok) = &self.token {
      writeln!(f, "[ERROR] {tok}: {msg}", msg = self.msg)?;
      if let Some(from) = &tok.from {
        writeln!(f, "[INFO] Called by: {from}")?;
      }
    } else {
      writeln!(f, "[ERROR]: {msg}", msg = self.msg)?;
    }

    Ok(())
  }
}

impl From<String> for Error {
  fn from(msg: String) -> Self { Self { token: None, msg } }
}

impl From<&str> for Error {
  fn from(msg: &str) -> Self {
    Self {
      token: None,
      msg:   msg.to_owned(),
    }
  }
}

impl From<(&Token, String)> for Error {
  fn from((token, msg): (&Token, String)) -> Self {
    Self {
      token: Some(token.clone()),
      msg,
    }
  }
}

impl From<(&Token, &str)> for Error {
  fn from((token, msg): (&Token, &str)) -> Self {
    Self {
      token: Some(token.clone()),
      msg:   msg.to_owned(),
    }
  }
}

pub struct Source {
  source_path: String,
  source:      String,
}

impl Source {
  pub fn from_string(source: String) -> Self {
    Self {
      source_path: "<prompt>".to_owned(),
      source,
    }
  }

  fn try_from_path(source_path: &str) -> Result<Self, Error> {
    match fs::read_to_string(source_path) {
      Ok(source) => {
        Ok(Self {
          source_path: source_path.to_owned(),
          source,
        })
      }
      Err(err) => {
        Err(format!("Could not open provided source path '{source_path}': {err}",).into())
      }
    }
  }

  pub fn try_into_tokens(&self) -> Result<Tokens, Error> {
    let mut tokens: Vec<Token> = Vec::new();

    for (row, line) in self.source.lines().enumerate() {
      let mut in_string = false;
      let mut literal = String::new();
      let mut col = 1;
      for (i, ch) in line.chars().enumerate() {
        if ch.is_whitespace() || i == line.len() - 1 {
          if i == line.len() - 1 {
            literal.push(ch);
            literal = literal.trim().to_owned();
          }

          if literal.starts_with('\"') {
            in_string = true;

            if literal.len() == 1 {
              literal.push(ch);
              continue;
            }
          }

          if literal.ends_with('\"') {
            in_string = false;
          }

          if in_string {
            literal.push(ch);
            continue;
          }

          if literal.is_empty() {
            col = i + 2;
            literal = String::new();
            continue;
          }

          if literal.starts_with("//") {
            break;
          }

          tokens.push(Token {
            loc:     Loc {
              source_path: self.source_path.clone(),
              row: row + 1,
              col,
            },
            literal: literal.clone(),
            from:    None,
          });

          col = i + 2;
          literal = String::new();

          continue;
        }

        literal.push(ch);
      }

      if in_string {
        let tok = Token {
          loc:     Loc {
            source_path: self.source_path.clone(),
            row: row + 1,
            col,
          },
          from:    None,
          literal: literal.clone(),
        };

        return Err((&tok, "Unclosed string literal").into());
      }
    }

    // for token in &tokens {
    //   println!("{token}");
    // }

    Ok(Tokens { tokens })
  }
}

pub struct Tokens {
  tokens: Vec<Token>,
}

#[allow(unused)]
#[derive(Clone, PartialEq, Eq)]
pub enum Literal {
  Num(i64),
  Ptr(u64),
  Str(String),
  Bool(bool),
}

impl fmt::Debug for Literal {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::Num(n) => write!(f, "{}", *n),
      Self::Ptr(p) => write!(f, "0x{p:x}"),
      Self::Str(s) => write!(f, "\"{s}\""),
      Self::Bool(b) => write!(f, "{b}"),
    }
  }
}

impl fmt::Display for Literal {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::Num(n) => write!(f, "{}", *n),
      Self::Ptr(p) => write!(f, "0x{p:x}"),
      Self::Str(s) => write!(f, "{s}"),
      Self::Bool(b) => write!(f, "{b}"),
    }
  }
}

impl Literal {
  fn typ(&self) -> String {
    String::from(match self {
      Self::Num(_) => "Number",
      Self::Ptr(_) => "Pointer",
      Self::Str(_) => "String",
      Self::Bool(_) => "Boolean",
    })
  }

  fn expect_num(&self, th: &str, token: &Token) -> Result<i64, Error> {
    if let Self::Num(n) = self {
      Ok(*n)
    } else {
      Err(
        (
          token,
          format!("Expected {th} element on stack to be of type Number but got {}", self.typ()),
        )
          .into(),
      )
    }
  }

  fn expect_bool(&self, th: &str, token: &Token) -> Result<bool, Error> {
    if let Self::Bool(b) = self {
      Ok(*b)
    } else {
      Err(
        (
          token,
          format!("Expected {th} element on stack to be of type Boolean but got {}", self.typ()),
        )
          .into(),
      )
    }
  }

  fn expect_ptr(&self, th: &str, token: &Token) -> Result<u64, Error> {
    if let Self::Ptr(b) = self {
      Ok(*b)
    } else {
      Err(
        (
          token,
          format!("Expected {th} element on stack to be of type Pointer but got {}", self.typ()),
        )
          .into(),
      )
    }
  }

  fn expect_str(&self, th: &str, token: &Token) -> Result<String, Error> {
    if let Self::Str(b) = self.clone() {
      Ok(b)
    } else {
      Err(
        (
          token,
          format!("Expected {th} element on stack to be of type String but got {}", self.typ()),
        )
          .into(),
      )
    }
  }
}
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Intrinsic {
  Ident(String),

  Push(Literal),

  Dup,
  Swap,
  Drop,
  Print,
  Println,
  Over,
  Rot,

  Eq,
  Ne,
  Gt,
  Lt,
  Ge,
  Le,

  Add,
  Sub,
  Mul,
  Div,
  Mod,
  Max,

  Shr,
  Shl,
  Or,
  And,
  Not,

  #[allow(unused)]
  Store(usize),

  #[allow(unused)]
  Load(usize),

  #[allow(unused)]
  Cast(Literal),

  Here,
  Dump,

  If,
  Elif,
  Else,
  While,
  Do,
  End,

  Include,
  Proc,
  Const,

  Memory,

  Let,
  In,
  Peek,

  Offset,
  Reset,

  // Syscalls
  Write,
  Open,
  Exit,
}

#[derive(Clone, Debug)]
pub struct Operation {
  pub token:     Token,
  pub intrinsic: Intrinsic,
}

impl Operation {
  pub fn execute(&self, program: &mut Program) -> Result<(), Error> {
    fn compute_arithmetic(
      stack: &mut Stack, token: &Token, f: fn(i64, i64) -> Option<i64>,
    ) -> Result<(), Error> {
      let (a, b) = stack.expect_two(token)?;
      let a = a.expect_num("first", token)?;
      let b = b.expect_num("second", token)?;

      f(b, a).map_or_else(
        || Err((token, "Arithmetic function caused overflow").into()),
        |x| {
          stack.push(Literal::Num(x));
          Ok(())
        },
      )
    }

    fn compute_comparison(
      stack: &mut Stack, token: &Token, f: fn(&i64, &i64) -> bool,
    ) -> Result<(), Error> {
      let (a, b) = stack.expect_two(token)?;
      let a = a.expect_num("first", token)?;
      let b = b.expect_num("second", token)?;

      stack.push(Literal::Bool(f(&b, &a)));

      Ok(())
    }

    fn compute_and(stack: &mut Stack, token: &Token) -> Result<(), Error> {
      let (a, b) = stack.expect_two(token)?;

      match a {
        Literal::Num(a) => {
          if let Literal::Num(b) = b {
            stack.push(Literal::Num(a & b));
            Ok(())
          } else {
            Err(
              (
                token,
                format!(
                  "Expected second element on stack to be of the same type as the first element \
                   (Number) but got {}",
                  b.typ()
                ),
              )
                .into(),
            )
          }
        }
        Literal::Bool(a) => {
          if let Literal::Bool(b) = b {
            stack.push(Literal::Bool(a && b));
            Ok(())
          } else {
            Err(
              (
                token,
                format!(
                  "Expected second element on stack to be of the same type as the first element \
                   (Boolean) but got {}",
                  b.typ()
                ),
              )
                .into(),
            )
          }
        }
        _ => {
          Err(
            (
              token,
              format!(
                "Expected first elements on stack to be of type Number or Bool but got {}",
                a.typ()
              ),
            )
              .into(),
          )
        }
      }
    }

    fn compute_or(stack: &mut Stack, token: &Token) -> Result<(), Error> {
      let (a, b) = stack.expect_two(token)?;

      match a {
        Literal::Num(a) => {
          if let Literal::Num(b) = b {
            stack.push(Literal::Num(a | b));
            Ok(())
          } else {
            Err(
              (
                token,
                format!(
                  "Expected second element on stack to be of the same type as the first element \
                   (Number) but got {}",
                  b.typ()
                ),
              )
                .into(),
            )
          }
        }
        Literal::Bool(a) => {
          if let Literal::Bool(b) = b {
            stack.push(Literal::Bool(a || b));
            Ok(())
          } else {
            Err(
              (
                token,
                format!(
                  "Expected second element on stack to be of the same type as the first element \
                   (Boolean) but got {}",
                  b.typ()
                ),
              )
                .into(),
            )
          }
        }
        _ => {
          Err(
            (
              token,
              format!(
                "Expected first elements on stack to be of type Number or Bool but got {}",
                a.typ()
              ),
            )
              .into(),
          )
        }
      }
    }

    fn jump_to_end(program: &mut Program, token: &Token) -> Result<(), Error> {
      let mut depth: i32 = 0;
      program.state.program_counter += 1;

      loop {
        if let Some(t) = program.operations.get(program.state.program_counter) {
          let t = &t.intrinsic;
          if t == &Intrinsic::While || t == &Intrinsic::If || t == &Intrinsic::Let {
            depth += 1;
          }
          if t == &Intrinsic::End {
            depth -= 1;
          }

          if depth == -1 && t == &Intrinsic::End {
            program.state.program_counter -= 1;
            return Ok(());
          }

          program.state.program_counter += 1;
        } else {
          return Err((token, "No matching end tag").into());
        }
      }
    }

    fn jump_to_else_end(program: &mut Program, token: &Token) -> Result<(), Error> {
      let mut depth = 0;
      program.state.program_counter += 1;

      loop {
        if let Some(t) = program.operations.get(program.state.program_counter) {
          let t = &t.intrinsic;
          if t == &Intrinsic::While || t == &Intrinsic::If || t == &Intrinsic::Let {
            depth += 1;
          }

          if t == &Intrinsic::End {
            depth -= 1;
          }

          if depth == -1 && t == &Intrinsic::End {
            program.state.block_stack.pop().expect("unreachable");

            return Ok(());
          }

          if depth == 0 && t == &Intrinsic::Else {
            return Ok(());
          }

          program.state.program_counter += 1;
        } else {
          return Err((token, "No matching end tag").into());
        }
      }
    }

    fn expect_ident(program: &mut Program, token: &Token) -> Result<String, Error> {
      if let Some(ident) = program.operations.get(program.state.program_counter + 1).cloned() {
        if let Intrinsic::Ident(ident) = &ident.intrinsic {
          return Ok(ident.clone());
        }
        return Err((token, "No identifier is provided").into());
      }
      Err((token, "No identifier is provided").into())
    }

    let stack = &mut program.state.stack;
    let token = &self.token;

    match &self.intrinsic {
      Intrinsic::Ident(ident) => {
        if let Some(operations) = program.state.const_table.get(ident).cloned() {
          for mut inner in operations {
            inner.token.from = Some(Box::new(self.token.clone()));
            inner.execute(program)?;
          }
          return Ok(());
        }
        if let Some(funcall) = program.state.proc_table.get(ident) {
          program.state.block_stack.push((Block::Proc, program.state.program_counter));
          program.state.program_counter = *funcall;
          return Ok(());
        }

        if let Some(literal) = program.state.let_bindings.get(ident) {
          program.state.stack.push(literal.clone());
          return Ok(());
        }

        return Err((token, "Unknown word").into());
      }

      Intrinsic::Push(value) => stack.push(value.clone()),
      Intrinsic::Dup => {
        let a = stack.expect_one(token)?;
        stack.push(a.clone());
        stack.push(a);
      }
      Intrinsic::Swap => {
        let (a, b) = stack.expect_two(token)?;
        stack.push(a);
        stack.push(b);
      }
      Intrinsic::Drop => {
        let _: Literal = stack.expect_one(token)?;
      }
      Intrinsic::Print => {
        let a = stack.expect_one(token)?;
        print!("{a} ");
      }
      Intrinsic::Println => {
        let a = stack.expect_one(token)?;
        println!("{a}");
      }
      Intrinsic::Over => {
        let (a, b) = stack.expect_two(token)?;
        stack.push(b.clone());
        stack.push(a);
        stack.push(b);
      }
      Intrinsic::Rot => {
        let (a, b, c) = stack.expect_three(token)?;
        stack.push(b);
        stack.push(a);
        stack.push(c);
      }

      Intrinsic::Eq => compute_comparison(stack, token, i64::eq)?,
      Intrinsic::Ne => compute_comparison(stack, token, i64::ne)?,
      Intrinsic::Gt => compute_comparison(stack, token, i64::gt)?,
      Intrinsic::Lt => compute_comparison(stack, token, i64::lt)?,
      Intrinsic::Ge => compute_comparison(stack, token, i64::ge)?,
      Intrinsic::Le => compute_comparison(stack, token, i64::le)?,

      Intrinsic::Add => {
        let (a, b) = stack.expect_two(token)?;
        match a {
          Literal::Num(a) => {
            match b {
              Literal::Num(b) => stack.push(Literal::Num(a + b)),
              Literal::Ptr(b) => {
                stack.push(Literal::Ptr(a as u64 + b));
              }
              _ => {
                return Err(
                  (
                    token,
                    format!(
                      "Expected second element on stack to be of type Number or Pointer but got {}",
                      b.typ()
                    ),
                  )
                    .into(),
                );
              }
            }
          }
          Literal::Ptr(a) => {
            match b {
              Literal::Num(b) => stack.push(Literal::Ptr(a + b as u64)),
              Literal::Ptr(b) => {
                stack.push(Literal::Ptr(a + b));
              }
              _ => {
                return Err(
                  (
                    token,
                    format!(
                      "Expected second element on stack to be of type Number or Pointer but got {}",
                      b.typ()
                    ),
                  )
                    .into(),
                );
              }
            }
          }
          _ => {
            return Err(
              (
                token,
                format!(
                  "Expected first element on stack to be of type Number or Pointer but got {}",
                  a.typ()
                ),
              )
                .into(),
            );
          }
        }
      }
      Intrinsic::Sub => {
        let (a, b) = stack.expect_two(token)?;
        match a {
          Literal::Num(a) => {
            match b {
              Literal::Num(b) => stack.push(Literal::Num(b - a)),
              Literal::Ptr(b) => {
                stack.push(Literal::Ptr(b - a as u64));
              }
              _ => {
                return Err(
                  (
                    token,
                    format!(
                      "Expected second element on stack to be of type Number or Pointer but got {}",
                      b.typ()
                    ),
                  )
                    .into(),
                );
              }
            }
          }
          Literal::Ptr(a) => {
            match b {
              Literal::Num(b) => stack.push(Literal::Ptr(b as u64 - a)),
              Literal::Ptr(b) => {
                stack.push(Literal::Ptr(b - a));
              }
              _ => {
                return Err(
                  (
                    token,
                    format!(
                      "Expected second element on stack to be of type Number or Pointer but got {}",
                      b.typ()
                    ),
                  )
                    .into(),
                );
              }
            }
          }
          _ => {
            return Err(
              (
                token,
                format!(
                  "Expected first element on stack to be of type Number or Pointer but got {}",
                  a.typ()
                ),
              )
                .into(),
            );
          }
        }
      }
      Intrinsic::Mul => compute_arithmetic(stack, token, i64::checked_mul)?,
      Intrinsic::Div => compute_arithmetic(stack, token, i64::checked_div)?,
      Intrinsic::Mod => compute_arithmetic(stack, token, i64::checked_rem)?,
      Intrinsic::Max => {
        compute_arithmetic(stack, token, |a, b| Some(i64::max(a, b)))?;
      }
      Intrinsic::Shr => compute_arithmetic(stack, token, |a, b| Some(a >> b))?,
      Intrinsic::Shl => compute_arithmetic(stack, token, |a, b| Some(a << b))?,

      Intrinsic::Or => compute_or(stack, token)?,
      Intrinsic::And => compute_and(stack, token)?,
      Intrinsic::Not => {
        let a = stack.expect_one(token)?.expect_bool("first", token)?;
        stack.push(Literal::Bool(!a));
      }

      Intrinsic::Store(n) => {
        let (addr, value) = program.state.stack.expect_two(token)?;
        let addr: usize = addr.expect_ptr("first", token)? as usize;
        let value: u8 = value.expect_num("second", token)? as u8;

        if addr >= program.state.memory.len() {
          // TODO: Flag for memory capacity
          return Err(
            (token, format!("index {} out of bounds [0:{}]", addr, program.state.memory.len()))
              .into(),
          );
        }

        match n {
          8 => program.state.memory[addr] = value,
          _ => todo!(),
        }
      }
      Intrinsic::Load(n) => {
        let addr = program.state.stack.expect_one(token)?;
        let addr = addr.expect_ptr("first", token)? as usize;

        if addr >= program.state.memory.len() {
          // TODO: Flag for memory capacity
          return Err(
            (token, format!("index {} out of bounds [0:{}]", addr, program.state.memory.len()))
              .into(),
          );
        }

        match n {
          8 => program.state.stack.push(Literal::Num(i64::from(program.state.memory[addr]))),
          _ => todo!(),
        }
      }
      Intrinsic::Cast(_) => todo!(),

      Intrinsic::Here => todo!(),
      Intrinsic::Dump => {
        for s in &stack.stack {
          print!("{s:?} ");
        }
        println!();
      }

      Intrinsic::If => {
        program.state.block_stack.push((Block::If, program.state.program_counter));

        let cnd = stack.expect_one(token)?.expect_bool("first", token)?;

        if !cnd {
          jump_to_else_end(program, token)?;
        }
      }

      Intrinsic::Elif => {
        let cnd = stack.expect_one(token)?.expect_bool("first", token)?;

        if !cnd {
          jump_to_else_end(program, token)?;
        }
      }

      Intrinsic::Else => jump_to_end(program, token)?,

      Intrinsic::While => {
        program.state.block_stack.push((Block::While, program.state.program_counter));
      }

      Intrinsic::Do => {
        let cnd = stack.expect_one(token)?.expect_bool("first", token)?;

        if !cnd {
          jump_to_end(program, token)?;
          program.state.program_counter += 1;
          if matches!(program.state.block_stack.pop(), None) {
            return Err(("").into());
          };
        }
      }

      Intrinsic::End => {
        if let Some((b, data)) = program.state.block_stack.pop() {
          // println!("End of {b:?}");

          match b {
            Block::If => {}
            Block::While => {
              program.state.block_stack.push((b, data));
              program.state.program_counter = data;
            }
            Block::Proc => {
              program.state.program_counter = data;
            }
            Block::Let => {
              program.state.let_bindings.pop(data);
            }
          }
        } else {
          return Err((token, "Headless end").into());
        }
      }

      Intrinsic::Include => {
        if let Some(t) = program.operations.get(program.state.program_counter + 1) {
          program.state.program_counter += 1;
          if let Intrinsic::Push(Literal::Str(source_path)) = &t.intrinsic {
            let include = Source::try_from_path(source_path)?.try_into_tokens()?.into_program();

            for (i, operation) in include.operations.into_iter().enumerate() {
              program.operations.insert(program.state.program_counter + i + 1, operation);
            }
          }

          // for operation in &program.operations {
          //   println!("{}", operation.token);
          // }
        } else {
          return Err((token, "No source path is provided").into());
        }
      }

      Intrinsic::Proc => {
        let ident = expect_ident(program, token)?;
        if program.state.proc_table.insert(ident, program.state.program_counter + 1).is_some() {
          return Err((token, "Procedure cant be redefined").into());
        }

        jump_to_end(program, token)?;
        program.state.program_counter += 1;
      }

      Intrinsic::Const => {
        let ident = expect_ident(program, token)?;

        let start = program.state.program_counter + 2;
        jump_to_end(program, token)?;
        program.state.program_counter += 1;
        let end = program.state.program_counter;

        // TODO: Check in proc table

        let mut operations = program.operations.get(start..end).expect("unreachable").to_vec();

        operations
          .iter_mut()
          .for_each(|operation| operation.token.from = Some(Box::new(self.token.clone())));

        if program.state.const_table.insert(ident, operations).is_some() {
          return Err((token, "Constant cant be redefined").into());
        }
      }

      Intrinsic::Memory => {
        program.state.stack.push(Literal::Ptr(1));
      }

      Intrinsic::In => {
        todo!()
      }

      Intrinsic::Let => {
        program.state.program_counter += 1;

        let mut identifiers: Vec<String> = vec![];

        if let Some(mut cur) = program.operations.get(program.state.program_counter) {
          while cur.intrinsic != Intrinsic::In {
            if let Some(op) = program.operations.get(program.state.program_counter) {
              if let Intrinsic::Ident(ident) = &op.intrinsic {
                if identifiers.contains(ident) {
                  return Err((&cur.token, "Identifier already defined").into());
                }
                identifiers.push(ident.clone());
              }
            } else {
              return Err((token, "Expected identifier").into());
            }
            program.state.program_counter += 1;
            cur = program.operations.get(program.state.program_counter).expect("unreachable");
          }
        } else {
          return Err((token, "Let bindings expected").into());
        }

        identifiers.reverse();
        let len = identifiers.len();

        for ident in identifiers {
          let value = program.state.stack.expect_one(token)?;
          program.state.let_bindings.push(ident, value);
        }

        program.state.block_stack.push((Block::Let, len));
      }
      Intrinsic::Peek => todo!(),

      Intrinsic::Offset => todo!(),
      Intrinsic::Reset => return Err("Not implemented".into()),

      Intrinsic::Write => {
        let (fd, ptr, count) = stack.expect_three(token)?;
        let fd = fd.expect_num("first", token)? as usize;
        let ptr = ptr.expect_ptr("second", token)? as usize;
        let count = count.expect_num("third", token)? as usize;

        if ptr + count >= program.state.memory.len() {
          return Err(
            (
              token,
              format!(
                "index [{}:{}] out of bounds [0:{}]",
                ptr,
                ptr + count,
                program.state.memory.len()
              ),
            )
              .into(),
          );
        }

        let buf = program.state.memory.get(ptr..ptr + count).expect("unreachable");

        if let Some(fd) = program.state.file_descriptors.get_mut(&fd) {
          if let Err(err) = fd.write(buf) {
            return Err((token, format!("Could not write to file: {err}")).into());
          }
        } else {
          return Err((token, "Unknown file descriptor").into());
        }
      }
      Intrinsic::Open => {
        let path = stack.expect_one(token)?;
        let path = path.expect_str("first", token)?;

        match fs::OpenOptions::new().read(true).write(true).create(true).open(path) {
          Ok(fd) => {
            let mut n: usize = rand::random::<u8>() as usize;
            while program.state.file_descriptors.contains_key(&n) {
              n = rand::random();
            }

            program.state.file_descriptors.insert(n, Box::new(fd));
            stack.push(Literal::Num(n as i64));
          }
          Err(_) => stack.push(Literal::Num(-1)),
        }
      }
      Intrinsic::Exit => {
        let code = stack.expect_one(token)?;
        let code = code.expect_num("first", token)?;
        process::exit(code.try_into().expect("stfu clippy"));
      }
    }

    Ok(())
  }
}

#[derive(Debug)]
pub enum Block {
  If,
  While,
  Let,

  Proc,
}

type Pc = usize;

#[derive(Default)]
pub struct Stack {
  pub stack: Vec<Literal>,
}

impl Stack {
  fn expect_one(&mut self, token: &Token) -> Result<Literal, Error> {
    self.stack.pop().map_or_else(
      || Err((token, "Expected at least one element on stack but got zero").into()),
      Ok,
    )
  }

  fn expect_two(&mut self, token: &Token) -> Result<(Literal, Literal), Error> {
    if let Some(a) = self.stack.pop() {
      self.stack.pop().map_or_else(
        || Err((token, "Expected at least two elements on stack but got one").into()),
        |b| Ok((a, b)),
      )
    } else {
      Err((token, "Expected at least two elements on stack but got zero").into())
    }
  }

  fn expect_three(&mut self, token: &Token) -> Result<(Literal, Literal, Literal), Error> {
    if let Some(a) = self.stack.pop() {
      if let Some(b) = self.stack.pop() {
        self.stack.pop().map_or_else(
          || Err((token, "Expected at least three elements on stack but got two").into()),
          |c| Ok((a, b, c)),
        )
      } else {
        Err((token, "Expected at least three elements on stack but got one").into())
      }
    } else {
      Err((token, "Expected at least three elements on stack but got zero").into())
    }
  }

  fn push(&mut self, value: Literal) { self.stack.push(value) }
}

#[derive(Default, Debug)]
pub struct LetBindings {
  bindings: Vec<(String, Literal)>,
}

impl LetBindings {
  #[allow(dead_code)]
  fn contains(&self, key: &String) -> bool { self.bindings.iter().any(|(k, _)| k == key) }

  fn get(&self, key: &String) -> Option<&Literal> {
    return if let Some((_, literal)) = self.bindings.iter().rev().find(|(k, _)| k == key) {
      Some(literal)
    } else {
      None
    };
  }

  fn push(&mut self, key: String, value: Literal) { self.bindings.push((key, value)) }

  fn pop(&mut self, n: usize) {
    for _ in 0..n {
      self.bindings.pop().expect("unreachable");
    }
  }
}

#[derive(Default)]
#[allow(unused)]
pub struct ProgramState {
  pub program_counter:  Pc,
  pub block_stack:      Vec<(Block, Pc)>,
  pub call_stack:       Vec<Pc>,
  pub const_table:      HashMap<String, Vec<Operation>>,
  pub proc_table:       HashMap<String, Pc>,
  pub let_bindings:     LetBindings,
  pub stack:            Stack,
  pub memory:           Vec<u8>,
  pub file_descriptors: HashMap<usize, Box<dyn io::Write>>,
}

pub struct Program {
  pub operations: Vec<Operation>,
  pub state:      ProgramState,
}

impl Tokens {
  pub fn into_operations(self) -> Vec<Operation> {
    let mut intrinsics: Vec<Intrinsic> = Vec::new();

    for token in &self.tokens {
      use Intrinsic as I;

      match token.literal.as_str() {
        "dup" => intrinsics.push(I::Dup),
        "swap" => intrinsics.push(I::Swap),
        "drop" => intrinsics.push(I::Drop),
        "print" => intrinsics.push(I::Print),
        "println" => intrinsics.push(I::Println),
        "over" => intrinsics.push(I::Over),
        "rot" => intrinsics.push(I::Rot),

        "eq" | "==" => intrinsics.push(I::Eq),
        "ne" | "!=" => intrinsics.push(I::Ne),
        "gt" | ">" => intrinsics.push(I::Gt),
        "lt" | "<" => intrinsics.push(I::Lt),
        "ge" | ">=" => intrinsics.push(I::Ge),
        "le" | "<=" => intrinsics.push(I::Le),

        "add" => intrinsics.push(I::Add),
        "sub" => intrinsics.push(I::Sub),
        "mul" => intrinsics.push(I::Mul),
        "div" => intrinsics.push(I::Div),
        "mod" => intrinsics.push(I::Mod),
        "max" => intrinsics.push(I::Max),

        "@8" => intrinsics.push(I::Load(8)),
        "!8" => intrinsics.push(I::Store(8)),

        "true" => intrinsics.push(I::Push(Literal::Bool(true))),
        "false" => intrinsics.push(I::Push(Literal::Bool(false))),

        "shr" | ">>" => intrinsics.push(I::Shr),
        "shl" | "<<" => intrinsics.push(I::Shl),
        "or" => intrinsics.push(I::Or),
        "and" => intrinsics.push(I::And),
        "not" => intrinsics.push(I::Not),

        "here" => intrinsics.push(I::Here),
        "dump" | "?" => intrinsics.push(I::Dump),

        "if" => intrinsics.push(I::If),
        "if*" => intrinsics.push(I::Elif),
        "else" => intrinsics.push(I::Else),
        "while" => intrinsics.push(I::While),
        "do" => intrinsics.push(I::Do),
        "end" => intrinsics.push(I::End),

        "include" => intrinsics.push(I::Include),
        "proc" => intrinsics.push(I::Proc),
        "const" => intrinsics.push(I::Const),

        "memory" => intrinsics.push(I::Memory),

        "in" => intrinsics.push(I::In),
        "let" => intrinsics.push(I::Let),
        "peek" => intrinsics.push(I::Peek),

        "offset" => intrinsics.push(I::Offset),
        "reset" => intrinsics.push(I::Reset),

        "write" => intrinsics.push(I::Write),
        "open" => intrinsics.push(I::Open),
        "exit" => intrinsics.push(I::Exit),

        word => {
          if word.starts_with('"') {
            intrinsics.push(I::Push(Literal::Str(
              word.get(1..word.len() - 1).expect("to error before").to_owned(),
            )));
            continue;
          }

          if let Ok(n) = word.parse::<i64>() {
            intrinsics.push(I::Push(Literal::Num(n)));
            continue;
          }

          intrinsics.push(I::Ident(word.to_owned()));
        }
      }
    }

    let program = intrinsics
      .iter()
      .zip(&self.tokens)
      .map(|(intrinsic, token)| {
        Operation {
          token:     token.clone(),
          intrinsic: intrinsic.clone(),
        }
      })
      .collect();

    program
  }

  pub fn into_program(self) -> Program {
    Program {
      operations: self.into_operations(),
      state:      ProgramState::default(),
    }
  }
}

impl Program {
  pub fn step(&mut self) -> Result<(), Error> {
    let instr = self.operations.get(self.state.program_counter).expect("unreachable").clone();

    // println!("{}", instr.token);
    // println!("{:#?}", self.state.block_stack);

    instr.execute(self)?;

    self.state.program_counter += 1;

    Ok(())
  }

  pub fn run(&mut self) -> Result<(), Error> {
    self.state.memory = Vec::new();
    self.state.memory.resize(640_000, 0);

    self.state.file_descriptors.insert(1, Box::new(io::stdout()));
    self.state.file_descriptors.insert(2, Box::new(io::stderr()));

    loop {
      if self.state.program_counter >= self.operations.len() {
        return Ok(());
      }

      self.step()?;
    }
  }
}

pub fn interpret(source_path: &str) -> Result<(), Error> {
  Source::try_from_path(source_path)?.try_into_tokens()?.into_program().run()
}
