mod porth;

use std::{env, io::Write};

use porth::Error;

#[allow(unused)]
fn usage() {
  eprintln!("Usage: {} <source_path> [options]", env::args().next().expect("program is provided"));
  eprintln!("Options:");
  eprintln!("    -h --help       to print this usage to Stderr");
}

fn prompt(name: &str) -> Result<String, Error> {
  let mut line = String::new();
  print!("{name}");

  if let Err(err) = std::io::stdout().flush() {
    return Err(format!("Could not flush stdout: {err}").into());
  }

  if let Err(err) = std::io::stdin().read_line(&mut line) {
    return Err(format!("Could not read stdin: {err}").into());
  }

  return Ok(line.trim().to_owned());
}

fn main() -> Result<(), Error> {
  let mut args = env::args();
  args.next().expect("program is provided");

  // TODO: Prompt option if no path

  if let Some(source_path) = args.next() {
    return porth::interpret(&source_path);
  }

  let mut program = porth::Source::from_string(String::new()).try_into_tokens()?.into_program();

  let mut prev_stack = program.state.stack.stack.clone();

  loop {
    let input = prompt("porth> ")?;
    let operations = porth::Source::from_string(input).try_into_tokens()?.into_operations();

    program.operations.append(&mut operations.clone());

    if let Err(err) = program.run() {
      println!("{err}");
    }

    if program.state.stack.stack != prev_stack {
      porth::Operation::execute(
        &porth::Operation {
          token:     porth::Token {
            loc:     porth::Loc {
              source_path: "<prompt>".to_owned(),
              row:         0,
              col:         0,
            },
            from:    None,
            literal: "Intern".to_owned(),
          },
          intrinsic: porth::Intrinsic::Dump,
        },
        &mut program,
      )?;

      prev_stack = program.state.stack.stack.clone();
    }

    program.state.program_counter = program.operations.len();
  }
}
