mod tokenizing {
  use crate::porth;

  fn tokens_from_str(test_source: &str) -> Vec<porth::Token> {
    porth::Source::try_into_tokens(&porth::Source {
      source_path: String::new(),
      source:      test_source.to_owned(),
    })
    .expect("the tokenizer to be able to parse this")
    .tokens
  }

  mod comments {
    use crate::porth::test::tokenizing::tokens_from_str;

    #[test]
    fn test_comments_0() {
      let tokens = tokens_from_str(r#"  10 // " Hello, World!\n" "#);
      assert_eq!(tokens.len(), 1);
    }

    #[test]
    fn test_comments_1() {
      let tokens = tokens_from_str(r#"//  10 // " Hello, World!\n" "#);
      assert_eq!(tokens.len(), 0);
    }

    #[test]
    fn test_comments_3() {
      let tokens = tokens_from_str(r#"10 " Hello, World!\n" // lol "#);
      assert_eq!(tokens.len(), 2);
    }
  }

  mod location {
    use crate::porth::test::tokenizing::tokens_from_str;

    #[test]
    fn test_location() {
      let tokens = tokens_from_str(
        r#"   10 add
        20      " Hey! " "#,
      );

      let token_0 = tokens.get(0).expect("the 0th token");
      let token_1 = tokens.get(1).expect("the 1st token");
      let token_2 = tokens.get(2).expect("the 2nd token");
      let token_3 = tokens.get(3).expect("the 3rd token");

      assert_eq!(token_0.literal, r#"10"#);
      assert_eq!(token_1.literal, r#"add"#);
      assert_eq!(token_2.literal, r#"20"#);
      assert_eq!(token_3.literal, r#"" Hey! ""#);

      assert_eq!(token_0.loc.to_string(), ":1:4");
      assert_eq!(token_1.loc.to_string(), ":1:7");
      assert_eq!(token_2.loc.to_string(), ":2:9");
      assert_eq!(token_3.loc.to_string(), ":2:17");
    }
  }

  mod string_literal {
    use crate::porth::test::tokenizing::tokens_from_str;

    #[test]
    fn test_string() {
      let tokens = tokens_from_str(r#""Hello" add"#);
      let token = tokens.get(0).expect("the first token");

      assert_eq!(token.literal, r#""Hello""#);
    }

    #[test]
    fn test_string_with_whitespace() {
      let tokens = tokens_from_str(r#"   " Hello, World!\n" "#);
      let token = tokens.get(0).expect("the first token");

      assert_eq!(token.literal, r#"" Hello, World!\n""#);
    }

    #[test]
    fn test_empty_string() {
      let tokens = tokens_from_str(r#"   "" "#);
      let token = tokens.get(0).expect("the first token");

      assert_eq!(token.literal, r#""""#);
    }
  }
}
