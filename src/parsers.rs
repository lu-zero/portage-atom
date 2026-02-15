use winnow::error::{ContextError, ErrMode};
use winnow::prelude::*;
use winnow::token::take_while;

/// Parse alphanumeric + common special characters
/// Base set: [A-Za-z0-9+_-]
pub(crate) fn parse_ident_base<'s>() -> impl Parser<&'s str, &'s str, ErrMode<ContextError>> {
    take_while(1.., |c: char| {
        c.is_ascii_alphanumeric() || c == '_' || c == '-' || c == '+'
    })
}

/// Parse alphanumeric + common special characters + dot
/// Set: [A-Za-z0-9+_.-]
pub(crate) fn parse_ident_with_dot<'s>() -> impl Parser<&'s str, &'s str, ErrMode<ContextError>> {
    take_while(1.., |c: char| {
        c.is_ascii_alphanumeric() || c == '_' || c == '-' || c == '+' || c == '.'
    })
}

/// Parse alphanumeric + common special characters + @
/// Set: [A-Za-z0-9+_@-]
pub(crate) fn parse_ident_with_at<'s>() -> impl Parser<&'s str, &'s str, ErrMode<ContextError>> {
    take_while(1.., |c: char| {
        c.is_ascii_alphanumeric() || c == '_' || c == '-' || c == '+' || c == '@'
    })
}

/// Parse alphanumeric + common special characters + . and *
/// Set: [A-Za-z0-9+_.*-]
pub(crate) fn parse_ident_with_dot_star<'s>() -> impl Parser<&'s str, &'s str, ErrMode<ContextError>>
{
    take_while(1.., |c: char| {
        c.is_ascii_alphanumeric() || c == '_' || c == '-' || c == '+' || c == '.' || c == '*'
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_ident_base() {
        assert_eq!(parse_ident_base().parse("hello"), Ok("hello"));
        assert_eq!(parse_ident_base().parse("hello-world"), Ok("hello-world"));
        assert_eq!(parse_ident_base().parse("hello_world"), Ok("hello_world"));
        assert_eq!(parse_ident_base().parse("hello+world"), Ok("hello+world"));
        assert!(parse_ident_base().parse("").is_err());
        // Note: single "-" is technically valid for the base parser (no validation)
        // The validation happens in the specific parsers that use this
        assert_eq!(parse_ident_base().parse("-"), Ok("-"));
    }

    #[test]
    fn test_parse_ident_with_dot() {
        assert_eq!(
            parse_ident_with_dot().parse("hello.world"),
            Ok("hello.world")
        );
        assert_eq!(parse_ident_with_dot().parse("dev.lang"), Ok("dev.lang"));
        assert!(parse_ident_with_dot().parse(".invalid").is_ok()); // No validation here
    }

    #[test]
    fn test_parse_ident_with_at() {
        assert_eq!(parse_ident_with_at().parse("user@host"), Ok("user@host"));
        assert_eq!(parse_ident_with_at().parse("flag@"), Ok("flag@"));
    }

    #[test]
    fn test_parse_ident_with_dot_star() {
        assert_eq!(parse_ident_with_dot_star().parse("pkg.*"), Ok("pkg.*"));
        assert_eq!(
            parse_ident_with_dot_star().parse("test-1.2*3"),
            Ok("test-1.2*3")
        );
    }
}
