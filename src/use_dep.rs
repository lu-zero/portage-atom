use std::fmt;
use std::str::FromStr;

use winnow::combinator::{alt, cut_err, delimited, opt, preceded, separated, terminated};
use winnow::error::{ContextError, ErrMode, StrContext};
use winnow::prelude::*;
use winnow::token::take_while;

use crate::error::{Error, Result};

/// Default value for a USE flag that is not defined by the dependency package
///
/// When a package does not define a particular USE flag in its IUSE, the
/// default annotation specifies what value the package manager should assume.
///
/// See [PMS 8.3.4](https://projects.gentoo.org/pms/9/pms.html#style-and-style-use-dependencies).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UseDefault {
    /// `(+)` — assume the flag is enabled if not defined by the package.
    Enabled,
    /// `(-)` — assume the flag is disabled if not defined by the package.
    Disabled,
}

impl fmt::Display for UseDefault {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            UseDefault::Enabled => write!(f, "(+)"),
            UseDefault::Disabled => write!(f, "(-)"),
        }
    }
}

/// The kind of constraint a USE dependency expresses
///
/// See [PMS 8.3.4](https://projects.gentoo.org/pms/9/pms.html#style-and-style-use-dependencies).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UseDepKind {
    /// `[flag]` — the dependency's flag must be enabled.
    Enabled,
    /// `[-flag]` — the dependency's flag must be disabled.
    Disabled,
    /// `[flag?]` — if the *parent's* flag is enabled, the dependency's flag
    /// must also be enabled; otherwise unconstrained.
    Conditional,
    /// `[!flag?]` — if the *parent's* flag is disabled, the dependency's flag
    /// must be enabled; otherwise unconstrained.
    ConditionalInverse,
    /// `[flag=]` — the dependency's flag must match the parent's flag state
    /// (both enabled or both disabled).
    Equal,
    /// `[!flag=]` — the dependency's flag must be the opposite of the
    /// parent's flag state.
    EqualInverse,
}

impl fmt::Display for UseDepKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            UseDepKind::Enabled => Ok(()),
            UseDepKind::Disabled => write!(f, "-"),
            UseDepKind::Conditional => write!(f, "?"),
            UseDepKind::ConditionalInverse => write!(f, "!?"),
            UseDepKind::Equal => write!(f, "="),
            UseDepKind::EqualInverse => write!(f, "!="),
        }
    }
}

/// A single USE flag constraint within a dependency atom
///
/// Appears inside brackets in dependency strings, e.g. `[ssl,-debug,python?]`.
/// Each `UseDep` constrains one flag on the dependency package, optionally
/// relative to the parent package's flag state.
///
/// See [PMS 8.3.4](https://projects.gentoo.org/pms/9/pms.html#style-and-style-use-dependencies).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct UseDep {
    /// The USE flag name (e.g. `ssl`, `debug`, `python_targets_python3_12`).
    pub flag: String,
    /// The kind of constraint this dependency expresses.
    pub kind: UseDepKind,
    /// Optional default value (`(+)` or `(-)`) for when the flag is not
    /// defined by the dependency package.
    pub default: Option<UseDefault>,
}

impl UseDep {
    pub fn new(flag: impl Into<String>, kind: UseDepKind) -> Self {
        UseDep {
            flag: flag.into(),
            kind,
            default: None,
        }
    }

    pub fn with_default(flag: impl Into<String>, kind: UseDepKind, default: UseDefault) -> Self {
        UseDep {
            flag: flag.into(),
            kind,
            default: Some(default),
        }
    }

    /// Parse single USE dependency (without brackets)
    pub fn parse(input: &str) -> Result<Self> {
        parse_use_dep_item()
            .parse(input)
            .map_err(|e| Error::InvalidUseDep(format!("{}: {}", input, e)))
    }
}

impl fmt::Display for UseDep {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.kind {
            UseDepKind::Disabled => write!(f, "-")?,
            UseDepKind::ConditionalInverse | UseDepKind::EqualInverse => write!(f, "!")?,
            _ => {}
        }

        write!(f, "{}", self.flag)?;

        // PMS 8.3.4: default immediately follows the flag name, before ?/=
        if let Some(default) = self.default {
            write!(f, "{}", default)?;
        }

        match self.kind {
            UseDepKind::Conditional | UseDepKind::ConditionalInverse => write!(f, "?")?,
            UseDepKind::Equal | UseDepKind::EqualInverse => write!(f, "=")?,
            _ => {}
        }

        Ok(())
    }
}

impl PartialOrd for UseDep {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for UseDep {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.flag.cmp(&other.flag)
    }
}

impl FromStr for UseDep {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        Self::parse(s)
    }
}

// Winnow parsers

/// Parse USE flag name
fn parse_use_flag<'s>() -> impl Parser<&'s str, String, ErrMode<ContextError>> {
    take_while(1.., |c: char| {
        c.is_ascii_alphanumeric() || c == '_' || c == '-' || c == '+' || c == '@'
    })
    .map(|s: &str| s.to_string())
}

/// Parse USE default
fn parse_use_default<'s>() -> impl Parser<&'s str, UseDefault, ErrMode<ContextError>> {
    alt((
        "(+)".value(UseDefault::Enabled),
        "(-)".value(UseDefault::Disabled),
    ))
}

/// Parse single USE dependency item
pub(crate) fn parse_use_dep_item<'s>() -> impl Parser<&'s str, UseDep, ErrMode<ContextError>> {
    alt((
        // !flag? - inverse conditional
        (
            preceded('!', parse_use_flag()),
            opt(parse_use_default()),
            '?',
        )
            .map(|(flag, default, _)| UseDep {
                flag,
                kind: UseDepKind::ConditionalInverse,
                default,
            }),
        // !flag= - inverse equal
        (
            preceded('!', parse_use_flag()),
            opt(parse_use_default()),
            '=',
        )
            .map(|(flag, default, _)| UseDep {
                flag,
                kind: UseDepKind::EqualInverse,
                default,
            }),
        // -flag - disabled
        (preceded('-', parse_use_flag()), opt(parse_use_default())).map(|(flag, default)| UseDep {
            flag,
            kind: UseDepKind::Disabled,
            default,
        }),
        // flag? - conditional
        (parse_use_flag(), opt(parse_use_default()), '?').map(|(flag, default, _)| UseDep {
            flag,
            kind: UseDepKind::Conditional,
            default,
        }),
        // flag= - equal
        (parse_use_flag(), opt(parse_use_default()), '=').map(|(flag, default, _)| UseDep {
            flag,
            kind: UseDepKind::Equal,
            default,
        }),
        // flag - enabled
        (parse_use_flag(), opt(parse_use_default())).map(|(flag, default)| UseDep {
            flag,
            kind: UseDepKind::Enabled,
            default,
        }),
    ))
}

/// Parse USE dependencies (with brackets)
pub(crate) fn parse_use_deps<'s>() -> impl Parser<&'s str, Vec<UseDep>, ErrMode<ContextError>> {
    delimited(
        '[',
        cut_err(terminated(
            separated(0.., parse_use_dep_item(), ','),
            opt(','),
        )),
        cut_err(']'),
    )
    .context(StrContext::Label("use deps"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_use_dep_enabled() {
        let dep = UseDep::parse("ssl").unwrap();
        assert_eq!(dep.flag, "ssl");
        assert_eq!(dep.kind, UseDepKind::Enabled);
        assert_eq!(dep.to_string(), "ssl");
    }

    #[test]
    fn test_use_dep_disabled() {
        let dep = UseDep::parse("-debug").unwrap();
        assert_eq!(dep.flag, "debug");
        assert_eq!(dep.kind, UseDepKind::Disabled);
        assert_eq!(dep.to_string(), "-debug");
    }

    #[test]
    fn test_use_dep_conditional() {
        let dep = UseDep::parse("python?").unwrap();
        assert_eq!(dep.flag, "python");
        assert_eq!(dep.kind, UseDepKind::Conditional);
        assert_eq!(dep.to_string(), "python?");
    }

    #[test]
    fn test_use_dep_with_default() {
        let dep = UseDep::parse("ssl(+)").unwrap();
        assert_eq!(dep.flag, "ssl");
        assert_eq!(dep.kind, UseDepKind::Enabled);
        assert_eq!(dep.default, Some(UseDefault::Enabled));
        assert_eq!(dep.to_string(), "ssl(+)");
    }

    #[test]
    fn test_use_deps_list() {
        let deps = parse_use_deps().parse("[ssl,-debug,python?]").unwrap();
        assert_eq!(deps.len(), 3);
        assert_eq!(deps[0].flag, "ssl");
        assert_eq!(deps[1].flag, "debug");
        assert_eq!(deps[1].kind, UseDepKind::Disabled);
        assert_eq!(deps[2].flag, "python");
        assert_eq!(deps[2].kind, UseDepKind::Conditional);
    }

    // Issue 1: Empty USE dep brackets []
    #[test]
    fn test_empty_use_deps() {
        let deps = parse_use_deps().parse("[]").unwrap();
        assert!(deps.is_empty());
    }

    // Issue 2: USE dep defaults (+) and (-)
    #[test]
    fn test_use_dep_with_defaults() {
        let dep = UseDep::parse("unicode(+)").unwrap();
        assert_eq!(dep.flag, "unicode");
        assert_eq!(dep.kind, UseDepKind::Enabled);
        assert_eq!(dep.default, Some(UseDefault::Enabled));
        assert_eq!(dep.to_string(), "unicode(+)");

        let dep = UseDep::parse("unicode(-)").unwrap();
        assert_eq!(dep.flag, "unicode");
        assert_eq!(dep.kind, UseDepKind::Enabled);
        assert_eq!(dep.default, Some(UseDefault::Disabled));
        assert_eq!(dep.to_string(), "unicode(-)");

        let dep = UseDep::parse("icu(+)").unwrap();
        assert_eq!(dep.flag, "icu");
        assert_eq!(dep.kind, UseDepKind::Enabled);
        assert_eq!(dep.default, Some(UseDefault::Enabled));
        assert_eq!(dep.to_string(), "icu(+)");
    }

    // Issue 4: Trailing comma in USE dep list
    #[test]
    fn test_use_deps_with_trailing_comma() {
        let deps = parse_use_deps().parse("[introspection?,]").unwrap();
        assert_eq!(deps.len(), 1);
        assert_eq!(deps[0].flag, "introspection");
        assert_eq!(deps[0].kind, UseDepKind::Conditional);
    }
}
