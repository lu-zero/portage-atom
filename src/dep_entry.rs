use std::fmt;

use winnow::ascii::multispace0;
use winnow::combinator::{alt, cut_err, delimited, dispatch, opt, peek, preceded, repeat};
use winnow::error::{ContextError, ErrMode, StrContext};
use winnow::prelude::*;
use winnow::token::{any, take_while};

use crate::dep::{parse_dep, Dep};
use crate::error::{Error, Result};

/// Structured dependency tree entry.
///
/// Represents the three forms that appear in ebuild `*DEPEND` variables
/// (PMS 8.2): bare atoms, USE-conditional groups, and `|| ()` any-of groups.
///
/// See [PMS 8.2](https://projects.gentoo.org/pms/9/pms.html#dependency-specification-format).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DepEntry {
    /// A single dependency atom.
    Atom(Dep),
    /// `flag? ( children )` or `!flag? ( children )` conditional group.
    UseConditional {
        /// USE flag name.
        flag: String,
        /// `true` for `!use?` (negated conditional).
        negate: bool,
        /// Dependencies guarded by this flag.
        children: Vec<DepEntry>,
    },
    /// `|| ( a b c )` — any one of the children satisfies the dependency.
    AnyOf(Vec<DepEntry>),
}

impl DepEntry {
    /// Parse a full dependency string into a list of entries.
    ///
    /// Accepts the format used in ebuild `*DEPEND` variables: whitespace-separated
    /// atoms, `|| ( ... )` any-of groups, `use? ( ... )` conditional groups,
    /// and bare `( ... )` all-of groups (flattened into the parent list).
    ///
    /// # Examples
    ///
    /// ```
    /// use portage_atom::DepEntry;
    ///
    /// let entries = DepEntry::parse("dev-lang/rust ssl? ( dev-libs/openssl )").unwrap();
    /// assert_eq!(entries.len(), 2);
    /// ```
    pub fn parse(input: &str) -> Result<Vec<DepEntry>> {
        parse_dep_string()
            .parse(input)
            .map_err(|e| Error::InvalidDepString(format!("{e}")))
    }
}

impl fmt::Display for DepEntry {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            DepEntry::Atom(dep) => write!(f, "{dep}"),
            DepEntry::UseConditional {
                flag,
                negate,
                children,
            } => {
                if *negate {
                    write!(f, "!")?;
                }
                write!(f, "{flag}? ( ")?;
                for (i, child) in children.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{child}")?;
                }
                write!(f, " )")
            }
            DepEntry::AnyOf(entries) => {
                write!(f, "|| ( ")?;
                for (i, entry) in entries.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{entry}")?;
                }
                write!(f, " )")
            }
        }
    }
}

// Winnow parsers

/// Parse a complete dependency string (top-level).
pub(crate) fn parse_dep_string<'s>() -> impl Parser<&'s str, Vec<DepEntry>, ErrMode<ContextError>> {
    move |input: &mut &'s str| {
        let entries = parse_dep_entries(input)?;
        multispace0.parse_next(input)?;
        Ok(entries)
    }
}

/// Parse zero or more dependency entries separated by whitespace.
///
/// Stops when it encounters `)` or end-of-input.  Bare parenthesized groups
/// are flattened into the result via `fold`.
fn parse_dep_entries(input: &mut &str) -> ModalResult<Vec<DepEntry>> {
    repeat(0.., preceded(multispace0, parse_dep_entry))
        .fold(Vec::new, |mut acc: Vec<DepEntry>, batch: Vec<DepEntry>| {
            acc.extend(batch);
            acc
        })
        .parse_next(input)
}

/// Parse a single dependency entry, returning one or more entries
/// (bare parenthesized groups are flattened into multiple entries).
///
/// Uses `dispatch!(peek(any); ...)` to route on the first character:
/// - `|` → any-of group (`|| ( ... )`)
/// - `(` → bare paren group (flattened)
/// - `>`, `<`, `~`, `=` → versioned atom (skip USE-conditional attempt)
/// - anything else → try USE conditional first, fall back to atom
fn parse_dep_entry(input: &mut &str) -> ModalResult<Vec<DepEntry>> {
    dispatch! {peek(any);
        '|' => parse_any_of.map(|e| vec![e]),
        '(' => parse_paren_group,
        '>' | '<' | '~' | '=' => parse_dep()
            .context(StrContext::Label("dependency atom"))
            .map(|d| vec![DepEntry::Atom(d)]),
        _ => alt((
            parse_use_conditional.map(|e| vec![e]),
            parse_dep()
                .context(StrContext::Label("dependency atom"))
                .map(|d| vec![DepEntry::Atom(d)]),
        )),
    }
    .parse_next(input)
}

/// Parse `|| ( entry+ )`.
///
/// After consuming `||`, uses `cut_err` to commit — a missing `(` or `)`
/// becomes a hard error instead of backtracking into `alt`.
fn parse_any_of(input: &mut &str) -> ModalResult<DepEntry> {
    "||".parse_next(input)?;
    multispace0.parse_next(input)?;
    cut_err(delimited('(', parse_dep_entries, (multispace0, ')')))
        .context(StrContext::Label("'||' group"))
        .map(DepEntry::AnyOf)
        .parse_next(input)
}

/// Parse `[!]flag? ( entry* )`.
///
/// Backtracks freely until `?` is consumed — after that, `cut_err`
/// commits so a missing `( ... )` is a hard error.
fn parse_use_conditional(input: &mut &str) -> ModalResult<DepEntry> {
    let negate = opt('!').parse_next(input)?.is_some();
    let flag: String = take_while(1.., |c: char| {
        c.is_ascii_alphanumeric() || c == '_' || c == '-' || c == '+'
    })
    .map(|s: &str| s.to_string())
    .parse_next(input)?;
    '?'.parse_next(input)?;
    // After '?', committed to USE conditional
    multispace0.parse_next(input)?;
    let children = cut_err(delimited('(', parse_dep_entries, (multispace0, ')')))
        .context(StrContext::Label("USE conditional group"))
        .parse_next(input)?;
    Ok(DepEntry::UseConditional {
        flag,
        negate,
        children,
    })
}

/// Parse `( entry* )` — bare parenthesized group, flattened.
///
/// After consuming `(`, uses `cut_err` for the closing `)`.
fn parse_paren_group(input: &mut &str) -> ModalResult<Vec<DepEntry>> {
    delimited(
        '(',
        parse_dep_entries,
        cut_err((multispace0, ')')).context(StrContext::Label("closing ')'")),
    )
    .parse_next(input)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dep::Blocker;
    use crate::use_dep::{UseDefault, UseDepKind};
    use crate::version::{Operator, Revision, Version};
    use std::cmp::Ordering;

    #[test]
    fn empty_string() {
        let entries = DepEntry::parse("").unwrap();
        assert!(entries.is_empty());
    }

    #[test]
    fn single_atom() {
        let entries = DepEntry::parse("dev-lang/rust").unwrap();
        assert_eq!(entries.len(), 1);
        assert!(matches!(&entries[0], DepEntry::Atom(dep) if dep.category() == "dev-lang"));
    }

    #[test]
    fn multiple_atoms() {
        let entries = DepEntry::parse("dev-lang/rust dev-libs/bar").unwrap();
        assert_eq!(entries.len(), 2);
        assert!(matches!(&entries[0], DepEntry::Atom(dep) if dep.package() == "rust"));
        assert!(matches!(&entries[1], DepEntry::Atom(dep) if dep.package() == "bar"));
    }

    #[test]
    fn versioned_atom() {
        let entries = DepEntry::parse(">=dev-lang/rust-1.75.0").unwrap();
        assert_eq!(entries.len(), 1);
        match &entries[0] {
            DepEntry::Atom(dep) => {
                assert!(dep.version.is_some());
                let v = dep.version.as_ref().unwrap();
                assert_eq!(v.numbers[0], 1);
                assert_eq!(v.numbers[1], 75);
            }
            _ => panic!("expected Atom"),
        }
    }

    #[test]
    fn any_of_group() {
        let entries = DepEntry::parse("|| ( dev-libs/bar dev-libs/baz )").unwrap();
        assert_eq!(entries.len(), 1);
        match &entries[0] {
            DepEntry::AnyOf(children) => {
                assert_eq!(children.len(), 2);
                assert!(matches!(&children[0], DepEntry::Atom(dep) if dep.package() == "bar"));
                assert!(matches!(&children[1], DepEntry::Atom(dep) if dep.package() == "baz"));
            }
            _ => panic!("expected AnyOf"),
        }
    }

    #[test]
    fn use_conditional() {
        let entries = DepEntry::parse("ssl? ( dev-libs/openssl )").unwrap();
        assert_eq!(entries.len(), 1);
        match &entries[0] {
            DepEntry::UseConditional {
                flag,
                negate,
                children,
            } => {
                assert_eq!(flag, "ssl");
                assert!(!negate);
                assert_eq!(children.len(), 1);
            }
            _ => panic!("expected UseConditional"),
        }
    }

    #[test]
    fn negated_use_conditional() {
        let entries = DepEntry::parse("!debug? ( dev-libs/bar )").unwrap();
        assert_eq!(entries.len(), 1);
        match &entries[0] {
            DepEntry::UseConditional {
                flag,
                negate,
                children,
            } => {
                assert_eq!(flag, "debug");
                assert!(negate);
                assert_eq!(children.len(), 1);
            }
            _ => panic!("expected UseConditional"),
        }
    }

    #[test]
    fn nested_use_in_any_of() {
        let entries = DepEntry::parse("|| ( ssl? ( dev-libs/openssl ) dev-libs/gnutls )").unwrap();
        assert_eq!(entries.len(), 1);
        match &entries[0] {
            DepEntry::AnyOf(children) => {
                assert_eq!(children.len(), 2);
                assert!(matches!(
                    &children[0],
                    DepEntry::UseConditional { flag, .. } if flag == "ssl"
                ));
                assert!(matches!(&children[1], DepEntry::Atom(dep) if dep.package() == "gnutls"));
            }
            _ => panic!("expected AnyOf"),
        }
    }

    #[test]
    fn all_of_flattened() {
        let entries = DepEntry::parse("( dev-libs/a dev-libs/b )").unwrap();
        assert_eq!(entries.len(), 2);
        assert!(matches!(&entries[0], DepEntry::Atom(dep) if dep.package() == "a"));
        assert!(matches!(&entries[1], DepEntry::Atom(dep) if dep.package() == "b"));
    }

    #[test]
    fn complex_mixed() {
        let input =
            "dev-lang/rust || ( dev-libs/openssl dev-libs/libressl ) ssl? ( net-misc/curl )";
        let entries = DepEntry::parse(input).unwrap();
        assert_eq!(entries.len(), 3);
        assert!(matches!(&entries[0], DepEntry::Atom(_)));
        assert!(matches!(&entries[1], DepEntry::AnyOf(_)));
        assert!(matches!(&entries[2], DepEntry::UseConditional { .. }));
    }

    #[test]
    fn display_round_trip() {
        let input =
            "dev-lang/rust || ( dev-libs/openssl dev-libs/libressl ) ssl? ( net-misc/curl )";
        let entries = DepEntry::parse(input).unwrap();
        let displayed: Vec<String> = entries.iter().map(|e| e.to_string()).collect();
        let rejoined = displayed.join(" ");
        let reparsed = DepEntry::parse(&rejoined).unwrap();
        assert_eq!(entries, reparsed);
    }

    #[test]
    fn blocker_in_dep_string() {
        let entries = DepEntry::parse("!dev-libs/old").unwrap();
        assert_eq!(entries.len(), 1);
        match &entries[0] {
            DepEntry::Atom(dep) => {
                assert_eq!(dep.blocker, Some(Blocker::Weak));
                assert_eq!(dep.package(), "old");
            }
            _ => panic!("expected Atom"),
        }
    }

    #[test]
    fn strong_blocker_in_dep_string() {
        let entries = DepEntry::parse("!!dev-libs/old").unwrap();
        assert_eq!(entries.len(), 1);
        match &entries[0] {
            DepEntry::Atom(dep) => {
                assert_eq!(dep.blocker, Some(Blocker::Strong));
                assert_eq!(dep.package(), "old");
            }
            _ => panic!("expected Atom"),
        }
    }

    #[test]
    fn slot_in_dep_string() {
        let entries = DepEntry::parse("dev-lang/python:3.11").unwrap();
        assert_eq!(entries.len(), 1);
        match &entries[0] {
            DepEntry::Atom(dep) => {
                assert!(dep.slot_dep.is_some());
            }
            _ => panic!("expected Atom"),
        }
    }

    #[test]
    fn error_unmatched_paren() {
        let result = DepEntry::parse("( dev-libs/a");
        assert!(result.is_err());
        match result.unwrap_err() {
            Error::InvalidDepString(_) => {}
            other => panic!("expected InvalidDepString, got: {other:?}"),
        }
    }

    // --- dispatch-specific edge cases ---

    /// `>=`, `<`, `~`, `=` dispatch directly to atom parser.
    #[test]
    fn operator_prefixed_atoms() {
        for input in [
            ">=dev-lang/rust-1.75.0",
            "<dev-libs/bar-2.0",
            "~dev-libs/baz-1.0",
            "=dev-libs/qux-3.0",
        ] {
            let entries = DepEntry::parse(input).unwrap();
            assert_eq!(entries.len(), 1, "failed for: {input}");
            assert!(matches!(&entries[0], DepEntry::Atom(dep) if dep.version.is_some()));
        }
    }

    /// `!` followed by a category/package must parse as a blocker atom, not
    /// a USE conditional.
    #[test]
    fn blocker_not_confused_with_use_conditional() {
        let entries = DepEntry::parse("!dev-libs/old ssl? ( dev-libs/openssl )").unwrap();
        assert_eq!(entries.len(), 2);
        assert!(matches!(&entries[0], DepEntry::Atom(dep) if dep.blocker == Some(Blocker::Weak)));
        assert!(
            matches!(&entries[1], DepEntry::UseConditional { flag, negate, .. }
            if flag == "ssl" && !negate)
        );
    }

    /// Empty USE conditional body.
    #[test]
    fn empty_use_conditional() {
        let entries = DepEntry::parse("test? ( )").unwrap();
        assert_eq!(entries.len(), 1);
        match &entries[0] {
            DepEntry::UseConditional { flag, children, .. } => {
                assert_eq!(flag, "test");
                assert!(children.is_empty());
            }
            _ => panic!("expected UseConditional"),
        }
    }

    /// Missing `( )` after `||` is a hard error (cut_err), not a backtrack.
    #[test]
    fn error_any_of_missing_paren() {
        assert!(DepEntry::parse("|| dev-libs/a").is_err());
    }

    /// Missing `( )` after `flag?` is a hard error (cut_err).
    #[test]
    fn error_use_cond_missing_paren() {
        assert!(DepEntry::parse("ssl? dev-libs/openssl").is_err());
    }

    /// Extra whitespace should be tolerated everywhere.
    #[test]
    fn extra_whitespace() {
        let entries = DepEntry::parse("  dev-lang/rust   ssl? (  dev-libs/openssl  )  ").unwrap();
        assert_eq!(entries.len(), 2);
        assert!(matches!(&entries[0], DepEntry::Atom(_)));
        assert!(matches!(&entries[1], DepEntry::UseConditional { .. }));
    }

    /// Display round-trip with nested structures.
    #[test]
    fn display_round_trip_nested() {
        let input = "|| ( ssl? ( dev-libs/openssl ) !ssl? ( dev-libs/libressl ) )";
        let entries = DepEntry::parse(input).unwrap();
        let displayed: Vec<String> = entries.iter().map(|e| e.to_string()).collect();
        let rejoined = displayed.join(" ");
        let reparsed = DepEntry::parse(&rejoined).unwrap();
        assert_eq!(entries, reparsed);
    }

    /// Atoms with USE deps and repo in a dep string.
    #[test]
    fn complex_atoms_in_dep_string() {
        let entries =
            DepEntry::parse(">=dev-lang/rust-1.75.0:0[llvm_targets_AMDGPU] dev-libs/bar::gentoo")
                .unwrap();
        assert_eq!(entries.len(), 2);
        match &entries[0] {
            DepEntry::Atom(dep) => {
                assert!(dep.version.is_some());
                assert!(dep.slot_dep.is_some());
                assert!(dep.use_deps.is_some());
            }
            _ => panic!("expected Atom"),
        }
        match &entries[1] {
            DepEntry::Atom(dep) => {
                assert_eq!(dep.repo, Some("gentoo".to_string()));
            }
            _ => panic!("expected Atom"),
        }
    }

    // Issue 1: Empty USE dep brackets []
    #[test]
    fn test_atoms_with_empty_use_deps() {
        let entries = DepEntry::parse("dev-libs/libbsd[]").unwrap();
        assert_eq!(entries.len(), 1);
        match &entries[0] {
            DepEntry::Atom(dep) => {
                assert_eq!(dep.package(), "libbsd");
                assert!(dep.use_deps.as_ref().unwrap().is_empty());
            }
            _ => panic!("expected Atom"),
        }

        let entries = DepEntry::parse(">=dev-libs/libatomic_ops-7.4[]").unwrap();
        assert_eq!(entries.len(), 1);
        match &entries[0] {
            DepEntry::Atom(dep) => {
                assert_eq!(dep.package(), "libatomic_ops");
                assert!(dep.version.is_some());
                assert!(dep.use_deps.as_ref().unwrap().is_empty());
            }
            _ => panic!("expected Atom"),
        }
    }

    // Issue 2: USE dep defaults (+) and (-)
    #[test]
    fn test_atoms_with_use_dep_defaults() {
        let entries = DepEntry::parse("sys-libs/ncurses:=[unicode(+)?]").unwrap();
        assert_eq!(entries.len(), 1);
        match &entries[0] {
            DepEntry::Atom(dep) => {
                assert_eq!(dep.package(), "ncurses");
                let use_deps = dep.use_deps.as_ref().unwrap();
                assert_eq!(use_deps.len(), 1);
                assert_eq!(use_deps[0].flag, "unicode");
                assert_eq!(use_deps[0].kind, UseDepKind::Conditional);
                assert_eq!(use_deps[0].default, Some(UseDefault::Enabled));
            }
            _ => panic!("expected Atom"),
        }

        let entries = DepEntry::parse("dev-libs/libxml2[icu(+)]").unwrap();
        assert_eq!(entries.len(), 1);
        match &entries[0] {
            DepEntry::Atom(dep) => {
                assert_eq!(dep.package(), "libxml2");
                let use_deps = dep.use_deps.as_ref().unwrap();
                assert_eq!(use_deps.len(), 1);
                assert_eq!(use_deps[0].flag, "icu");
                assert_eq!(use_deps[0].kind, UseDepKind::Enabled);
                assert_eq!(use_deps[0].default, Some(UseDefault::Enabled));
            }
            _ => panic!("expected Atom"),
        }

        let entries = DepEntry::parse("sys-libs/readline:=[unicode(-)]").unwrap();
        assert_eq!(entries.len(), 1);
        match &entries[0] {
            DepEntry::Atom(dep) => {
                assert_eq!(dep.package(), "readline");
                let use_deps = dep.use_deps.as_ref().unwrap();
                assert_eq!(use_deps.len(), 1);
                assert_eq!(use_deps[0].flag, "unicode");
                assert_eq!(use_deps[0].kind, UseDepKind::Enabled);
                assert_eq!(use_deps[0].default, Some(UseDefault::Disabled));
            }
            _ => panic!("expected Atom"),
        }
    }

    // Issue 3: = version prefix with glob * suffix
    #[test]
    fn test_atoms_with_glob_version() {
        let entries = DepEntry::parse("=dev-util/nvidia-cuda-toolkit-11*").unwrap();
        assert_eq!(entries.len(), 1);
        match &entries[0] {
            DepEntry::Atom(dep) => {
                assert_eq!(dep.package(), "nvidia-cuda-toolkit");
                assert!(dep.version.is_some());
                let version = dep.version.as_ref().unwrap();
                assert_eq!(version.op, Some(Operator::Equal));
                assert!(version.glob); // PMS: * is part of version, not operator
            }
            _ => panic!("expected Atom"),
        }

        let entries = DepEntry::parse("=sys-devel/gcc-13*").unwrap();
        assert_eq!(entries.len(), 1);
        match &entries[0] {
            DepEntry::Atom(dep) => {
                assert_eq!(dep.package(), "gcc");
                assert!(dep.version.is_some());
                let version = dep.version.as_ref().unwrap();
                assert_eq!(version.op, Some(Operator::Equal));
                assert!(version.glob); // PMS: * is part of version, not operator
            }
            _ => panic!("expected Atom"),
        }
    }

    // Test PMS glob version matching behavior
    #[test]
    fn test_glob_version_matching() {
        // PMS: =1.2* should match 1.2.3, 1.2.4, etc.
        let v1_2_star = Version {
            op: None,
            numbers: vec![1, 2],
            letter: None,
            suffixes: vec![],
            revision: Revision(0),
            glob: true,
        };

        let v1_2_3 = Version {
            op: None,
            numbers: vec![1, 2, 3],
            letter: None,
            suffixes: vec![],
            revision: Revision(0),
            glob: false,
        };

        let v1_2_4 = Version {
            op: None,
            numbers: vec![1, 2, 4],
            letter: None,
            suffixes: vec![],
            revision: Revision(0),
            glob: false,
        };

        let v1_3 = Version {
            op: None,
            numbers: vec![1, 3],
            letter: None,
            suffixes: vec![],
            revision: Revision(0),
            glob: false,
        };

        // PMS glob matching: 1.2* should match 1.2.3 and 1.2.4
        assert_eq!(v1_2_star.cmp(&v1_2_3), Ordering::Equal);
        assert_eq!(v1_2_star.cmp(&v1_2_4), Ordering::Equal);

        // But should not match 1.3*
        assert_ne!(v1_2_star.cmp(&v1_3), Ordering::Equal);
    }

    // Issue 4: Trailing comma in USE dep list
    #[test]
    fn test_atoms_with_trailing_comma_in_use_deps() {
        let entries =
            DepEntry::parse(">=app-accessibility/at-spi2-core-2.46.0[introspection?,]").unwrap();
        assert_eq!(entries.len(), 1);
        match &entries[0] {
            DepEntry::Atom(dep) => {
                assert_eq!(dep.package(), "at-spi2-core");
                assert!(dep.version.is_some());
                let use_deps = dep.use_deps.as_ref().unwrap();
                assert_eq!(use_deps.len(), 1);
                assert_eq!(use_deps[0].flag, "introspection");
                assert_eq!(use_deps[0].kind, UseDepKind::Conditional);
            }
            _ => panic!("expected Atom"),
        }
    }

    // Issue 5: USE-conditional dep groups with whitespace handling
    #[test]
    fn test_use_conditional_with_whitespace() {
        let entries =
            DepEntry::parse("python_single_target_python3_11? ( dev-lang/python )").unwrap();
        assert_eq!(entries.len(), 1);
        match &entries[0] {
            DepEntry::UseConditional {
                flag,
                negate,
                children,
            } => {
                assert_eq!(flag, "python_single_target_python3_11");
                assert!(!negate);
                assert_eq!(children.len(), 1);
            }
            _ => panic!("expected UseConditional"),
        }

        let entries = DepEntry::parse("test? ( dev-libs/check )").unwrap();
        assert_eq!(entries.len(), 1);
        match &entries[0] {
            DepEntry::UseConditional {
                flag,
                negate,
                children,
            } => {
                assert_eq!(flag, "test");
                assert!(!negate);
                assert_eq!(children.len(), 1);
            }
            _ => panic!("expected UseConditional"),
        }

        let entries = DepEntry::parse("|| ( dev-libs/openssl dev-libs/libressl )").unwrap();
        assert_eq!(entries.len(), 1);
        match &entries[0] {
            DepEntry::AnyOf(children) => {
                assert_eq!(children.len(), 2);
            }
            _ => panic!("expected AnyOf"),
        }

        let entries = DepEntry::parse("X? ( x11-libs/libX11 )").unwrap();
        assert_eq!(entries.len(), 1);
        match &entries[0] {
            DepEntry::UseConditional {
                flag,
                negate,
                children,
            } => {
                assert_eq!(flag, "X");
                assert!(!negate);
                assert_eq!(children.len(), 1);
            }
            _ => panic!("expected UseConditional"),
        }
    }
}
