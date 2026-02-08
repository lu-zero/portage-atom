use std::fmt;
use std::str::FromStr;

use winnow::combinator::{alt, opt, preceded};
use winnow::error::{ContextError, ErrMode, StrContext};
use winnow::prelude::*;
use winnow::token::take_while;

use crate::error::{Error, Result};

/// Slot operator for sub-slot rebuilds
///
/// See [PMS 8.3.3](https://projects.gentoo.org/pms/latest/pms.html#slot-dependencies).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SlotOperator {
    /// `:=` — the dependent package must be rebuilt when the dependency's
    /// slot or sub-slot changes.
    Equal,
    /// `:*` — accept any slot; no rebuild is triggered on slot changes.
    Star,
}

impl fmt::Display for SlotOperator {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            SlotOperator::Equal => write!(f, "="),
            SlotOperator::Star => write!(f, "*"),
        }
    }
}

/// Slot name and optional sub-slot
///
/// Slots allow multiple versions of a package to be installed simultaneously
/// (e.g. `dev-lang/python:3.11` and `dev-lang/python:3.12`). Sub-slots
/// track ABI compatibility; a sub-slot change signals that reverse
/// dependencies using `:=` must be rebuilt.
///
/// See [PMS 7.2](https://projects.gentoo.org/pms/latest/pms.html#mandatory-ebuilddefined-variables).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Slot {
    /// The slot name (e.g. `0`, `3.12`, `stable`).
    pub slot: String,
    /// Optional sub-slot for ABI tracking (e.g. `1.2` in `:0/1.2`).
    pub subslot: Option<String>,
}

impl Slot {
    pub fn new(slot: impl Into<String>) -> Self {
        Slot {
            slot: slot.into(),
            subslot: None,
        }
    }

    pub fn with_subslot(slot: impl Into<String>, subslot: impl Into<String>) -> Self {
        Slot {
            slot: slot.into(),
            subslot: Some(subslot.into()),
        }
    }
}

impl fmt::Display for Slot {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.slot)?;
        if let Some(ref subslot) = self.subslot {
            write!(f, "/{}", subslot)?;
        }
        Ok(())
    }
}

/// Slot dependency with optional operator
///
/// Represents the slot constraint portion of a dependency atom
/// (everything after the `:`), e.g. `:0`, `:0/2.1`, `:0=`, `:=`, `:*`.
///
/// See [PMS 8.3.3](https://projects.gentoo.org/pms/latest/pms.html#slot-dependencies).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SlotDep {
    /// A named slot with optional sub-slot and optional operator,
    /// e.g. `:0`, `:0/1.2`, `:0=`.
    Slot {
        slot: Option<Slot>,
        op: Option<SlotOperator>,
    },
    /// A bare operator without a named slot (`:=` or `:*`).
    Operator(SlotOperator),
}

impl SlotDep {
    /// Parse from string (without leading :)
    pub fn parse(input: &str) -> Result<Self> {
        parse_slot_dep()
            .parse(input)
            .map_err(|e| Error::InvalidSlot(format!("{}: {}", input, e)))
    }
}

impl fmt::Display for SlotDep {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            SlotDep::Slot { slot, op } => {
                if let Some(s) = slot {
                    write!(f, "{}", s)?;
                }
                if let Some(o) = op {
                    write!(f, "{}", o)?;
                }
                Ok(())
            }
            SlotDep::Operator(op) => write!(f, "{}", op),
        }
    }
}

impl FromStr for SlotDep {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        Self::parse(s)
    }
}

// Winnow parsers

/// Parse slot name (alphanumeric, _, -, +, .)
fn parse_slot_name<'s>() -> impl Parser<&'s str, String, ErrMode<ContextError>> {
    take_while(1.., |c: char| {
        c.is_ascii_alphanumeric() || c == '_' || c == '-' || c == '+' || c == '.'
    })
    .map(|s: &str| s.to_string())
}

/// Parse slot with optional subslot
fn parse_slot<'s>() -> impl Parser<&'s str, Slot, ErrMode<ContextError>> {
    (parse_slot_name(), opt(preceded('/', parse_slot_name())))
        .map(|(slot, subslot)| Slot { slot, subslot })
}

/// Parse slot operator
fn parse_slot_operator<'s>() -> impl Parser<&'s str, SlotOperator, ErrMode<ContextError>> {
    alt((
        '='.value(SlotOperator::Equal),
        '*'.value(SlotOperator::Star),
    ))
}

/// Parse slot dependency (after the : has been consumed)
pub(crate) fn parse_slot_dep<'s>() -> impl Parser<&'s str, SlotDep, ErrMode<ContextError>> {
    alt((
        // Just operator: := or :*
        parse_slot_operator().map(SlotDep::Operator),
        // Slot with optional operator: :0, :0=, :0/1.2
        (parse_slot(), opt(parse_slot_operator())).map(|(slot, op)| SlotDep::Slot {
            slot: Some(slot),
            op,
        }),
    ))
    .context(StrContext::Label("slot"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_slot_parsing() {
        let slot = SlotDep::parse("0").unwrap();
        match slot {
            SlotDep::Slot {
                slot: Some(s),
                op: None,
            } => {
                assert_eq!(s.slot, "0");
                assert_eq!(s.subslot, None);
            }
            _ => panic!("unexpected slot dep"),
        }
    }

    #[test]
    fn test_slot_with_subslot() {
        let slot = SlotDep::parse("0/2.1").unwrap();
        match slot {
            SlotDep::Slot {
                slot: Some(s),
                op: None,
            } => {
                assert_eq!(s.slot, "0");
                assert_eq!(s.subslot, Some("2.1".to_string()));
            }
            _ => panic!("unexpected slot dep"),
        }
    }

    #[test]
    fn test_slot_operators() {
        let slot = SlotDep::parse("=").unwrap();
        assert_eq!(slot, SlotDep::Operator(SlotOperator::Equal));

        let slot = SlotDep::parse("*").unwrap();
        assert_eq!(slot, SlotDep::Operator(SlotOperator::Star));

        let slot = SlotDep::parse("0=").unwrap();
        match slot {
            SlotDep::Slot {
                slot: Some(s),
                op: Some(SlotOperator::Equal),
            } => {
                assert_eq!(s.slot, "0");
            }
            _ => panic!("unexpected slot dep"),
        }
    }
}
