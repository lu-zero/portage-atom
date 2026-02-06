//! Lightweight Portage package atom parser based on [PMS]
//!
//! This crate provides types and parsing for Gentoo/Portage package atoms
//! according to the [Package Manager Specification (PMS)][PMS].
//!
//! [PMS]: https://projects.gentoo.org/pms/latest/pms.html
//!
//! # Examples
//!
//! Parse a simple unversioned atom:
//! ```
//! use portage_atom::Cpn;
//!
//! let cpn = Cpn::parse("dev-lang/rust").unwrap();
//! assert_eq!(cpn.category, "dev-lang");
//! assert_eq!(cpn.package, "rust");
//! ```
//!
//! Parse a versioned atom:
//! ```
//! use portage_atom::Cpv;
//!
//! let cpv = Cpv::parse("dev-lang/rust-1.75.0").unwrap();
//! assert_eq!(cpv.version.numbers[0], 1);
//! ```
//!
//! Parse a full dependency:
//! ```
//! use portage_atom::Dep;
//!
//! let dep = Dep::parse(">=dev-lang/rust-1.75.0:0[llvm_targets_AMDGPU]").unwrap();
//! assert!(dep.version.is_some());
//! assert!(dep.slot_dep.is_some());
//! assert!(dep.use_deps.is_some());
//! ```

mod cpn;
mod cpv;
mod dep;
mod error;
mod slot;
mod use_dep;
mod version;

// Re-export main types
pub use cpn::Cpn;
pub use cpv::Cpv;
pub use dep::{Blocker, Dep};
pub use error::{Error, Result};
pub use slot::{Slot, SlotDep, SlotOperator};
pub use use_dep::{UseDefault, UseDep, UseDepKind};
pub use version::{Operator, Revision, Suffix, SuffixKind, Version};
