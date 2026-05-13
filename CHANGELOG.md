# Changelog

## 0.7.0

### Performance

- **Eliminate backtracking** in `dep` and `dep_entry` parsers (~27-35% faster):
  - `find_last_hyphen_digit()` uses `rfind('-')` for version boundary detection
  - `has_version_suffix()` dispatches CPV vs CPN without `alt` backtracking
  - `parse_version_no_raw()` skips raw string allocation in dep parsing path
  - USE-conditional dispatch uses `? (` discriminant with early `/`/`:`/`[` short-circuit
- Portage-atom now matches or beats pkgcraft across all benchmarks.

### Bug fixes

- **PMS 8.3.1 compliance**: reject glob `*` with non-`=` operators (`>=pkg-1*` is illegal)
- **Version `Eq`/`Hash` consistency**: `1 == 1.0 == 1.0.0` — trailing zeros are normalized in `PartialEq` and `Hash` to match `Ord` behavior (PMS: missing components are 0)
- **PMS 3.1.4 compliance**: USE-conditional parser now accepts `@` in flag names (deprecated LINGUAS character) and validates first character is alphanumeric

### Refactoring

- USE-conditional lookahead rewritten from identifier-scanning to `? (` discriminant pattern — character-set-agnostic, shorter, and faster
- Doc comments corrected for Cpn category/package first-character restrictions

### Tests

- 91 → 115 tests (+24 new PMS compliance tests):
  - PMS 3.1.1/3.1.2 category and package naming rules
  - PMS 3.2 / Algorithm 3.1 version ordering chain
  - PMS 8.3.1 all six operators, glob validation
  - PMS 8.2 USE-conditional discriminant, `@` flag names, deeply nested structures
  - PMS 8.3.3 slot operators, subslots, round-trips

## 0.6.0

- Add `Hash` derive to `Dep` and `DepEntry`
- Add `AllOf` variant to `DepEntry`
- Preserve raw version string in CPV parsing
- Update criterion to 0.7

## 0.5.0

- Update winnow to 1.0.0
- Add builder feature with bon-derived builders
- Use `ModalResult` for parser functions
- Intern remaining string fields

## 0.4.0

- Use gentoo-interner for string deduplication
- Add benchmarks for parsing and comparison

## 0.3.0

- Add PMS 8.2.4 `^^ ( )` and PMS 8.2.5 `?? ( )` dependency groups
- Fix glob version parsing and version comparison

## 0.2.0

- Add `DepEntry` type and PMS dependency string parser
- Add parse examples

## 0.1.0

- Initial implementation
