# Revision history for system-f-numerical

## 0.1.0.0 -- 2026-04-19

* Initial release.
* Church-encoded naturals (`Nat`) with `zero`, `suc`, `pred`, and
  `Integer` marshalling.
* Church-encoded finite lists (`List`) with `empty`, `cons`, `append`,
  and `lmul` (Cartesian product).
* Full hyperoperation hierarchy (`add`, `mul`, `exp`, `tet`, `pent`)
  derived from a single `hypSuc` combinator.
* `hspec` + `QuickCheck` test suite: 132 cases covering arithmetic
  laws, list laws, and cross-level hyperoperation consistency.
