# Project Overview: `HoTT`

## 1. Purpose and Scope

`HoTT` is a comprehensive formalization of **Homotopy Type Theory** and **Univalent Foundations** in the Coq proof assistant (`theories/`), paired with an executable Python computational model and verification suite (`hott/` and `tests/`). Propositional equality is interpreted homotopically as paths in a space, type isomorphism as homotopy equivalence, and Voevodsky's Univalence Axiom identifies equivalent types in a universe.

---

## 2. Repository Architecture

### Layer 1: Standalone and Modular Coq Formalizations (`theories/`)
- **Foundations and Path Groupoids**:
  - [CoreHomotopyTheory.v](file:///botworkspace/HoTT/theories/CoreHomotopyTheory.v): Martin-Lof identity types (`paths`, `idpath`), the `J` eliminator, higher groupoid laws (`concat_1p`, `concat_p1`, `concat_p_pp`, `concat_Vp`, `concat_pV`, `inv_V`, `inv_pp`), functoriality (`ap`, `transport`), homotopy fibers (`fiber`), and equivalences (`IsEquiv`, `Equiv`).
  - `theories/Basics/` and `theories/Types/`: Universe polymorphism, path groupoids, contractibility, equivalences, truncation levels, and type-former path spaces (`Paths.v`, `Sigma.v`, `Prod.v`, `Forall.v`, `Arrow.v`, `Universe.v`).
- **Truncation Hierarchy and Hedberg's Theorem**:
  - [Truncation.v](file:///botworkspace/HoTT/theories/Truncation.v) and [HSet.v](file:///botworkspace/HoTT/theories/HSet.v): Inductive truncation indices starting at `-2` (contractible), mere propositions (`IsProp`), h-sets (`IsSet`), cumulative `n`-type hierarchy (`is_n_type`, `is_trunc`), and Hedberg's theorem proving that decidable equality implies `IsSet`.
- **Univalence and Function Extensionality**:
  - [Univalence.v](file:///botworkspace/HoTT/theories/Univalence.v): Canonical `idToEqv`, Voevodsky's `univalence_axiom` (`ua`, `ua_idToEqv`, `idToEqv_ua`, `transport_ua_beta`), constructive derivation of weak and dependent function extensionality (`weak_funext`, `funext_dep`, `funext_nondep`), and propositional extensionality (`prop_equiv_to_id`).
  - [UnivalenceAxiom.v](file:///botworkspace/HoTT/theories/UnivalenceAxiom.v), [FunextAxiom.v](file:///botworkspace/HoTT/theories/FunextAxiom.v), [UnivalenceVarieties.v](file:///botworkspace/HoTT/theories/UnivalenceVarieties.v), and [FunextVarieties.v](file:///botworkspace/HoTT/theories/FunextVarieties.v): Unified bridges between weak, Orton-Pitts very weak, naive, and full univalence and function extensionality.
- **Higher Inductive Types (HITs)**:
  - [HigherInductiveTypes.v](file:///botworkspace/HoTT/theories/HigherInductiveTypes.v), [Circle.v](file:///botworkspace/HoTT/theories/HIT/Circle.v), and [Suspension.v](file:///botworkspace/HoTT/theories/HIT/Suspension.v): Interval HIT (`Interval`), Circle `S1` with modularized encode-decode loop space equivalence (`S1_decode_loop_step`, `S1_encode_sect`, `S1_encode_retr`, `equiv_loopS1_int`), Suspension `Susp` with meridian loop lemmas (`Susp_merid_loop`, `Susp_merid_loop_base`, `Susp_merid_loop_inv`), and Torus `T2` (`torus_equiv_circle_prod`).
- **Homotopy Excision and Stability**:
  - [BlakersMassey.v](file:///botworkspace/HoTT/theories/BlakersMassey.v): `n`-connected spaces and maps, homotopy pushouts and pullbacks, the Blakers-Massey Homotopy Excision Theorem (`blakers_massey_theorem`), and the Freudenthal Suspension Theorem (`freudenthal_suspension_theorem`, `freudenthal_stability_equiv`).

### Layer 2: Executable Python Homotopy Type Theory Package (`hott/`)
- [identity.py](file:///botworkspace/HoTT/hott/identity.py): Computational path algebra, `J`-elimination, `ap`, `apd`, and `transport`.
- [equivalence.py](file:///botworkspace/HoTT/hott/equivalence.py): Homotopies, fibers, contractibility witnesses, and quasi-inverses.
- [truncation.py](file:///botworkspace/HoTT/hott/truncation.py): Truncation level verification and Hedberg constant-path factorization.
- [univalence.py](file:///botworkspace/HoTT/hott/univalence.py): Univalence transport, function extensionality derivation, and propositional extensionality.
- [hit.py](file:///botworkspace/HoTT/hott/hit.py): Interval, Circle `S1`, Suspension `Susp`, and Torus `T2` models.
- [connectivity.py](file:///botworkspace/HoTT/hott/connectivity.py): Blakers-Massey connectivity bounds and Freudenthal sphere homotopy group stability.

---

## 3. Verification and Build Workflow

```bash
# Run the full Coq and Python verification suite:
python3 /botworkspace/HoTT/check.py

# Run standalone Coq theory verification and unit tests:
python3 /botworkspace/HoTT/run_tests.py
```

See [THEOREM_INDEX.md](file:///botworkspace/HoTT/THEOREM_INDEX.md) for the complete inventory of formalized theorems and definitions.
