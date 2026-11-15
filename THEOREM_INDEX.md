# Theorem and Formalization Inventory (`HoTT`)

This document catalogs the core Homotopy Type Theory formalizations across the Coq theories (`theories/`) and the executable Python verification package (`hott/`).

---

## 1. Identity Types, Path Groupoids, and Equivalences (`theories/CoreHomotopyTheory.v`, `theories/Basics/`)

| Identifier | Statement / Signature | File |
|------------|-----------------------|------|
| `paths` / `idpath` | Martin-Lof intensional identity type `paths a b` and reflexivity `idpath` | `theories/CoreHomotopyTheory.v` (line 10) |
| `J` / `based_path_induction` | Path induction (J-eliminator) with computation rule on `idpath` | `theories/CoreHomotopyTheory.v` (line 15), `theories/Univalence.v` (line 17) |
| `concat`, `inverse` | Path composition and path reversal | `theories/CoreHomotopyTheory.v` (lines 23-28) |
| `concat_1p`, `concat_p1`, `concat_p_pp` | Left/right unit and associativity laws of the higher path groupoid | `theories/CoreHomotopyTheory.v` (lines 35-45) |
| `concat_Vp`, `concat_pV`, `inv_V`, `inv_pp` | Inverse cancellation, involution, and contravariance over composition | `theories/CoreHomotopyTheory.v` (lines 51-66) |
| `ap`, `apd`, `transport` | Functoriality on paths, dependent action on paths, and fibration transport | `theories/CoreHomotopyTheory.v` (lines 72-77) |
| `IsContr`, `Homotopy`, `fiber` | Contractible types, pointwise homotopies, and homotopy fibers `fib_f(y)` | `theories/CoreHomotopyTheory.v` (lines 84-90) |
| `IsEquiv`, `Equiv` | Homotopy equivalences and quasi-inverses | `theories/CoreHomotopyTheory.v` (lines 93-99) |
| `isequiv_to_contr_fibers`, `contr_fibers_to_isequiv`, `equiv_iff_contr_fibers` | Equivalence between quasi-invertibility and contractible homotopy fibers | `theories/CoreHomotopyTheory.v` (lines 186-203) |

---

## 2. Truncation Hierarchy and Hedberg's Theorem (`theories/Truncation.v`, `theories/CoreHomotopyTheory.v`)

| Identifier | Statement / Signature | File |
|------------|-----------------------|------|
| `trunc_index`, `is_n_type`, `is_trunc` | Inductive truncation levels starting at $-2$ (contractible) | `theories/Truncation.v`, `theories/CoreHomotopyTheory.v` (lines 213-238) |
| `is_contr_to_is_prop`, `is_prop_to_is_set` | Cumulative upward closure of truncation levels ($-2 \implies -1 \implies 0$) | `theories/CoreHomotopyTheory.v` (lines 267-279) |
| `is_prop_to_is_minus_one_type`, `is_minus_one_type_to_is_prop` | Equivalence between mere propositions `IsProp` and $(-1)$-types | `theories/CoreHomotopyTheory.v` (lines 286-295) |
| `is_set_to_is_zero_type`, `is_zero_type_to_is_set` | Equivalence between h-sets `IsSet` (UIP) and $0$-types | `theories/CoreHomotopyTheory.v` (lines 303-311) |
| `hedberg_theorem` | Any type with decidable path equality (`DecidablePaths A`) is an h-set (`IsSet A`) | `theories/Truncation.v`, `theories/CoreHomotopyTheory.v` |

---

## 3. Voevodsky Univalence and Function Extensionality (`theories/Univalence.v`, `theories/UnivalenceAxiom.v`, `theories/FunextAxiom.v`)

| Identifier | Statement / Signature | File |
|------------|-----------------------|------|
| `idToEqv` / `equiv_path` | Canonical map $(A = B) \to (A \simeq B)$ defined by path induction | `theories/Univalence.v` (line 119), `theories/Types/Universe.v` |
| `univalence_axiom`, `ua` | Voevodsky's Univalence Axiom and inverse map $(A \simeq B) \to (A = B)$ | `theories/Univalence.v` (lines 125-127), `theories/UnivalenceAxiom.v` |
| `ua_idToEqv`, `idToEqv_ua`, `transport_ua_beta` | Propositional eta/beta computation rules for `ua` and `transport` | `theories/Univalence.v` (lines 130-165) |
| `ua_free_path_contr`, `weak_funext`, `funext_dep`, `funext_nondep` | Constructive derivation of Weak and Dependent Function Extensionality from Univalence | `theories/Univalence.v` (lines 180-257), `theories/UnivalenceImpliesFunext.v` |
| `prop_equiv_to_id`, `is_prop_equiv_is_id` | Propositional Extensionality derived as a special case of Univalence | `theories/Univalence.v` (lines 264-282) |
| `weak_univalence_to_univalence`, `very_weak_univalence_to_univalence` | Unified bridges between weak, Orton-Pitts very weak, and standard univalence | `theories/UnivalenceAxiom.v`, `theories/UnivalenceVarieties.v` |
| `funext_to_naive_funext`, `funext_to_weak_funext`, `weak_funext_to_funext` | Unified bridges between naive, weak, and full function extensionality | `theories/FunextAxiom.v`, `theories/FunextVarieties.v` |

---

## 4. Higher Inductive Types (`theories/HigherInductiveTypes.v`, `theories/HIT/Circle.v`, `theories/HIT/Suspension.v`)

| Identifier | Statement / Signature | File |
|------------|-----------------------|------|
| `Interval`, `seg`, `interval_is_contr`, `interval_funext` | Interval HIT $[0, 1]$, contractibility, and derivation of function extensionality | `theories/HigherInductiveTypes.v`, `theories/HIT/Interval.v` |
| `S1`, `base`, `loop`, `S1_ind`, `S1_rec` | Circle $S^1$ with dependent and non-dependent eliminators and $\beta$-rules | `theories/HigherInductiveTypes.v`, `theories/HIT/Circle.v` |
| `S1_decode_loop_step`, `S1_encode_sect`, `S1_encode_retr`, `equiv_loopS1_int` | Modularized encode-decode proof that $\Omega(S^1, \text{base}) \simeq \mathbb{Z}$ | `theories/HIT/Circle.v` (lines 102-168) |
| `Susp`, `north`, `south`, `merid`, `Susp_ind`, `Susp_rec` | Suspension $\Sigma A$ with meridian glue paths and induction/recursion principles | `theories/HigherInductiveTypes.v`, `theories/HIT/Suspension.v` |
| `Susp_merid_loop`, `Susp_merid_loop_base`, `Susp_merid_loop_inv` | Reusable meridian loop and inversion lemmas in $\Omega(\Sigma A, \text{north})$ | `theories/HIT/Suspension.v` (lines 160-177), `theories/HigherInductiveTypes.v` (lines 333-350) |
| `s1_equiv_susp_bool` | Homotopy equivalence $S^1 \simeq \Sigma(\mathbf{2})$ | `theories/HigherInductiveTypes.v` |
| `T2`, `torus_equiv_circle_prod` | Torus $T^2$ with 2-cell surface path and equivalence $T^2 \simeq S^1 \times S^1$ | `theories/HigherInductiveTypes.v` (lines 250-329) |

---

## 5. Blakers-Massey Homotopy Excision and Freudenthal Suspension (`theories/BlakersMassey.v`)

| Identifier | Statement / Signature | File |
|------------|-----------------------|------|
| `is_connected`, `is_connected_map` | $n$-connected spaces and $n$-connected maps via fiber connectivity | `theories/BlakersMassey.v` (lines 145-148) |
| `freudenthal_map`, `freudenthal_map_base` | Suspension unit $\sigma : A \to \Omega(\Sigma A, \text{north})$ sending $a \mapsto \text{merid}(a) \cdot \text{merid}(a_0)^{-1}$ | `theories/BlakersMassey.v` (lines 215-218) |
| `Pushout`, `HomotopyPullback`, `blakers_massey_comparison` | Homotopy pushouts, homotopy pullbacks, and canonical comparison map | `theories/BlakersMassey.v` (lines 229-276) |
| `blakers_massey_theorem` | Blakers-Massey homotopy excision: for $n$-connected $f$ and $m$-connected $g$, the pullback-to-pushout comparison map is $(n + m)$-connected | `theories/BlakersMassey.v` (line 286) |
| `freudenthal_suspension_theorem`, `freudenthal_stability_equiv` | Freudenthal Suspension Theorem: for $n$-connected $(A, a_0)$, $\sigma : A \to \Omega\Sigma A$ is $2n$-connected and $\pi_k(A) \simeq \pi_{k+1}(\Sigma A)$ for $k \le 2n$ | `theories/BlakersMassey.v` (lines 293-302) |

---

## 6. Executable Python Homotopy Type Theory Models (`hott/`)

| Module | Key Classes and Functions | Verified Theorems |
|--------|---------------------------|-------------------|
| `hott/identity.py` | `Path`, `refl`, `J`, `concat`, `inv`, `ap`, `transport` | Groupoid laws, J-computation, and transport functoriality |
| `hott/equivalence.py` | `Homotopy`, `Fiber`, `ContractibleWitness`, `IsEquiv`, `Equiv` | Equivalence composition, inversion, and contractible fibers |
| `hott/truncation.py` | `TruncationLevel`, `check_is_contr`, `check_is_prop`, `check_is_set`, `hedberg_set_witness` | Cumulative $n$-type hierarchy and Hedberg's theorem |
| `hott/univalence.py` | `id_to_equiv`, `ua`, `transport_ua`, `derive_funext_from_ua`, `prop_ext_from_ua` | Univalence computation rules, funext derivation, and propext |
| `hott/hit.py` | `IntervalHIT`, `CircleHIT`, `SuspensionHIT`, `TorusHIT` | Interval funext, $S^1 \simeq \Sigma\mathbf{2}$, $\pi_1(S^1) \cong \mathbb{Z}$, and $T^2 \simeq S^1 \times S^1$ |
| `hott/connectivity.py` | `ConnectivityLevel`, `PushoutSquare`, `blakers_massey_connectivity`, `freudenthal_suspension` | Blakers-Massey connectivity bound $n + m$ and Freudenthal bound $2n$, yielding $\pi_k(S^n) = 0$ ($k < n$) and $\pi_n(S^n) \cong \mathbb{Z}$ |
