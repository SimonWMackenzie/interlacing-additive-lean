import EthInapproximability.ParameterizedNP.InheritedContracts

/-!
# Parameterized NP route: the defect induction of the direct bridge

Route: **parameterized NP-hardness** (`routes/parameterized-np/`, active).

Autoformalization anchors (frozen release named by
`routes/parameterized-np/CURRENT_VERSION`, i.e.
`routes/parameterized-np/versions/2026-08-02-iteration-cexc-repair/source/autoformalization`),
all in `sections/10-direct-bridge.tex`:

* `eq:direct-input` (line 11) — the two common-threshold input clauses
  `D_W(1, θ, 1 - δ_U) ≥ C_W` and `Λ_W(1, θ, y) ≥ C_W - 1`;
* `eq:direct-two-copy` (line 24) — the inherited two-copy ladder output
  `Λ_W(2, 2θ, y²) ≥ C_W`;
* `eq:direct-three-copy` (line 31) — `D(W[3, 4θ, y²]) ≥ C_W + 1`, legal when
  `4θ ≤ 1` (line 27);
* `λ = -ln(1 - δ_U)` (line 43) and the globally fixed `δ = 1/10`, `y = 3/5`
  (lines 36--37);
* `eq:direct-entry-gates` (line 56) — its **second** inequality
  `3λ + (7/5) ln 2 ≤ -2 ln y` is the hypothesis `lem:defect-induction`
  re-assumes by name (line 223);
* `A_a = ⌈m 2^a θ⌉` (line 82), the level restriction "we use only levels for
  which `2^a θ ≤ 1`" (line 84), and `eq:direct-ceiling-ladder` (line 88);
* `Def(K) = ln (n^p / |K|)` (line 96) and the sentence at line 98, "a defect
  bound `Def(K) ≤ L` is the same as normalized density at least `e^{-L}`";
* `B(p) = (1 + 6/(5p)) ln 2` (line 193) and `eq:direct-B-inequalities`
  (line 206);
* `c_a(p) = p - 2^{a-1}` (line 217) with "the half-integer value at `a = 0` is
  intentional" (line 219);
* **`lem:defect-induction`** (line 222) — the deliverable of this module;
* **`clm:direct-auxiliary`** (line 237) — the one-bit-down auxiliary statement
  with the additive `B(p)` allowance;
* `eq:direct-bob-recursion` (equation lines 296--301, label line 300), whose
  first half, at line 297, is the excess-copy ceiling halving.

Reader counterparts (`routes/parameterized-np/reader-facing/`), each opened and
checked to state the same fact, and each assigned to exactly one declaration
here:

* `sections/04-bridge.tex`, `lem:bridge-defect-amplification` (label line 57,
  statement lines 58--71) — the reader form of `lem:defect-induction`; it is
  the counterpart of `defectInduction`.
* `sections/B-bridge-details.tex`, `lem:bridge-auxiliary-defect` (label line
  79, statement lines 80--88) — the reader form of `clm:direct-auxiliary`; it
  is the counterpart of `auxiliaryDefectBound`.
* `sections/B-bridge-details.tex`, §"Ceilings and the auxiliary allowance"
  (line 39): `A_a` and `eq:appendix-ceiling-ladder` (line 44) for `rowFloor`
  and its ladder lemma; `c_a(p)` with `c_0(p) = p - 1/2` (lines 46--50) for
  `excessCopies`; `B(p)` (line 52) and `eq:appendix-B-arithmetic` (line 65)
  for `bobAllowance` and its four inequalities.
* `sections/B-bridge-details.tex`, line 16 — the reader definition
  `Δ_p(K) = ln (n^p / |K|)`, the reader form of the `Def` readout already
  banked as `InheritedContracts.columnDefect`.

These reader items are disjoint from the ones assigned in `INHERIT-001`.
That module's recorded reader counterparts (`InheritedContracts.lean`, module
header) are exactly `sections/02-preliminaries.tex` §"The inherited classical
engine" (line 111) with `prop:paper-projection-facts` (line 120), and
`sections/04-bridge.tex` `thm:near-to-robust` (line 82).  None of those is
claimed here, and none of the items claimed here is claimed there, so nothing
is cited twice.  Note that the reader's own projection sentences,
`sections/B-bridge-details.tex` lines 18--21 and 29--32, are the prose
matching `INHERIT-001`'s content but are *not* listed in its counterpart
record; they remain unassigned and are not claimed by this module either.
No prose paragraph is used as a statement counterpart: the only two statement
counterparts here are the genuine reader lemmas `lem:bridge-defect-amplification`
and `lem:bridge-auxiliary-defect`.

Crosswalk row: `READER_CROSSWALK.md`, "Generic robustness bridge".

## Vendored-counterpart finding (the case that applies)

The tranche brief asks which case applies: *a kernel-checked counterpart
already exists in the vendored `EthBridge` development, and it is consumed
here rather than re-proved.*

* `EthBridge.theorem_one` (`vendor/npc-cc/EthBridge/Main.lean:665`) is the
  kernel-checked per-member counterpart of `lem:defect-induction`.  It is
  already covered by `tools/AxiomAudit.lean` (line 6).
* `EthBridge.one_bit_down` (`vendor/npc-cc/EthBridge/Induction.lean:1470`) is
  the kernel-checked counterpart of `clm:direct-auxiliary`.
* `EthBridge.Bdef`, `EthBridge.cExcess`, `EthBridge.rowThreshold`,
  `EthBridge.colDefect` (`vendor/npc-cc/EthBridge/Defs.lean:43, 56, 66, 78`)
  are the vendored readouts; `EthBridge.Bdef_ge_log2`, `Bdef_antitone`,
  `Bdef_ceil_halving`, `Bdef_three`, `cExcess_ceil_halving`,
  `rowThreshold_ceil_halving`, `rowThreshold_mono`, `margin`, and
  `state_defect_iff_density` are the kernel-checked arithmetic.

Both vendored theorems are stated in the *density* form
`|K| ≥ n^p e^{-(...)}`; the frozen paper states the *defect* form
`Def(K) ≤ ...` and demands a nonempty `K` (line 96 defines `Def` as a genuine
logarithm, and the guard list at lines 101--104 lists "nonempty `K`").  This
module therefore states the paper's defect form with `K.Nonempty` as an
explicit binder and converts through `EthBridge.state_defect_iff_density`; the
conversion is exactly the sentence at line 98 and adds no mathematics.

Everything the vendored proofs need beyond the frozen statement is a *named*
hypothesis here, never an axiom: `eq:direct-input` clause one and
`eq:direct-two-copy` are carried as the explicit binders `hNear` and
`hTwoCopy`.

## Status and dependencies

* Proof status: **inherited** for `defectInduction` and
  `auxiliaryDefectBound` (the vendored terms are consumed, never re-proved and
  never widened); **new (elementary)** for the readout definitions, the aux
  battery, the `δ_U` corollary, and the non-vacuity witnesses.
* Imports: `EthInapproximability.ParameterizedNP.InheritedContracts`, hence
  `EthInapproximability.Prelude`, hence `LegacyNPCC.Core` (project-axiom-free)
  and `LegacyNPCC.Bridge`.  `LegacyNPCC.Stage12` is **not** imported, so the
  cited AGHP balanced-family axiom is not in scope.
* External adapters: none.  Nothing here is axiomatized.  `EXPANDER-001` is
  not touched by this module.
* Axiom surface: `propext`, `Classical.choice`, `Quot.sound`, audited in
  `tools/AxiomAudit.lean`.
* Ledger rows: `BRIDGE-001` (this is its `lem:defect-induction` component),
  consuming `INHERIT-001`.

## GAP-EXPOSED in this tranche (nothing is weakened to close them)

1. `lem:copy-restriction` (`10-direct-bridge.tex:132`, exact-image copy
   restriction) is **not** landed here.  It is an internal step of the
   frozen proof of `lem:defect-induction`; because the vendored counterpart
   supplies the whole induction, the route does not need it to state or use
   the lemma, but it remains a separate reboot obligation, exactly as the
   `INHERIT-001` ledger row already records.
2. `thm:direct-robustification` (`10-direct-bridge.tex:35`), the entry at the
   requested robust depth, is not landed here.  Only its second entry gate
   (`eq:direct-entry-gates`, second inequality) appears, as the hypothesis the
   defect induction re-assumes.
3. The premise bundle of `defectInduction` has **no exhibited inhabitant** in
   this module, and none can be exhibited until Stages 1--4 land in Lean.  The
   two semantic facts the module carries are `eq:direct-input` clause one (the
   near-full clause, at density `e^{-λ} = 1 - δ_U`) and `eq:direct-two-copy`;
   the latter is *not* a clause of `eq:direct-input` but the ladder output the
   frozen section derives from clause two at lines 19--25.  Both are
   construction outputs of Sections 8--9 for the pinned `W`, and both are
   carried here as explicit named hypotheses, never as axioms.  The firing
   witness `defectInduction_fires` is therefore *conditional only*: every
   purely numeric guard, the row condition, the defect condition and its
   strict positivity are discharged unconditionally and the delivered bound is
   a real consequence of the two carried facts, but nothing here asserts that
   any `W` satisfying them exists.  This is faithful to the frozen section,
   whose opening sentence (line 3) is that all construction-specific
   information has already been discarded.
4. `eq:direct-two-copy` is **assumed, not derived**.  The frozen section
   derives it from `eq:direct-input` clause two by the inherited two-copy
   ladder under `C_W ≥ 3` and `2θ ≤ 1` (lines 19--25).  The checked inherited
   declaration `NPCC.two_copy_ladder`, whose exact guards are
   `eq:contract-two-copy-input` and whose conclusions are
   `eq:contract-two-copy-output` (`D-inherited-contracts.tex:317`, with the
   substitution `H = C_W - 1` and the guard `1 < H` discharged by `C_W ≥ 3`),
   is landable now; it is opened as its own ledger row `BRIDGE-TWOCOPY-001`
   and belongs to its own tranche, never to an ad hoc port.  Taking the
   derived form as a binder makes this module's lemma weaker than the
   paper's, so nothing is overclaimed by the omission.
5. Pinning the firing witness at `X = Y = Bool` is **refutable**, not merely
   unproved.  `nearFull_refuted_of_two_rows` proves that `|X| = 2` and
   `C_W ≥ 3` are jointly incompatible with the near-full clause, and
   `andPair_nearFull_refuted` records the instance itself.  The firing witness
   is therefore stated at universally quantified `X`, `Y`, `W`, and `C_W`,
   with only the numeric parameters and the carrier shapes pinned.

## Faithfulness notes (mechanical rules M1--M10)

* `bobAllowance`, `excessCopies`, `rowFloor` transcribe the paper's closed
  forms literally and are proved to be the vendored readouts by `rfl`, so no
  second definition of the same quantity is introduced.
* `excessCopies` keeps the integer exponent in `ℤ`, so `c_0(p) = p - 1/2` is
  the intentional half-integer of line 219 rather than a truncated `ℕ` power.
* The copy guard `p > 2^{a-1}` is rendered `2 ^ a < 2 * p` in `ℕ`.  This is
  exact at **every** level including `a = 0`, where the truncated spelling
  `2 ^ (a - 1) < p` would read `1 < p` instead of the paper's `p > 1/2`.
* No complexity or robustness conclusion is placed in constructor data: the
  three readouts are plain functions of public parameters, and both
  deliverables use explicit binders rather than a premise bundle, so no
  derived telescope is restated as a structure field.
* Interlace widths are untouched: this module is generic in the copy count
  `p` of `Interlace(W,p)` and introduces neither `q` nor `Q`.
* Trivial-conclusion pole.  Both deliverables are universally quantified
  implications, so the pole is not an existential witness but a vacuous
  conclusion: `C_W + a ≤ D(...)` would be free if `C_W + a` could be `0`.  The
  guard `3 ≤ C_W` (line 40 of the frozen section) excludes it, and the pinned
  witness below records the resulting bound `5 ≤ D(...)` explicitly.
* Vacuous-hypothesis pole.  A row/defect premise that no carrier satisfies
  would also make the lemma free.  `defectInduction_state_nondegenerate`
  exhibits a carrier pair satisfying both *carrier-level* premises at legal
  parameters, with the column carrier a **proper** subset of `Y^{[p]}` of
  strictly positive defect, so the **defect** premise is not satisfiable only
  at the degenerate full carrier (`columnDefect_univ` records that the full
  carrier has defect `0`).  Its **row** carrier is `Finset.univ`, and at the
  `θ = 1/4` assignment it has to be: there `A_2 = ⌈m·4·(1/4)⌉ = m`, so
  `IsEquipartitionedGE R univ m` forces every fibre to be all of `X`.  The
  companion `defectInduction_state_nondegenerate_properRows` therefore repeats
  the same witness at `θ = 1/8`, where `A_2 = 1` and a **proper** row carrier
  satisfies the row premise, with `R ≠ Finset.univ` as an explicit conjunct.
  Neither witness mentions `W` or `C_W`, so neither is a witness for the whole
  premise bundle; the two semantic clauses are handled by the conditional
  firing witness and by the refutation lemma of GAP-EXPOSED item 5.
* Sufficient-condition pole.  Aux 15 discharges the entry gate from
  `λ ≤ 17/1000`, and a sufficient condition that were vacuous or absurdly slack
  would hide rather than check the gate.  `entry_gate_lambda_window` pins the
  exact threshold at the globally fixed `y = 3/5` into `(17/1000, 18/1000)` and
  records that the gate **fails** at `λ = -ln(1 - δ)` for the globally fixed
  `δ = 1/10`, so the deletion tolerance `δ_U` of `eq:direct-input` is strictly
  smaller than `δ` and the two frozen constants must not be conflated.
-/

namespace EthInapproximability.ParameterizedNP.DefectInduction

open NPCC
open Workspace.Types.Interlace
open Workspace.Types.CommComplexity
open EthInapproximability.ParameterizedNP.InheritedContracts

/-! ## The three level readouts of `sec:defect-induction`

`Def(K)` itself is not redefined: it is `InheritedContracts.columnDefect`,
banked under `INHERIT-001` from the same anchor (`10-direct-bridge.tex:96`). -/

/-- **`B(p) = (1 + 6/(5p)) ln 2`** (`10-direct-bridge.tex:193`), the Bob-defect
allowance absorbed by `clm:direct-auxiliary`.  Reader: `B-bridge-details.tex`
line 52.

Used only for integer `p ≥ 2`, as the paper says at line 191. -/
noncomputable def bobAllowance (p : ℕ) : ℝ :=
  (1 + 6 / (5 * (p : ℝ))) * Real.log 2

/-- **`c_a(p) = p - 2^{a-1}`** (`10-direct-bridge.tex:217`), the excess-copy
count.  Reader: `B-bridge-details.tex` lines 46--50.

The exponent is taken in `ℤ`, so `c_0(p) = p - 1/2` is the intentional
half-integer of line 219 and not a truncated natural power. -/
noncomputable def excessCopies (a p : ℕ) : ℝ :=
  (p : ℝ) - (2 : ℝ) ^ ((a : ℤ) - 1)

/-- **`A_a = ⌈m 2^a θ⌉`** (`10-direct-bridge.tex:82`), the retained-row floor
per active copy, with `m = |Rows(W)| = |X|`.  Reader: `B-bridge-details.tex`
line 41. -/
noncomputable def rowFloor (m : ℕ) (θ : ℝ) (a : ℕ) : ℕ :=
  ⌈(m : ℝ) * (2 : ℝ) ^ a * θ⌉₊

/-! ### The readouts are the vendored ones

Each of the four identifications is `rfl`, which is what allows the vendored
kernel-checked theorems to be consumed without restating any quantity. -/

theorem bobAllowance_eq (p : ℕ) : bobAllowance p = EthBridge.Bdef p := rfl

theorem excessCopies_eq (a p : ℕ) : excessCopies a p = EthBridge.cExcess a p :=
  rfl

theorem rowFloor_eq (m : ℕ) (θ : ℝ) (a : ℕ) :
    rowFloor m θ a = EthBridge.rowThreshold m θ a := rfl

theorem columnDefect_eq_colDefect {Y : Type*} [Fintype Y] {k : ℕ}
    (C : Finset (Fin k → Y)) : columnDefect C = EthBridge.colDefect Y k C := rfl

/-! ## Aux-lemma battery

General properties of the three readouts and of the guard shape.  Every
statement below is about arbitrary levels, copy counts, and carriers — none of
them mentions the pinned witness. -/

/-- **Aux 1 (calibration at `a = 0`).**  `c_0(p) = p - 1/2`: the intentional
half-integer of `10-direct-bridge.tex:219`, which is what makes the terminal
one-copy projection strictly denser than `e^{-λ}` in the level-zero case of the
frozen proof (line 310). -/
lemma excessCopies_zero (p : ℕ) : excessCopies 0 p = (p : ℝ) - 1 / 2 := by
  unfold excessCopies
  norm_num

/-- **Aux 2 (calibration at `a ≥ 1`).**  `c_{a+1}(p) = p - 2^a`: at every
positive level the exponent is a genuine natural power. -/
lemma excessCopies_succ (a p : ℕ) :
    excessCopies (a + 1) p = (p : ℝ) - (2 : ℝ) ^ a := by
  unfold excessCopies
  have h : ((a + 1 : ℕ) : ℤ) - 1 = (a : ℤ) := by push_cast; ring
  rw [h, zpow_natCast]

/-- **Aux 3 (sign).**  The copy guard `p > 2^{a-1}` — written `2 ^ a < 2 * p`
in `ℕ` — is exactly positivity of the excess-copy count, so the defect budget
`c_a(p) λ` is positive whenever `λ` is. -/
lemma excessCopies_pos {a p : ℕ} (hp : 2 ^ a < 2 * p) : 0 < excessCopies a p := by
  have hcast : (2 : ℝ) ^ a < 2 * (p : ℝ) := by exact_mod_cast hp
  have hzpow : (2 : ℝ) ^ ((a : ℤ) - 1) = (2 : ℝ) ^ a / 2 := by
    rw [show (a : ℤ) - 1 = (a : ℤ) + (-1) by ring,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast, zpow_neg_one]
    ring
  unfold excessCopies
  rw [hzpow]
  linarith

/-- **Aux 4 (`ℕ`-guard reshaping).**  At levels `a ≥ 1` the doubled copy guard
`2 ^ a < 2 * p` is the truncated guard `2 ^ (a - 1) < p`.  The two spellings
differ only at `a = 0`, where the paper's `p > 1/2` is the doubled form. -/
lemma copies_halved {a p : ℕ} (ha : 1 ≤ a) (hp : 2 ^ a < 2 * p) :
    2 ^ (a - 1) < p := by
  have h : (2 : ℕ) ^ a = 2 * 2 ^ (a - 1) := by
    conv_lhs => rw [show a = (a - 1) + 1 by omega]
    rw [pow_succ]
    ring
  omega

/-- **Aux 5 (`eq:direct-B-inequalities`, first).**  `B(p) ≥ ln 2` for `p ≥ 2`
(`10-direct-bridge.tex:199`; reader `eq:appendix-B-arithmetic`, line 57). -/
lemma log_two_le_bobAllowance (p : ℕ) (hp : 2 ≤ p) :
    Real.log 2 ≤ bobAllowance p :=
  EthBridge.Bdef_ge_log2 p hp

/-- **Aux 6 (`eq:direct-B-inequalities`, second).**  `B` is antitone on
`[2, ∞)`: `B(p') ≥ B(p)` whenever `2 ≤ p' ≤ p` (`10-direct-bridge.tex:200`). -/
lemma bobAllowance_antitone (p p' : ℕ) (hp' : 2 ≤ p') (hpp : p' ≤ p) :
    bobAllowance p ≤ bobAllowance p' :=
  EthBridge.Bdef_antitone p p' hp' hpp

/-- **Aux 7 (`eq:direct-B-inequalities`, third).**
`B(⌈p/2⌉) ≥ (⌈p/2⌉ / p) (B(p) + ln 2)` for `p ≥ 3`
(`10-direct-bridge.tex:201-203`).  This is the inequality that lets the Bob
branch of `clm:direct-auxiliary` re-enter the auxiliary statement after the
maximum projection to `⌈p/2⌉` copies. -/
lemma bobAllowance_ceil_halving (p : ℕ) (hp : 3 ≤ p) :
    ((((p + 1) / 2 : ℕ) : ℝ) / (p : ℝ)) * (bobAllowance p + Real.log 2)
      ≤ bobAllowance ((p + 1) / 2) :=
  EthBridge.Bdef_ceil_halving p hp

/-- **Aux 8 (`eq:direct-B-inequalities`, fourth).**
`(3/p) B(p) ≤ (7/5) ln 2` for `p ≥ 3`, tight at `p = 3`
(`10-direct-bridge.tex:204`).  Together with the entry gate this is what makes
the three-copy projection of the `a = 2` base land at density `y²`. -/
lemma bobAllowance_three (p : ℕ) (hp : 3 ≤ p) :
    (3 / (p : ℝ)) * bobAllowance p ≤ (7 / 5) * Real.log 2 :=
  EthBridge.Bdef_three p hp

/-- **Aux 9 (`eq:direct-bob-recursion`, first half).**
`(⌈p/2⌉ / p) c_a(p) ≤ c_{a-1}(⌈p/2⌉)` for `a ≥ 1`
(`10-direct-bridge.tex:297`, the first half of the equation at lines 296--301
labelled at line 300; reader `eq:appendix-B-arithmetic`, lines 62--63). -/
lemma excessCopies_ceil_halving (a p : ℕ) (ha : 1 ≤ a)
    (hp : (2 : ℝ) ^ ((a : ℤ) - 1) < (p : ℝ)) :
    ((((p + 1) / 2 : ℕ) : ℝ) / (p : ℝ)) * excessCopies a p
      ≤ excessCopies (a - 1) ((p + 1) / 2) :=
  EthBridge.cExcess_ceil_halving a p ha hp

/-- **Aux 10 (`eq:direct-ceiling-ladder`).**  `A_{a-1} ≤ ⌈A_a / 2⌉` for
`a ≥ 1` (`10-direct-bridge.tex:88`; reader `eq:appendix-ceiling-ladder`, line
44).  This is the bookkeeping that lets Alice's first bit halve the retained
row count and still land at the next lower level. -/
lemma rowFloor_ceiling_ladder (m : ℕ) (θ : ℝ) (a : ℕ) (ha : 1 ≤ a) :
    rowFloor m θ (a - 1) ≤ ⌈(rowFloor m θ a : ℝ) / 2⌉₊ :=
  EthBridge.rowThreshold_ceil_halving m θ a ha

/-- **Aux 11 (calibration at `a = 0`).**  `A_0 = ⌈m θ⌉`, the row floor of the
bracket family `bracketGE X Y p θ ·` itself, so level zero of the induction
sits exactly on the inherited bracket threshold. -/
lemma rowFloor_zero (m : ℕ) (θ : ℝ) : rowFloor m θ 0 = ⌈(m : ℝ) * θ⌉₊ := by
  unfold rowFloor
  norm_num

/-- **Aux 12 (monotonicity in the level).**  `A_a ≤ A_{a'}` for `a ≤ a'` and
`0 ≤ θ`: a state with at least `A_a` rows per block is in particular a
candidate at every lower level. -/
lemma rowFloor_mono (m : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) {a a' : ℕ} (haa : a ≤ a') :
    rowFloor m θ a ≤ rowFloor m θ a' :=
  EthBridge.rowThreshold_mono m θ hθ haa

/-- **Aux 13 (the defect/density dictionary).**  The sentence at
`10-direct-bridge.tex:98`: for a nonempty column carrier over a nonempty `Y`,
`Def(K) ≤ L` is the same as normalized density at least `e^{-L}`.  This is the
only conversion used to consume the vendored density-form theorems. -/
lemma columnDefect_le_iff_density {Y : Type*} [Fintype Y] {k : ℕ}
    (K : Finset (Fin k → Y)) (L : ℝ) (hK : K.Nonempty)
    (hY : 1 ≤ Fintype.card Y) :
    columnDefect K ≤ L ↔
      ((Fintype.card Y : ℝ) ^ k) * Real.exp (-L) ≤ (K.card : ℝ) :=
  EthBridge.state_defect_iff_density Y k K L (Finset.card_pos.mpr hK)
    (lt_of_lt_of_le Nat.zero_lt_one hY)

/-- **Aux 14 (`λ = -ln(1 - δ_U)`).**  The definition at
`10-direct-bridge.tex:43` inverts to `e^{-λ} = 1 - δ_U`, and `λ > 0` for every
legal deletion tolerance `0 < δ_U < 1`.  This is what lets the paper's literal
first input clause be stated with `1 - δ_U` and consumed at density
`e^{-λ}`. -/
lemma exp_neg_lambda {δU : ℝ} (hδ0 : 0 < δU) (hδ1 : δU < 1) :
    Real.exp (-(-Real.log (1 - δU))) = 1 - δU ∧ 0 < -Real.log (1 - δU) := by
  have hpos : (0 : ℝ) < 1 - δU := by linarith
  constructor
  · rw [neg_neg, Real.exp_log hpos]
  · have : Real.log (1 - δU) < 0 := Real.log_neg hpos (by linarith)
    linarith

/-- **Aux 15 (the entry gate at the globally fixed `y = 3/5`).**  The second
inequality of `eq:direct-entry-gates` (`10-direct-bridge.tex:55`) holds at the
globally fixed `y = 1/2 + δ = 3/5` (line 37) for every `0 < λ ≤ 17/1000`.
This makes the gate a *checkable* condition on the deletion tolerance rather
than an unexamined hypothesis. -/
lemma entry_gate_of_lambda_small {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam ≤ 17 / 1000) :
    3 * lam + (7 / 5) * Real.log 2 ≤ -2 * Real.log (3 / 5) :=
  EthBridge.margin lam hlam0 hlam

/-- **Aux 16 (general row-carrier inhabitation).**  The full row carrier of a
`p`-fold interlace meets every row floor that its `X`-fibres can meet, so the
row premise of the defect induction is never vacuous when `A_a ≤ |X|`. -/
lemma univ_rows_equipartitionedGE {ι X : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype X] (T : ℕ) (hT : T ≤ Fintype.card X) :
    IsEquipartitionedGE (Finset.univ : Finset (ι × X))
      (Finset.univ : Finset ι) T := by
  classical
  intro q _
  refine le_trans hT ?_
  have hcard : (Finset.univ : Finset X).card ≤
      ((Finset.univ : Finset (ι × X)).filter (fun r => r.1 = q)).card := by
    refine Finset.card_le_card_of_injOn (fun x => (q, x)) ?_ ?_
    · intro x _
      simp
    · intro a _ b _ hab
      exact (Prod.mk.injEq q a q b ▸ hab).2
  simpa [Finset.card_univ] using hcard

/-- **Aux 17 (positivity criterion for the defect readout).**  A nonempty
column carrier has strictly positive defect exactly when it is a **proper**
subset of `Y^{[k]}`.  This is the general test behind every non-vacuity
witness below: `columnDefect_univ` says the full carrier reads `0`, and this
lemma says nothing else does. -/
lemma columnDefect_pos_iff {Y : Type*} [Fintype Y] {k : ℕ}
    (C : Finset (Fin k → Y)) (hC : C.Nonempty) (hY : 1 ≤ Fintype.card Y) :
    0 < columnDefect C ↔ (C.card : ℝ) < (Fintype.card Y : ℝ) ^ k := by
  classical
  have hn : (1 : ℝ) ≤ (Fintype.card Y : ℝ) := by exact_mod_cast hY
  have hnk : (0 : ℝ) < (Fintype.card Y : ℝ) ^ k := by positivity
  have hCpos : (0 : ℝ) < (C.card : ℝ) := by
    have : 0 < C.card := Finset.card_pos.mpr hC
    exact_mod_cast this
  unfold columnDefect
  rw [Real.log_pos_iff (by positivity), lt_div_iff₀ hCpos, one_mul]

/-! ## The deliverables

Both are stated in the frozen paper's **defect** form, with the nonemptiness of
the column carrier an explicit binder, and both consume a vendored
kernel-checked term. -/

/-- **`lem:defect-induction`** (`10-direct-bridge.tex:222`; reader
`lem:bridge-defect-amplification`, `04-bridge.tex:57`).

Assume the second inequality of `eq:direct-entry-gates` (`hmargin`).  Let
`a ≥ 0` and `p > 2^{a-1}` (rendered `2 ^ a < 2 * p`, exact at every level).
Every restriction of `Interlace(W, p)` that retains at least `A_a` rows in each
active copy and has a nonempty column set `K` with `Def(K) ≤ c_a(p) λ` has
communication complexity at least `C_W + a`.

The two ambient inputs of the section appear as the explicit binders `hNear`
(`eq:direct-input`, first clause, at density `e^{-λ} = 1 - δ_U`) and
`hTwoCopy` (`eq:direct-two-copy`).  The ambient level restriction
`2^a θ ≤ 1` (line 84) and the ambient legality `4θ ≤ 1` (line 27) are the
binders `hlevel` and `hθ`.

The vendored `EthBridge.theorem_one` is *consumed*: after the defect/density
dictionary of Aux 13, the body is exactly the inherited term, so the axiom
surface is unchanged. -/
theorem defectInduction {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (CW p a : ℕ) (θ y lam : ℝ)
    (hp : 2 ^ a < 2 * p)
    (hlevel : (2 : ℝ) ^ a * θ ≤ 1)
    (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 4)
    (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hlam : 0 < lam)
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y) (hCW : 3 ≤ CW)
    (hmargin : 3 * lam + (7 / 5) * Real.log 2 ≤ -2 * Real.log y)
    (hNear : CW ≤ Dfamily (interlaceFun W 1)
      (bracketGE X Y 1 θ (Real.exp (-lam))))
    (hTwoCopy : CW ≤ LambdaGE W 2 (2 * θ) (y ^ 2))
    (R : Finset (Fin p × X)) (K : Finset (Fin p → Y))
    (hK : K.Nonempty)
    (hrows : IsEquipartitionedGE R (Finset.univ : Finset (Fin p))
      (rowFloor (Fintype.card X) θ a))
    (hdefect : columnDefect K ≤ excessCopies a p * lam) :
    CW + a ≤ D (subgame (interlaceFun W p) R K) := by
  have hmem : ((R, K) : Finset (Fin p × X) × Finset (Fin p → Y)) ∈
      EthBridge.stateDensity X Y p a θ lam :=
    ⟨hrows, (columnDefect_le_iff_density K (excessCopies a p * lam) hK hY).mp
      hdefect⟩
  exact EthBridge.theorem_one W CW p a θ y lam hp hlevel hθ0 hθ hy0 hy1 hlam
    hX hY hCW hmargin hNear hTwoCopy (R, K) hmem

/-- **`clm:direct-auxiliary`** (`10-direct-bridge.tex:237`; reader
`lem:bridge-auxiliary-defect`, `B-bridge-details.tex:79`).

For `a ≥ 2` and `p > 2^{a-1}`, the same row condition together with the
one-bit-weaker defect budget `Def(K) ≤ c_a(p) λ + B(p)` implies complexity at
least `C_W + a - 1`.

`hNear` is deliberately **absent**: the frozen proof of this claim (lines
245--305) consumes only `eq:direct-three-copy` at its `a = 2` base and
`eq:direct-two-copy` through the Alice/Bob recursion; the near-full clause of
`eq:direct-input` enters only at level `a = 0` of `lem:defect-induction`
(line 310--314).  The reader's own statement (`B-bridge-details.tex:80`) lists
`a ≥ 2`, `p > 2^{a-1}`, and `2^a θ ≤ 1` and nothing else, and `hlevel` is
carried for that fidelity.

The vendored `EthBridge.one_bit_down` is *consumed*. -/
theorem auxiliaryDefectBound {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (CW p a : ℕ) (θ y lam : ℝ)
    (ha : 2 ≤ a) (hp : 2 ^ a < 2 * p)
    (hlevel : (2 : ℝ) ^ a * θ ≤ 1)
    (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 4)
    (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hlam : 0 < lam)
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y) (hCW : 3 ≤ CW)
    (hmargin : 3 * lam + (7 / 5) * Real.log 2 ≤ -2 * Real.log y)
    (hTwoCopy : CW ≤ LambdaGE W 2 (2 * θ) (y ^ 2))
    (R : Finset (Fin p × X)) (K : Finset (Fin p → Y))
    (hK : K.Nonempty)
    (hrows : IsEquipartitionedGE R (Finset.univ : Finset (Fin p))
      (rowFloor (Fintype.card X) θ a))
    (hdefect : columnDefect K ≤ excessCopies a p * lam + bobAllowance p) :
    CW + (a - 1) ≤ D (subgame (interlaceFun W p) R K) := by
  have _ := hlevel
  have hmem : ((R, K) : Finset (Fin p × X) × Finset (Fin p → Y)) ∈
      EthBridge.obdState X Y p a θ lam :=
    ⟨hrows, (columnDefect_le_iff_density K
      (excessCopies a p * lam + bobAllowance p) hK hY).mp hdefect⟩
  exact EthBridge.one_bit_down W CW p a θ y lam ha
    (copies_halved (le_trans (by norm_num) ha) hp) hθ0 hθ hy0 hy1 hlam hX hY
    hCW hmargin hTwoCopy (R, K) hmem

/-- **`lem:defect-induction` in the paper's literal `δ_U` spelling.**

`eq:direct-input` (`10-direct-bridge.tex:9`) states the first clause at column
density `1 - δ_U`, and `λ = -ln(1 - δ_U)` is defined at line 43.  This
corollary is the same lemma with those two literals in place, so no call site
has to perform the exponential substitution by hand. -/
theorem defectInduction_ofDeltaU {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (CW p a : ℕ) (θ y δU : ℝ)
    (hδ0 : 0 < δU) (hδ1 : δU < 1)
    (hp : 2 ^ a < 2 * p)
    (hlevel : (2 : ℝ) ^ a * θ ≤ 1)
    (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 4)
    (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y) (hCW : 3 ≤ CW)
    (hmargin : 3 * (-Real.log (1 - δU)) + (7 / 5) * Real.log 2 ≤
      -2 * Real.log y)
    (hNear : CW ≤ Dfamily (interlaceFun W 1) (bracketGE X Y 1 θ (1 - δU)))
    (hTwoCopy : CW ≤ LambdaGE W 2 (2 * θ) (y ^ 2))
    (R : Finset (Fin p × X)) (K : Finset (Fin p → Y))
    (hK : K.Nonempty)
    (hrows : IsEquipartitionedGE R (Finset.univ : Finset (Fin p))
      (rowFloor (Fintype.card X) θ a))
    (hdefect : columnDefect K ≤ excessCopies a p * (-Real.log (1 - δU))) :
    CW + a ≤ D (subgame (interlaceFun W p) R K) := by
  obtain ⟨hexp, hlam⟩ := exp_neg_lambda hδ0 hδ1
  refine defectInduction W CW p a θ y (-Real.log (1 - δU)) hp hlevel hθ0 hθ
    hy0 hy1 hlam hX hY hCW hmargin ?_ hTwoCopy R K hK hrows hdefect
  rw [hexp]
  exact hNear

end EthInapproximability.ParameterizedNP.DefectInduction

/-! # Non-vacuity witnesses

LANE-GATE 3.  Four separate degeneracies are excluded, each by its own
witness, because a green build sees none of them:

1. **Vacuous guard bundle.**  `defectInduction_guards_legal` discharges every
   purely numeric guard of `defectInduction` simultaneously at one legal
   assignment — `a = 2`, `p = 10`, `θ = 1/4`, `y = 3/5`, `λ = 1/100`,
   `C_W = 3`, `|X| = |Y| = 2` — with the two guards that could be silently
   contradictory, `θ ≤ 1/4` and `2^a θ ≤ 1`, both **tight**.  The entry gate
   is not assumed: it is derived from `λ ≤ 17/1000` through Aux 15.  This is a
   statement about numbers only; it is **not** the gate artifact for the
   premise bundle, since it contains no `W`.
2. **Degenerate state, column side.**  `defectInduction_state_nondegenerate`
   exhibits a carrier pair meeting both carrier-level premises with the column
   carrier a **proper** subset of `Y^{[p]}` carrying **strictly positive**
   defect, so the defect premise is not satisfiable only at the full carrier,
   whose defect is `0` (`columnDefect_univ`).  It, too, contains no `W` and no
   `C_W`.  It pins `θ = 1/4`, where `θ ≤ 1/4` and `2^a θ ≤ 1` are both tight;
   that tightness forces its row carrier to be `Finset.univ`, which is why the
   next item exists.
2b. **Degenerate state, row side.**
   `defectInduction_state_nondegenerate_properRows` repeats the same witness at
   the still-legal `θ = 1/8`, where `A_2 = ⌈2·4·(1/8)⌉ = 1`.  There the row
   premise is met by `properRows`, one row per active copy, and
   `properRows ≠ Finset.univ` is an explicit conjunct, so the row floor is
   exercised on a genuine restriction and not only at the full row carrier.
   The two witnesses are complementary and both are kept: `θ = 1/4` shows the
   numeric guards are jointly satisfiable at their tight boundary, `θ = 1/8`
   shows both carrier premises are satisfiable strictly inside their carriers.
3. **Self-refuting instantiation.**  Pinning the whole bundle at
   `X = Y = Bool` would make the firing witness a vacuously true implication:
   `nearFull_refuted_of_two_rows` proves that at `|X| = 2` the near-full
   clause fails for **every** matrix and every `C_W ≥ 3`, because a one-row
   `p = 1` bracket member is computed by a single Bob bit, and
   `andPair_nearFull_refuted` records the refuted instance itself.  The firing
   witness `defectInduction_fires` is therefore stated at universally
   quantified `X`, `Y`, `W`, `C_W`, so its two carried hypotheses are not
   self-refuting, and no later lane can re-pin the contradictory instance
   without contradicting a landed lemma.
4. **Degenerate child defect.**  `projectionBound_admits_positive_child_defect`
   is the now-due `Def(C') > 0` instance for the projection interface — named
   for what it proves, since the returned carrier of the existential
   `defectProjection` is *not* claimed to have positive defect: at `|Y| = 2`,
   `ℓ = 1`, `p = 2` the bound `Def(C') ≤ (1/2) Def(C)` returned by
   `INHERIT-001`'s `defectProjection_nondegenerate` is in fact only satisfiable
   at `Def(C') = 0`, because the two admissible cardinalities over
   `Bool^{[1]}` give defects `0` and `ln 2 > (1/2) ln 2`.  The witness below
   moves to `ℓ = 2`, `p = 4` and pins a child carrier of defect exactly
   `ln 2 > 0` that satisfies the same projection bound, so the **bound**
   admits a strictly positive child defect at that instance.
5. **Slack sufficient condition.**  `entry_gate_lambda_window` checks that
   Aux 15's sufficient condition `λ ≤ 17/1000` is neither vacuous nor loose:
   the gate holds at `17/1000`, **fails** at `18/1000`, and **fails** at
   `λ = -ln(1 - δ)` for the globally fixed `δ = 1/10`, so the deletion
   tolerance `δ_U` is strictly below `δ` and the two frozen constants are not
   interchangeable.

What is **not** claimed: no inhabitant of the premise bundle of
`defectInduction` is exhibited anywhere in this module, and none can be until
Stages 1--4 land in Lean.  `eq:direct-input` clause one and the ladder output
`eq:direct-two-copy` are construction outputs for the pinned `W`, carried as
explicit named hypotheses exactly as GAP-EXPOSED items 3--4 of the module
header record.  Every other premise is proved outright. -/

namespace EthInapproximability.ParameterizedNP.DefectInduction

open NPCC
open Workspace.Types.Interlace
open Workspace.Types.CommComplexity
open EthInapproximability.ParameterizedNP.InheritedContracts

/-- The pinned Boolean matrix used by every witness: the `2 x 2` AND game. -/
def andPair : Bool → Bool → Bool := fun a b => a && b

/-! ## The punctured column carrier

`Y^{[k]}` with one tuple removed.  It is a proper, nonempty subset for every
`k ≥ 1`, so it has strictly positive defect, and its defect is bounded by
`1/(2^k - 1)`, which is what lets it sit inside a small defect budget. -/

/-- `K = Bool^{[k]} \ {0}`: the full column carrier with the all-`false` tuple
removed. -/
def puncturedColumns (k : ℕ) : Finset (Fin k → Bool) :=
  Finset.univ.erase (fun _ => false)

lemma puncturedColumns_card (k : ℕ) :
    (puncturedColumns k).card = 2 ^ k - 1 := by
  classical
  unfold puncturedColumns
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fun]
  simp

lemma puncturedColumns_nonempty (k : ℕ) (hk : 1 ≤ k) :
    (puncturedColumns k).Nonempty := by
  refine Finset.card_pos.mp ?_
  rw [puncturedColumns_card]
  have : (2 : ℕ) ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  omega

lemma puncturedColumns_ne_univ (k : ℕ) :
    puncturedColumns k ≠ (Finset.univ : Finset (Fin k → Bool)) := by
  intro h
  have hc : (puncturedColumns k).card =
      (Finset.univ : Finset (Fin k → Bool)).card := by rw [h]
  have hone : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_two_pow
  rw [puncturedColumns_card, Finset.card_univ, Fintype.card_fun] at hc
  simp only [Fintype.card_fin, Fintype.card_bool] at hc
  omega

/-- The punctured carrier's defect is the closed form `ln (2^k / (2^k - 1))`. -/
lemma puncturedColumns_defect (k : ℕ) :
    columnDefect (puncturedColumns k) =
      Real.log ((2 : ℝ) ^ k / ((2 : ℝ) ^ k - 1)) := by
  have hone : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
  have hcast : ((2 ^ k - 1 : ℕ) : ℝ) = (2 : ℝ) ^ k - 1 := by
    push_cast [Nat.cast_sub hone]
    ring
  have hY : ((Fintype.card Bool : ℝ)) = 2 := by simp
  unfold columnDefect
  rw [puncturedColumns_card, hcast, hY]

/-- **Strictly positive defect.**  The punctured carrier is a proper nonempty
subset, so its defect is `> 0`. -/
lemma puncturedColumns_defect_pos (k : ℕ) (hk : 1 ≤ k) :
    0 < columnDefect (puncturedColumns k) := by
  have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ k := by
    calc (2 : ℝ) = (2 : ℝ) ^ 1 := by norm_num
      _ ≤ (2 : ℝ) ^ k := by
          apply pow_le_pow_right₀ (by norm_num) hk
  rw [puncturedColumns_defect k]
  refine Real.log_pos ?_
  rw [lt_div_iff₀ (by linarith)]
  linarith

/-- **A usable upper bound.**  `Def(punctured k) ≤ 1/(2^k - 1)`, from
`ln x ≤ x - 1`.  This is what places the carrier inside a small defect
budget. -/
lemma puncturedColumns_defect_le (k : ℕ) (hk : 1 ≤ k) :
    columnDefect (puncturedColumns k) ≤ 1 / ((2 : ℝ) ^ k - 1) := by
  have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ k := by
    calc (2 : ℝ) = (2 : ℝ) ^ 1 := by norm_num
      _ ≤ (2 : ℝ) ^ k := by
          apply pow_le_pow_right₀ (by norm_num) hk
  have hden : (0 : ℝ) < (2 : ℝ) ^ k - 1 := by linarith
  rw [puncturedColumns_defect k]
  have hlog := Real.log_le_sub_one_of_pos
    (show (0 : ℝ) < (2 : ℝ) ^ k / ((2 : ℝ) ^ k - 1) by positivity)
  refine le_trans hlog ?_
  rw [div_sub_one (ne_of_gt hden)]
  have : (2 : ℝ) ^ k - ((2 : ℝ) ^ k - 1) = 1 := by ring
  rw [this]

/-! ## The generic punctured column carrier

The same carrier over an **arbitrary** finite `Y`: `Y^{[k]}` with one tuple
removed.  The `Bool` battery above is its `Y = Bool`, `c₀ = 0` instance
(`puncturedColumns_eq_erasedColumns`), so no quantity is defined twice.  The
generic form is what the firing witness needs, because every finite pinning of
the row type at two elements is refutable — see `nearFull_refuted_of_two_rows`
— and at `|Y| = 2` the same one-bit argument applies to Bob's side. -/

/-- `K = Y^{[k]} \ {c₀}`: the full column carrier with one tuple removed. -/
def erasedColumns {Y : Type*} [Fintype Y] [DecidableEq Y] {k : ℕ}
    (c₀ : Fin k → Y) : Finset (Fin k → Y) :=
  Finset.univ.erase c₀

/-- The `Bool` carrier of the witnesses above is the generic one at
`c₀ = 0`. -/
lemma puncturedColumns_eq_erasedColumns (k : ℕ) :
    puncturedColumns k = erasedColumns (fun _ : Fin k => false) := by
  classical
  ext c
  simp [puncturedColumns, erasedColumns]

lemma erasedColumns_card {Y : Type*} [Fintype Y] [DecidableEq Y] {k : ℕ}
    (c₀ : Fin k → Y) :
    (erasedColumns c₀).card = Fintype.card Y ^ k - 1 := by
  classical
  unfold erasedColumns
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fun]
  simp

lemma erasedColumns_nonempty {Y : Type*} [Fintype Y] [DecidableEq Y] {k : ℕ}
    (c₀ : Fin k → Y) (hk : 2 ≤ Fintype.card Y ^ k) :
    (erasedColumns c₀).Nonempty := by
  refine Finset.card_pos.mp ?_
  rw [erasedColumns_card]
  omega

/-- The generic punctured carrier's defect is the closed form
`ln (n^k / (n^k - 1))` with `n = |Y|`. -/
lemma erasedColumns_defect {Y : Type*} [Fintype Y] [DecidableEq Y] {k : ℕ}
    (c₀ : Fin k → Y) (hk : 2 ≤ Fintype.card Y ^ k) :
    columnDefect (erasedColumns c₀) =
      Real.log ((Fintype.card Y : ℝ) ^ k
        / ((Fintype.card Y : ℝ) ^ k - 1)) := by
  have hone : (1 : ℕ) ≤ Fintype.card Y ^ k := by omega
  have hcast : ((Fintype.card Y ^ k - 1 : ℕ) : ℝ)
      = (Fintype.card Y : ℝ) ^ k - 1 := by
    push_cast [Nat.cast_sub hone]
    ring
  unfold columnDefect
  rw [erasedColumns_card, hcast]

/-- **Strictly positive defect.**  Removing one tuple leaves a proper nonempty
subset, so the defect is `> 0`. -/
lemma erasedColumns_defect_pos {Y : Type*} [Fintype Y] [DecidableEq Y] {k : ℕ}
    (c₀ : Fin k → Y) (hk : 2 ≤ Fintype.card Y ^ k) :
    0 < columnDefect (erasedColumns c₀) := by
  have hN : (2 : ℝ) ≤ (Fintype.card Y : ℝ) ^ k := by exact_mod_cast hk
  rw [erasedColumns_defect c₀ hk]
  refine Real.log_pos ?_
  rw [lt_div_iff₀ (by linarith)]
  linarith

/-- **A usable upper bound.**  `Def(erased) ≤ 1/(n^k - 1)`, from
`ln x ≤ x - 1`. -/
lemma erasedColumns_defect_le {Y : Type*} [Fintype Y] [DecidableEq Y] {k : ℕ}
    (c₀ : Fin k → Y) (hk : 2 ≤ Fintype.card Y ^ k) :
    columnDefect (erasedColumns c₀) ≤ 1 / ((Fintype.card Y : ℝ) ^ k - 1) := by
  have hN : (2 : ℝ) ≤ (Fintype.card Y : ℝ) ^ k := by exact_mod_cast hk
  have hden : (0 : ℝ) < (Fintype.card Y : ℝ) ^ k - 1 := by linarith
  rw [erasedColumns_defect c₀ hk]
  have hlog := Real.log_le_sub_one_of_pos
    (show (0 : ℝ) < (Fintype.card Y : ℝ) ^ k / ((Fintype.card Y : ℝ) ^ k - 1) by
      positivity)
  refine le_trans hlog ?_
  rw [div_sub_one (ne_of_gt hden)]
  have h : (Fintype.card Y : ℝ) ^ k - ((Fintype.card Y : ℝ) ^ k - 1) = 1 := by
    ring
  rw [h]

/-! ## Witness 1: the numeric guard bundle is legal and non-contradictory -/

/-- **Aux 18 (non-vacuity, guards).**  Every purely numeric guard of
`defectInduction` holds simultaneously at
`a = 2`, `p = 10`, `θ = 1/4`, `y = 3/5`, `λ = 1/100`, `C_W = 3`,
`X = Y = Bool`.  The two guards that could be jointly contradictory are
**tight** here: `θ = 1/4` saturates `4θ ≤ 1` and `2^2 θ = 1` saturates the
level restriction.  The entry gate is *derived* from `λ ≤ 17/1000`, not
assumed. -/
theorem defectInduction_guards_legal :
    (2 : ℕ) ^ 2 < 2 * 10 ∧
    (2 : ℝ) ^ 2 * (1 / 4) ≤ 1 ∧
    (0 : ℝ) < 1 / 4 ∧ (1 / 4 : ℝ) ≤ 1 / 4 ∧
    (0 : ℝ) < 3 / 5 ∧ (3 / 5 : ℝ) ≤ 1 ∧
    (0 : ℝ) < 1 / 100 ∧
    1 ≤ Fintype.card Bool ∧ 3 ≤ 3 ∧
    3 * (1 / 100 : ℝ) + (7 / 5) * Real.log 2 ≤ -2 * Real.log (3 / 5) ∧
    rowFloor (Fintype.card Bool) (1 / 4 : ℝ) 2 = 2 := by
  refine ⟨by norm_num, by norm_num, by norm_num, le_rfl, by norm_num,
    by norm_num, by norm_num, by simp, le_rfl,
    entry_gate_of_lambda_small (by norm_num) (by norm_num), ?_⟩
  have hY : ((Fintype.card Bool : ℝ)) = 2 := by simp
  unfold rowFloor
  rw [hY]
  norm_num

/-! ## Witness 2: the state premises are met by a nondegenerate carrier pair -/

/-- **Aux 19 (non-vacuity, state).**  At the legal parameters of Aux 18 the two
state premises of `defectInduction` are met by an explicit carrier pair whose
column carrier is a **proper** nonempty subset of `Bool^{[10]}` with
**strictly positive** defect.  So the premises are not satisfiable only at the
full carrier, whose defect is `0` by `columnDefect_univ`.

Note the budget is genuinely consumed: `c_2(10) λ = 8/100`, and the carrier's
defect is a strictly positive real below it. -/
theorem defectInduction_state_nondegenerate :
    IsEquipartitionedGE (Finset.univ : Finset (Fin 10 × Bool))
      (Finset.univ : Finset (Fin 10)) (rowFloor (Fintype.card Bool) (1 / 4) 2) ∧
    (puncturedColumns 10).Nonempty ∧
    puncturedColumns 10 ≠ (Finset.univ : Finset (Fin 10 → Bool)) ∧
    0 < columnDefect (puncturedColumns 10) ∧
    columnDefect (puncturedColumns 10) ≤ excessCopies 2 10 * (1 / 100) := by
  have hfloor : rowFloor (Fintype.card Bool) (1 / 4 : ℝ) 2 = 2 := by
    have hY : ((Fintype.card Bool : ℝ)) = 2 := by simp
    unfold rowFloor
    rw [hY]
    norm_num
  refine ⟨?_, puncturedColumns_nonempty 10 (by norm_num),
    puncturedColumns_ne_univ 10, puncturedColumns_defect_pos 10 (by norm_num),
    ?_⟩
  · rw [hfloor]
    exact univ_rows_equipartitionedGE 2 (by simp)
  · have hbudget : excessCopies 2 10 * (1 / 100 : ℝ) = 8 / 100 := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, excessCopies_succ]
      norm_num
    rw [hbudget]
    refine le_trans (puncturedColumns_defect_le 10 (by norm_num)) ?_
    norm_num

/-! ## Witness 3: the near-full clause refutes every two-row pinning, so the
firing witness is stated abstractly

The pinned-matrix form of the firing witness would be a vacuously true
implication.  The two lemmas below prove that, and the firing witness that
follows avoids it by quantifying over `X`, `Y`, `W`, and `C_W`. -/

open Workspace.Types.Protocol in
/-- **Aux 20 (the one-row protocol).**  A subgame whose row carrier is a single
row is computed by one Bob bit: Bob announces the value of that row at his own
column.  General statement — arbitrary game, arbitrary row, arbitrary column
carrier — and the mechanism behind the refutation below. -/
lemma D_singletonRow_le_one {A B : Type*}
    (f : A → B → Bool) (r : A) (C : Finset B) :
    D (subgame f ({r} : Finset A) C) ≤ 1 := by
  refine Nat.sInf_le ?_
  refine ⟨Protocol.bNode (fun c : {c // c ∈ C} => f r c.val)
      (Protocol.leaf false) (Protocol.leaf true), ?_, ?_⟩
  · simp [Protocol.cost]
  · intro a c
    have ha : a.val = r := Finset.mem_singleton.mp a.property
    cases h : f r c.val <;>
      simp [Protocol.eval, subgame, ha, h]

/-- **Aux 21 (the `|X| = 2` refutation).**  At two rows the near-full clause of
`eq:direct-input` (`10-direct-bridge.tex:9`) is **false** for every matrix and
every `C_W ≥ 3`, at every legal row threshold `θ ≤ 1/2` and every column
density `z ≤ 1`.

Reason: the `p = 1` bracket family of `def:bracket` asks for
`⌈|X| θ⌉ = ⌈2θ⌉ = 1` row in the single active copy, so the pair
`({(0, x₀)}, Y^{[1]})` is a member; a one-row subgame is computed by one Bob
bit, so the family minimum is at most `1 < 3 ≤ C_W`.

This is the lemma that forbids re-pinning the firing witness at a two-row
matrix.  It is a statement about the hypothesis alone, not about the paper's
construction: the frozen section's `W` has `|Rows(W)|` growing with the
Stage--4 parameters, and nothing here bounds `Dfamily` for those.

`hθ0` is carried only for paper legality (`θ` is a row threshold, line 82); the
refutation itself needs just `θ ≤ 1/2`, so the statement is not weakened by
dropping it. -/
theorem nearFull_refuted_of_two_rows {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (CW : ℕ) (θ z : ℝ)
    (hX : Fintype.card X = 2) (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 2) (hz : z ≤ 1)
    (hCW : 3 ≤ CW) :
    ¬ CW ≤ Dfamily (interlaceFun W 1) (bracketGE X Y 1 θ z) := by
  classical
  have _ := hθ0
  obtain ⟨x₀⟩ : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have hrows : IsEquipartitionedGE ({((0 : Fin 1), x₀)} : Finset (Fin 1 × X))
      (Finset.univ : Finset (Fin 1)) ⌈(Fintype.card X : ℝ) * θ⌉₊ := by
    intro q _
    have hq : q = 0 := Subsingleton.elim _ _
    have hceil : ⌈(Fintype.card X : ℝ) * θ⌉₊ ≤ 1 := by
      refine Nat.ceil_le.mpr ?_
      rw [hX]
      push_cast
      linarith
    refine le_trans hceil ?_
    subst hq
    simp [Finset.filter_singleton]
  have hcols : ⌈((Fintype.card Y : ℝ) ^ 1) * z⌉₊
      ≤ (Finset.univ : Finset (Fin 1 → Y)).card := by
    have hcard : (Finset.univ : Finset (Fin 1 → Y)).card = Fintype.card Y := by
      simp [Finset.card_univ]
    have hpos : (0 : ℝ) ≤ (Fintype.card Y : ℝ) := by positivity
    rw [hcard]
    refine Nat.ceil_le.mpr ?_
    have : ((Fintype.card Y : ℝ) ^ 1) * z ≤ ((Fintype.card Y : ℝ) ^ 1) * 1 := by
      have h1 : (0 : ℝ) ≤ (Fintype.card Y : ℝ) ^ 1 := by positivity
      nlinarith
    simpa using this
  have hmem : ((({((0 : Fin 1), x₀)} : Finset (Fin 1 × X)),
      (Finset.univ : Finset (Fin 1 → Y))) :
      Finset (Fin 1 × X) × Finset (Fin 1 → Y)) ∈ bracketGE X Y 1 θ z :=
    ⟨hrows, hcols⟩
  have hfam : Dfamily (interlaceFun W 1) (bracketGE X Y 1 θ z)
      ≤ D (subgame (interlaceFun W 1) ({((0 : Fin 1), x₀)} : Finset (Fin 1 × X))
        (Finset.univ : Finset (Fin 1 → Y))) :=
    Nat.sInf_le ⟨_, hmem, rfl⟩
  have hone : D (subgame (interlaceFun W 1)
      ({((0 : Fin 1), x₀)} : Finset (Fin 1 × X))
      (Finset.univ : Finset (Fin 1 → Y))) ≤ 1 :=
    D_singletonRow_le_one _ _ _
  omega

/-- **Aux 22 (the refuted instance itself).**  The `2 x 2` AND game at the
pinned numeric parameters cannot satisfy the near-full clause at `C_W = 3`.
This is the exact hypothesis that a pinned-matrix firing witness would have
assumed, recorded here as **false** so that no later lane re-pins it. -/
theorem andPair_nearFull_refuted :
    ¬ (3 : ℕ) ≤ Dfamily (interlaceFun andPair 1)
      (bracketGE Bool Bool 1 (1 / 4) (Real.exp (-(1 / 100)))) := by
  refine nearFull_refuted_of_two_rows andPair 3 (1 / 4)
    (Real.exp (-(1 / 100))) (by simp) (by norm_num) (by norm_num) ?_ le_rfl
  exact Real.exp_le_one_iff.mpr (by norm_num)

/-- **Aux 23 (non-vacuity, abstract firing).**  `defectInduction` fires at
universally quantified `X`, `Y`, `W`, `C_W` with every numeric parameter pinned
to the legal assignment of Aux 18 — `a = 2`, `p = 10`, `θ = 1/4`, `y = 3/5`,
`λ = 1/100` — and with the carriers of Aux 19 in their generic form: all rows
of the ten-fold interlace, and `Y^{[10]}` with one tuple removed.

Everything except the two cited construction inputs is discharged here: the
copy guard, the level restriction, the row-threshold legality, the entry gate
(*derived* from `λ ≤ 17/1000`), the row condition (`A_2 = ⌈|X| · 4 · (1/4)⌉ =
|X|`, met by the full row carrier), nonemptiness of the column carrier, and the
defect condition (`Def ≤ 1/(|Y|^10 - 1) ≤ 1/1023 < 8/100 = c_2(10) λ`).  The
conclusion also records the delivered bound `5 ≤ D(...)` from `3 ≤ C_W`, and
the strict positivity of the carrier's defect, so the carrier is a **proper**
subset and the conclusion is not the free bound at `C_W + a = 0`.

The two remaining assumptions, `hNear` (`eq:direct-input` clause one at density
`e^{-λ}`) and `hTwoCopy` (the ladder output `eq:direct-two-copy`), are
construction outputs of Sections 8--9 and are **not** exhibited: this module
proves a conditional, not the existence of an instance.  What the abstraction
buys is that they are not self-refuting, which the previous pinned form was —
see `nearFull_refuted_of_two_rows` and `andPair_nearFull_refuted`. -/
theorem defectInduction_fires {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq Y] (W : X → Y → Bool) (CW : ℕ) (c₀ : Fin 10 → Y)
    (hX : 1 ≤ Fintype.card X) (hY : 2 ≤ Fintype.card Y) (hCW : 3 ≤ CW)
    (hNear : CW ≤ Dfamily (interlaceFun W 1)
      (bracketGE X Y 1 (1 / 4) (Real.exp (-(1 / 100)))))
    (hTwoCopy : CW ≤ LambdaGE W 2 (2 * (1 / 4)) ((3 / 5 : ℝ) ^ 2)) :
    CW + 2 ≤ D (subgame (interlaceFun W 10)
        (Finset.univ : Finset (Fin 10 × X)) (erasedColumns c₀)) ∧
      5 ≤ D (subgame (interlaceFun W 10)
        (Finset.univ : Finset (Fin 10 × X)) (erasedColumns c₀)) ∧
      0 < columnDefect (erasedColumns c₀) := by
  have hpow : (1024 : ℕ) ≤ Fintype.card Y ^ 10 := by
    calc (1024 : ℕ) = 2 ^ 10 := by norm_num
      _ ≤ Fintype.card Y ^ 10 := Nat.pow_le_pow_left hY 10
  have hk : (2 : ℕ) ≤ Fintype.card Y ^ 10 := le_trans (by norm_num) hpow
  have hfloor : rowFloor (Fintype.card X) (1 / 4 : ℝ) 2 = Fintype.card X := by
    unfold rowFloor
    rw [show ((Fintype.card X : ℝ) * (2 : ℝ) ^ 2 * (1 / 4))
        = ((Fintype.card X : ℕ) : ℝ) by ring]
    exact Nat.ceil_natCast _
  have hrows : IsEquipartitionedGE (Finset.univ : Finset (Fin 10 × X))
      (Finset.univ : Finset (Fin 10))
      (rowFloor (Fintype.card X) (1 / 4 : ℝ) 2) := by
    rw [hfloor]
    exact univ_rows_equipartitionedGE (Fintype.card X) le_rfl
  have hKne : (erasedColumns c₀).Nonempty := erasedColumns_nonempty c₀ hk
  have hdefpos : 0 < columnDefect (erasedColumns c₀) :=
    erasedColumns_defect_pos c₀ hk
  have hbudget : excessCopies 2 10 * (1 / 100 : ℝ) = 8 / 100 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, excessCopies_succ]
    norm_num
  have hdefect : columnDefect (erasedColumns c₀)
      ≤ excessCopies 2 10 * (1 / 100 : ℝ) := by
    rw [hbudget]
    refine le_trans (erasedColumns_defect_le c₀ hk) ?_
    have hN : (1024 : ℝ) ≤ (Fintype.card Y : ℝ) ^ 10 := by exact_mod_cast hpow
    rw [div_le_iff₀ (by linarith)]
    linarith
  have h := defectInduction W CW 10 2 (1 / 4) (3 / 5) (1 / 100)
    (by norm_num) (by norm_num) (by norm_num) le_rfl (by norm_num) (by norm_num)
    (by norm_num) hX (by omega) hCW
    (entry_gate_of_lambda_small (by norm_num) (by norm_num))
    hNear hTwoCopy (Finset.univ : Finset (Fin 10 × X)) (erasedColumns c₀)
    hKne hrows hdefect
  exact ⟨h, by omega, hdefpos⟩

/-! ## Witness 4: the now-due `Def(C') > 0` projection instance -/

/-- The pinned parent column carrier on four copies:
`{c ∈ Bool^{[4]} : c 0 = false ∧ c 1 = false}`, of size `4` out of `16`, hence
defect `ln 4 = 2 ln 2`. -/
def deepColumns : Finset (Fin 4 → Bool) :=
  Finset.univ.filter (fun c => c 0 = false ∧ c 1 = false)

/-- The pinned child column carrier on two copies:
`{c ∈ Bool^{[2]} : c 0 = false}`, of size `2` out of `4`, hence defect
`ln 2 > 0`. -/
def midColumns : Finset (Fin 2 → Bool) :=
  Finset.univ.filter (fun c => c 0 = false)

lemma deepColumns_card : deepColumns.card = 4 := by decide

lemma midColumns_card : midColumns.card = 2 := by decide

lemma deepColumns_nonempty : deepColumns.Nonempty :=
  Finset.card_pos.mp (by rw [deepColumns_card]; norm_num)

lemma deepColumns_defect : columnDefect deepColumns = 2 * Real.log 2 := by
  have hY : ((Fintype.card Bool : ℝ)) = 2 := by simp
  have hc : ((deepColumns.card : ℕ) : ℝ) = 4 := by
    rw [deepColumns_card]; norm_num
  unfold columnDefect
  rw [hY, hc, show ((2 : ℝ) ^ (4 : ℕ)) / 4 = 2 ^ (2 : ℕ) by norm_num,
    Real.log_pow]
  norm_num

lemma midColumns_defect : columnDefect midColumns = Real.log 2 := by
  have hY : ((Fintype.card Bool : ℝ)) = 2 := by simp
  have hc : ((midColumns.card : ℕ) : ℝ) = 2 := by
    rw [midColumns_card]; norm_num
  unfold columnDefect
  rw [hY, hc, show ((2 : ℝ) ^ (2 : ℕ)) / 2 = 2 by norm_num]

/-- **Aux 24 (non-vacuity, the projection bound admits a positive child
defect).**  The now-due `Def(C') > 0` instance, stated as what is provable.

At `|Y| = 2`, `ℓ = 1`, `p = 2` the projection bound `Def(C') ≤ (1/2) Def(C)`
of `INHERIT-001` is only satisfiable at `Def(C') = 0`, because over `Bool^{[1]}`
the two admissible cardinalities give defects `0` and `ln 2`, and
`ln 2 > (1/2) ln 2`.  Moving to `ℓ = 2`, `p = 4` repairs that: the pinned
parent `deepColumns` has defect `2 ln 2`, the bound reads `Def(C') ≤ ln 2`, and
the pinned child `midColumns` meets it with defect exactly `ln 2 > 0`.

**What this does and does not say.**  The provable content is that the *bound*
admits a strictly-positive-defect child at this instance, and — separately —
that `defectProjection` fires legally at the same parent and returns nonempty
carriers.  It is **not** claimed that the carrier the contract actually
returns has positive defect: `defectProjection` is existential, and the
underlying `memberMaxProjection` may legitimately return the full child
carrier, whose defect is `0` (`columnDefect_univ`).  The two groups of
conjuncts sit beside each other; the positive-defect child is not exhibited
inside the existential. -/
theorem projectionBound_admits_positive_child_defect :
    0 < columnDefect midColumns ∧
    columnDefect midColumns ≤ ((2 : ℝ) / (4 : ℝ)) * columnDefect deepColumns ∧
    0 < columnDefect deepColumns ∧
    ∃ (R' : Finset (Fin 2 × Bool)) (C' : Finset (Fin 2 → Bool)),
      IsEquipartitionedGE R' (Finset.univ : Finset (Fin 2)) 2 ∧
      R'.Nonempty ∧ C'.Nonempty ∧
      columnDefect C' ≤ ((2 : ℝ) / (4 : ℝ)) * columnDefect deepColumns ∧
      D (subgame (interlaceFun andPair 2) R' C') ≤
        D (subgame (interlaceFun andPair 4)
            (Finset.univ : Finset (Fin 4 × Bool)) deepColumns) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨by rw [midColumns_defect]; exact hlog2, ?_, ?_, ?_⟩
  · rw [midColumns_defect, deepColumns_defect]
    linarith
  · rw [deepColumns_defect]; linarith
  · obtain ⟨R', C', hR', hC'ne, hdef, hD⟩ :=
      defectProjection andPair 4 2 2 (by norm_num) (by norm_num) (by simp)
        (by simp) (Finset.univ : Finset (Fin 4 × Bool)) deepColumns
        (univ_rows_equipartitionedGE 2 (by simp)) deepColumns_nonempty
    exact ⟨R', C', hR', nonempty_of_equipartitionedGE (by norm_num)
      ⟨0, Finset.mem_univ _⟩ hR', hC'ne, by simpa using hdef, hD⟩

/-! ## Witness 5 (the row-side companion of Witness 2): the row premise is met
by a **proper** row carrier

Aux 19 pins `θ = 1/4`, where the two numeric guards `θ ≤ 1/4` and `2^a θ ≤ 1`
are simultaneously **tight** at `a = 2`.  That tightness has a price on the row
side.  There `A_2 = ⌈m · 2^2 · (1/4)⌉ = m`, and unfolding
`IsEquipartitionedGE R univ m` over `Fin p × X` says every fibre of `R` has at
least `m = |X|` elements; since each fibre injects into `X`, every fibre is all
of `X` and `R = Finset.univ`.  So at the tight assignment the row premise is
satisfiable *only* at the full row carrier and the row floor is never exercised
on a proper restriction — the row-side analogue of the column degeneracy that
`columnDefect_univ` rules out.

The companion below removes that degeneracy without touching Aux 19.  It keeps
`a = 2`, `p = 10`, `λ = 1/100` and the same column carrier, and moves only the
row threshold to `θ = 1/8`, which is still legal: `0 < 1/8`, `1/8 ≤ 1/4`, and
`2^2 · (1/8) = 1/2 ≤ 1`.  There `A_2 = ⌈2 · 4 · (1/8)⌉ = 1`, so a row carrier
keeping one row per active copy satisfies the row premise, and
`R ≠ Finset.univ` is carried as an **explicit conjunct**.  The two witnesses are
complementary and both are kept. -/

/-- **Aux 25 (why Witness 2's row carrier has to be `Finset.univ`).**  General
statement, no pinned parameters: a row set that is `(univ, |X|)`-equipartitioned
over a finite row type `X` is the **full** row carrier.  Each fibre injects into
`X` by its second component, so a fibre of size at least `|X|` is all of `X`.

Anchor: the row premise of `lem:defect-induction` is `A_a = ⌈m 2^a θ⌉`
(`10-direct-bridge.tex:82`) read through `def:equipartition-ge`.  This lemma
states a property of that interface, not a new paper claim, so it is assigned no
reader item of its own: `B-bridge-details.tex` line 41 stays with `rowFloor`.

It is the row-side analogue of `columnDefect_univ`, and it is what makes
Witness 5 necessary rather than decorative: `rowFloor |X| (1/4) 2 = |X|`, so at
the tight assignment of Witness 2 the row premise of `defectInduction` is
satisfiable *only* at `R = Finset.univ`. -/
lemma eq_univ_of_equipartitionedGE_card {ι X : Type*} [DecidableEq ι]
    [Fintype ι] [Fintype X] {R : Finset (ι × X)}
    (h : IsEquipartitionedGE R (Finset.univ : Finset ι) (Fintype.card X)) :
    R = (Finset.univ : Finset (ι × X)) := by
  classical
  ext r
  simp only [Finset.mem_univ, iff_true]
  obtain ⟨q, x⟩ := r
  by_contra hnot
  set S := R.filter (fun p => p.1 = q) with hS
  have hinj : Set.InjOn Prod.snd (S : Set (ι × X)) := by
    intro a ha b hb hab
    have ha1 : a.1 = q := (Finset.mem_filter.mp ha).2
    have hb1 : b.1 = q := (Finset.mem_filter.mp hb).2
    exact Prod.ext (ha1.trans hb1.symm) hab
  have hsub : S.image Prod.snd ⊆ (Finset.univ : Finset X).erase x := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
    have ha1 : a.1 = q := (Finset.mem_filter.mp ha).2
    have haR : a ∈ R := (Finset.mem_filter.mp ha).1
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    intro heq
    exact hnot (by rwa [show ((q, x) : ι × X) = a from Prod.ext ha1.symm heq.symm])
  have hle : S.card ≤ Fintype.card X - 1 := by
    calc S.card = (S.image Prod.snd).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ ((Finset.univ : Finset X).erase x).card := Finset.card_le_card hsub
      _ = Fintype.card X - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  have hpos : 0 < Fintype.card X := Fintype.card_pos_iff.mpr ⟨x⟩
  have hge : Fintype.card X ≤ S.card := h q (Finset.mem_univ _)
  omega

/-- `R = {(q, false) : q ∈ Fin 10}`, one row per active copy of the ten-fold
interlace: a nonempty **proper** subset of the full row carrier
`Fin 10 × Bool`. -/
def properRows : Finset (Fin 10 × Bool) :=
  Finset.univ.filter (fun r => r.2 = false)

/-- **Aux 26 (properness).**  `properRows` really is a proper subset: it omits
`(0, true)`. -/
lemma properRows_ne_univ :
    properRows ≠ (Finset.univ : Finset (Fin 10 × Bool)) := by
  intro h
  have hmem : ((0 : Fin 10), true) ∈ properRows := by
    rw [h]
    exact Finset.mem_univ _
  simp [properRows] at hmem

/-- **Aux 27 (row premise at floor `1`).**  Every fibre of `properRows` is
nonempty, so it is `(univ, 1)`-equipartitioned.  General in the sense that it
uses only the fibre of `(q, false)`, not any cardinality computation. -/
lemma properRows_equipartitionedGE_one :
    IsEquipartitionedGE properRows (Finset.univ : Finset (Fin 10)) 1 := by
  classical
  intro q _
  have hmem : ((q, false) : Fin 10 × Bool) ∈
      properRows.filter (fun r => r.1 = q) := by
    simp [properRows]
  exact Finset.card_pos.mpr ⟨_, hmem⟩

/-- **Aux 28 (non-vacuity, state with a proper row carrier).**  The companion of
Aux 19 at the non-tight row threshold `θ = 1/8`, with `a = 2`, `p = 10`,
`λ = 1/100` unchanged.

All three numeric row guards of `defectInduction` are re-checked here
(`0 < θ`, `θ ≤ 1/4`, `2^a θ ≤ 1`), the row floor is computed to be `1`, the row
premise is met by `properRows`, and `properRows ≠ Finset.univ` is an explicit
conjunct — so the row premise is **not** satisfiable only at the full row
carrier.  The column half is Aux 19's verbatim: a proper nonempty column
carrier of strictly positive defect strictly inside the budget
`c_2(10) λ = 8/100`.

Anchors: `A_a` (`10-direct-bridge.tex:82`) with the level restriction
`2^a θ ≤ 1` (line 84) and `θ ≤ 1/4` (the legality of `eq:direct-three-copy`,
line 27).  As a witness it is assigned no reader item of its own;
`B-bridge-details.tex` line 41 stays with `rowFloor`.

Like Aux 19 this mentions no `W` and no `C_W`; it is a carrier-level witness,
not an inhabitant of the premise bundle. -/
theorem defectInduction_state_nondegenerate_properRows :
    (0 : ℝ) < 1 / 8 ∧ (1 / 8 : ℝ) ≤ 1 / 4 ∧ (2 : ℝ) ^ 2 * (1 / 8) ≤ 1 ∧
    rowFloor (Fintype.card Bool) (1 / 8 : ℝ) 2 = 1 ∧
    IsEquipartitionedGE properRows (Finset.univ : Finset (Fin 10))
      (rowFloor (Fintype.card Bool) (1 / 8 : ℝ) 2) ∧
    properRows ≠ (Finset.univ : Finset (Fin 10 × Bool)) ∧
    properRows.Nonempty ∧
    (puncturedColumns 10).Nonempty ∧
    puncturedColumns 10 ≠ (Finset.univ : Finset (Fin 10 → Bool)) ∧
    0 < columnDefect (puncturedColumns 10) ∧
    columnDefect (puncturedColumns 10) ≤ excessCopies 2 10 * (1 / 100) := by
  have hfloor : rowFloor (Fintype.card Bool) (1 / 8 : ℝ) 2 = 1 := by
    have hY : ((Fintype.card Bool : ℝ)) = 2 := by simp
    unfold rowFloor
    rw [hY]
    norm_num
  refine ⟨by norm_num, by norm_num, by norm_num, hfloor, ?_,
    properRows_ne_univ,
    nonempty_of_equipartitionedGE le_rfl ⟨0, Finset.mem_univ _⟩
      properRows_equipartitionedGE_one,
    puncturedColumns_nonempty 10 (by norm_num),
    puncturedColumns_ne_univ 10, puncturedColumns_defect_pos 10 (by norm_num),
    ?_⟩
  · rw [hfloor]
    exact properRows_equipartitionedGE_one
  · have hbudget : excessCopies 2 10 * (1 / 100 : ℝ) = 8 / 100 := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, excessCopies_succ]
      norm_num
    rw [hbudget]
    refine le_trans (puncturedColumns_defect_le 10 (by norm_num)) ?_
    norm_num

/-! ## Witness 6: the entry gate is a real constraint on `λ`, and `δ_U ≠ δ`

`entry_gate_of_lambda_small` (Aux 15) discharges the second inequality of
`eq:direct-entry-gates` from the *sufficient* condition `λ ≤ 17/1000`.  A
sufficient condition can hide a defect in two ways: it can be unsatisfiable, or
it can be so slack that it never touches the gate.  The observation below
excludes both, and records one substantive reading check on the frozen section.

At the globally fixed `y = 1/2 + δ = 3/5` (`10-direct-bridge.tex:36-37`) the
gate reads `3λ ≤ -2 ln(3/5) - (7/5) ln 2`, whose right-hand side is
`(1/5) ln (5^10 / (3^10 · 2^7))`.  It holds at `λ = 17/1000` and fails at
`λ = 18/1000`, so the exact threshold lies in `(17/1000, 18/1000)` and Aux 15 is
within `1/1000` of it.

The third conjunct is the reading check.  `δ = 1/10` and the deletion tolerance
`δ_U` are **different** named constants of the frozen section (`δ` fixes `y` at
line 36; `δ_U` is the free tolerance of `eq:direct-input`, tied to `λ` by
`λ = -ln(1 - δ_U)` at line 43).  Substituting `δ_U := δ` makes the entry gate
**false**, so the section's `δ_U` is strictly smaller than `δ`; a transcription
that conflated the two would typecheck and prove nothing. -/

/-- **Aux 29 (the entry gate's `λ` window).**  At the globally fixed `y = 3/5`
(`10-direct-bridge.tex:37`): the second inequality of `eq:direct-entry-gates`
(line 55) holds at `λ = 17/1000`, fails at `λ = 18/1000`, and fails at
`λ = -ln(1 - δ)` for the globally fixed `δ = 1/10` (line 37), with
`λ = -ln(1 - δ_U)` at line 43 and `0 < δ_U < 1` at line 38.

No reader item is assigned here: this is a numeric check on the gate that
`entry_gate_of_lambda_small` already discharges, not a transcription of a
further reader statement, and `04-bridge.tex` `thm:near-to-robust` stays
assigned to `INHERIT-001`. -/
theorem entry_gate_lambda_window :
    3 * (17 / 1000 : ℝ) + (7 / 5) * Real.log 2 ≤ -2 * Real.log (3 / 5) ∧
    ¬ (3 * (18 / 1000 : ℝ) + (7 / 5) * Real.log 2 ≤ -2 * Real.log (3 / 5)) ∧
    ¬ (3 * (-Real.log (1 - 1 / 10 : ℝ)) + (7 / 5) * Real.log 2
        ≤ -2 * Real.log (3 / 5)) := by
  -- `-2 ln(3/5) - (7/5) ln 2 = (1/5) ln (5^10 / (3^10 · 2^7))`.
  have hlog35 : Real.log (3 / 5 : ℝ) = Real.log 3 - Real.log 5 :=
    Real.log_div (by norm_num) (by norm_num)
  have e5 : Real.log (9765625 : ℝ) = 10 * Real.log 5 := by
    rw [show (9765625 : ℝ) = 5 ^ (10 : ℕ) by norm_num, Real.log_pow]
    push_cast
    ring
  have e37 : Real.log (7558272 : ℝ) = 10 * Real.log 3 + 7 * Real.log 2 := by
    rw [show (7558272 : ℝ) = 3 ^ (10 : ℕ) * 2 ^ (7 : ℕ) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hnum : Real.log ((9765625 : ℝ) / 7558272)
      = 10 * Real.log 5 - (10 * Real.log 3 + 7 * Real.log 2) := by
    rw [Real.log_div (by norm_num) (by norm_num), e5, e37]
  -- `5^10 / (3^10 · 2^7) < e^{27/100}`, via `e^{9/100} ≥ 109/100` cubed.
  have hexpPos : (0 : ℝ) < Real.exp (9 / 100) := Real.exp_pos _
  have h9 : (109 / 100 : ℝ) ≤ Real.exp (9 / 100) := by
    have := Real.add_one_le_exp (9 / 100 : ℝ)
    linarith
  have hsplit : Real.exp (27 / 100 : ℝ)
      = Real.exp (9 / 100) * Real.exp (9 / 100) * Real.exp (9 / 100) := by
    rw [← Real.exp_add, ← Real.exp_add]
    norm_num
  have hexp : ((9765625 : ℝ) / 7558272) < Real.exp (27 / 100) := by
    have hsq : (109 / 100 : ℝ) * (109 / 100)
        ≤ Real.exp (9 / 100) * Real.exp (9 / 100) := by nlinarith
    have hcube : (109 / 100 : ℝ) * (109 / 100) * (109 / 100)
        ≤ Real.exp (9 / 100) * Real.exp (9 / 100) * Real.exp (9 / 100) := by
      nlinarith
    rw [hsplit]
    nlinarith
  have hlt : Real.log ((9765625 : ℝ) / 7558272) < 27 / 100 := by
    have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 9765625 / 7558272) hexp
    rwa [Real.log_exp] at h
  have hkey : -2 * Real.log (3 / 5 : ℝ) < 54 / 1000 + (7 / 5) * Real.log 2 := by
    rw [hlog35]
    linarith
  refine ⟨entry_gate_of_lambda_small (by norm_num) le_rfl, ?_, ?_⟩
  · intro h
    linarith
  · intro h
    have hd : Real.log (1 - 1 / 10 : ℝ) ≤ -(1 / 10) := by
      have := Real.log_le_sub_one_of_pos
        (show (0 : ℝ) < 1 - 1 / 10 by norm_num)
      linarith
    linarith

/-- **Aux 30 (the *first* entry gate's `θ` ceiling).**  The companion half of
`eq:direct-entry-gates` (`10-direct-bridge.tex:53`) is `4 Q_0 θ ≤ δ`, and
`thm:direct-robustification` fixes `δ = 1/10` (line 37) and
`Q_0 = max{8 b/(δ δ_U), 8/δ, 16} ≥ 16` (lines 47--49).  Every row threshold the
route itself supplies therefore satisfies `θ ≤ 1/640`.

This is recorded because it locates the degeneracy Witness 5 repairs.  The
tightness of `θ = 1/4` in Witness 2 is an artefact of that *pinning*, not a
property of the frozen route.  Precisely — and this is the only claim made
here, `A_a = m` does still occur at any level saturating `2^a θ = 1` — at a
level with `2^a θ ≤ 1/2` one has `A_a = ⌈m 2^a θ⌉ ≤ ⌈m/2⌉ < m` for `m ≥ 2`, so
there the row floor is met by proper row carriers.  Witness 2 pins `θ = 1/4` at
the level `a = 2`, which is exactly where `2^a θ = 1` saturates, so its own
level has `A_2 = m`.  With `θ ≤ 1/640` saturation cannot occur below `a = 10`,
so on the route itself the low levels are the unsaturated ones; Witness 5 keeps
`a = 2` and moves only to `θ = 1/8`, where `2^2 θ = 1/2`. -/
lemma routeGate_forces_theta_small {Q₀ θ : ℝ} (hQ : 16 ≤ Q₀) (hθ0 : 0 < θ)
    (hgate : 4 * Q₀ * θ ≤ 1 / 10) : θ ≤ 1 / 640 := by
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Q₀ - 16) (le_of_lt hθ0)]

end EthInapproximability.ParameterizedNP.DefectInduction
