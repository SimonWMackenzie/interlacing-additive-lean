import Mathlib
import NPCC.Defs
import NPCC.Complexity
import NPCC.ComplexityAux
import NPCC.Engine
import EthBridge.Arith
import EthBridge.Defs
import EthBridge.Hypotheses
import EthBridge.Bases

/-! # EthBridge one-bit-down induction (Tranche E2)

Statement-only (`sorry`) signatures for the four E2 obligations from
`eth-obligations.json`, drafted for faithfulness sign-off BEFORE any proving
(source: `eth-docs/REENTRY_ROBUSTIFICATION_BY_DIRECT_DEFECT_ACCOUNTING.md`,
§4 "The Direct Lower Bound", the auxiliary one-bit-down statement (12)→(13)):

* `obdState`             — the note's `(12)` state family (defect budget
                           `c_a(p)·λ + B(p)`, density form);
* `one_bit_down_base`    — `eth:lem-obd-base`  (a = 2 base, via (Three));
* `one_bit_down_alice`   — `eth:lem-obd-alice` (Alice step, a ≥ 3);
* `one_bit_down_bob`     — `eth:lem-obd-bob`   (Bob step,   a ≥ 3);
* `one_bit_down`         — `eth:thm-obd`       (the induction (12)→(13)).

Plus the helper sorry-lemmas the proof steps need, each mapped to a note
display number:

* `pos_part_sum`                     — note (15) `(u−h)₊ + (v−h)₊ ≥ u+v−2h`;
* `pigeonhole_child_selection`       — note (16) (uses (14),(15),(6));
* `neg_log_sum_le`                   — density-product → defect-sum glue
                                       (the `−ln` reading of (14));
* `two_pow_pred_lt_ceil_half`        — Bob step `q > 2^(a−2)` from `p > 2^(a−1)`;
* `rowThreshold_mono`                — Bob step row bookkeeping `A_(a−1) ≤ A_a`;
* `subgame_first_bit_dichotomy`      — "consider the first bit of a protocol"
                                       (typed `D_pos_split` + row/col-class
                                       restriction, de-privatized);
* `exists_denser_child`              — Bob "one child has defect ≤ Def(K)+ln 2";
* `exists_block_assignment`          — Alice "assign the block to a child
                                       containing at least ⌈A_a/2⌉ of its rows";
* `equipartitionGE_exists_exact_subset` — the exact↔GE equipartition adapter
                                       (scout FLAG (c-1));
* `member_max_projection`            — per-member maximum projection (note §8:
                                       defect ×(ℓ/p), row threshold preserved);
* `alice_coordinate_split`           — note (14): the typed product-of-
                                       projections engine (complementary
                                       coordinate split `p₀+p₁ = p`).

STRATEGIC ROUTE (scout report, fork (B)): the proofs are intended to
BRIDGE-AND-REUSE the flattened M&S machinery — `D_pos_split`,
`Dmat_row_part_le`, `Dmat_col_part_le` (all `private` in
`Workspace/BracketLemmas.lean`, to be exposed or re-derived),
`extended_product_of_projection` (PUBLIC, BracketLemmas.lean:934) and
`extended_maximum_projection` (PUBLIC, :1142) — transported per member via
the `Dfamily_eq_DSet` technique already used by `EthBridge.Bases`.
`one_step_partition` (Engine.lean:607) is NOT reusable here: it produces the
M&S row-rank children `p+ℓ+σ` / `p−ℓ`, not the complementary coordinate
split `ℓ₁+ℓ₂ = p` that §4 needs.

GLOBAL JUDGE FLAGS (individual flags at each declaration).
* All conclusions are PER-MEMBER (`… ≤ D (subgame (interlaceFun W p) RC.1
  RC.2)`), matching the entry point of `EthBridge.nonconstant`
  (Bases.lean:390) and the note's per-state phrasing; no family-min
  (`Dfamily`) form is stated, so no nonemptiness side conditions arise.
* The induction is packaged in `one_bit_down`; the Alice/Bob step lemmas
  take the level-(a−1) induction hypothesis as an explicit hypothesis `IH`
  so that each is independently provable and auditable.
* Child complexity bounds are phrased `D(child) + 1 ≤ D(parent)` (never
  `D(child) ≤ D(parent) − 1`), avoiding ℕ-truncation.
* The note's §2 side condition `2^a·x ≤ 1` is NOT carried: the one-bit-down
  argument never consumes it (the a = 2 base needs exactly `4x ≤ 1`, which
  `hx : x ≤ 1/4` supplies). Flagged for the judge to confirm.
* `hY : 1 ≤ Fintype.card Y` appears in the helper engines (projection /
  product-of-projections) and in both step lemmas, where nothing else
  excludes the empty-column degeneracy. Among the obligation lemmas it is
  omitted ONLY from `one_bit_down_base`, where `hTwo`+`hC` make it derivable
  (empty `Y` forces `LambdaGE = 0`, contradicting `3 ≤ C`); in `one_bit_down`
  it is retained redundantly (derivable there too). The judge may normalize.

DISCIPLINE: statements only; every body is `sorry` until the faithfulness
judge signs off. The `obdState` inhabitation / fidelity unit tests live in
`EthBridge.UnitTests` (DISCHARGED, no `sorry` — BtL: a def is trusted only
once its inhabitation closes); the one proved item retained here is the
`stateDensity ⊆ obdState` glue lemma (E3-adjacent, note (5)).
-/

namespace EthBridge

open NPCC
open Workspace.Types.Interlace
open Workspace.Types.CommComplexity

/-! ## The `(12)` one-bit-down state family (note §4)

A one-bit-down state at level `a ≥ 2` on `p > 2^(a-1)` active copies is a
restriction of `Interlace(W,p)` with

* at least `A_a` rows in every active block, and
* `Def(K) ≤ c_a(p)·λ + B(p)`                                       (12)

— i.e. the Theorem-1 (`stateDensity`) conditions with the extra `B(p)`
column-defect budget. Canonical form is the DENSITY form
`|K| ≥ n^p · e^{-(c_a(p)λ + B(p))}` (per the E0 judge decision for
`stateDensity`; `state_defect_iff_density` converts, `0 < |K|`, `0 < n`).

JUDGE FLAGS.
* The two conjuncts are literally the `hrows`/`hcols` hypotheses that the
  landed `EthBridge.nonconstant` (Bases.lean:390) consumes, so `(12)`-state
  nonconstancy is already proved for members of this family.
* Level constraints (`a ≥ 2`, `p > 2^(a-1)`) are USE-SITE hypotheses, not
  part of the family (mirroring `stateDensity`, whose `2^a x ≤ 1` is also
  use-site). -/

/-- **Note (12).** The one-bit-down state family at level `a` (density form):
row-equipartition at threshold `A_a` and `|K| ≥ n^p · e^{-(c_a(p)·λ + B(p))}`. -/
noncomputable def obdState (X Y : Type*) [Fintype X] [Fintype Y]
    (p a : ℕ) (x lam : ℝ) :
    Set (Finset (Fin p × X) × Finset (Fin p → Y)) :=
  { RC | IsEquipartitionedGE RC.1 (Finset.univ : Finset (Fin p))
           (rowThreshold (Fintype.card X) x a)
         ∧ ((Fintype.card Y : ℝ) ^ p) *
             Real.exp (-(cExcess a p * lam + Bdef p)) ≤ (RC.2.card : ℝ) }

/-! ## Pure-arithmetic helpers for the Alice step (notes (15), (16)) -/

/-- **Note (15).** `(u-h)₊ + (v-h)₊ ≥ u + v - 2h` over `ℝ` (positive parts
via `max · 0`). Instantiated with `u,v = p₀,p₁`, `h = 2^(a-2)` to give
`d₀ + d₁ ≥ p - 2^(a-1) = c_a(p)`. -/
theorem pos_part_sum (u v h : ℝ) :
    u + v - 2 * h ≤ max (u - h) 0 + max (v - h) 0 := by
  have h0 := le_max_left (u - h) 0
  have h1 := le_max_left (v - h) 0
  linarith

/-- **Note (16).** The Alice-step pigeonhole selection. If the two projected
defects satisfy `L₀ + L₁ ≤ c_a(p)·λ + B(p)` (note (14) applied to a `(12)`
budget) and `p₀ + p₁ = p > 2^(a-1)`, then some child `i` is ELIGIBLE
(`d_i > 0`, i.e. `p_i > 2^(a-2)`) and satisfies the level-(a−1) `(12)`
column budget `L_i ≤ c_(a-1)(p_i)·λ + B(p_i)`.

Proof route (note §4 Alice step): otherwise sum the strict reverse
inequalities over the eligible children, using `Bdef_antitone` (6)
(eligible `p_i` satisfy `3 ≤ p_i ≤ p` for `a ≥ 3`), `pos_part_sum` (15),
and `L_i ≥ 0`, to get `L₀ + L₁ > c_a(p)·λ + B(p)`, a contradiction.

JUDGE FLAGS.
* For eligible `i` and `a ≥ 3`, `d_i = p_i - 2^(a-2) = cExcess (a-1) p_i`
  (the `zpow` exponent `((a-1 : ℕ) : ℤ) - 1 = (a : ℤ) - 2` is a genuine
  integer power); the conclusion is stated directly through `cExcess`, so
  the selected child is literally a `(12)` state at level `a-1`.
* `hL₀/hL₁ : 0 ≤ L_i` give nonnegativity of the projected defects (supplied
  at the call site from `y_i ≤ 1`); the note's "`L_i = 0` for an empty
  coordinate set" convention (note §4, "we set `L_i = 0`") is recorded
  EXPLICITLY by `hE₀/hE₁ : p_i = 0 → L_i = 0`, supplied at the call site from
  `alice_coordinate_split`'s `p_i = 0 → y_i = 1` outputs.
* Non-strict `≤` in the conclusion, as in the note's (16). -/
theorem pigeonhole_child_selection (a p p₀ p₁ : ℕ) (L₀ L₁ lam : ℝ)
    (ha : 3 ≤ a) (hp : 2 ^ (a - 1) < p) (hsum : p₀ + p₁ = p)
    (hlam : 0 < lam) (hL₀ : 0 ≤ L₀) (hL₁ : 0 ≤ L₁)
    (hE₀ : p₀ = 0 → L₀ = 0) (hE₁ : p₁ = 0 → L₁ = 0)
    (hadd : L₀ + L₁ ≤ cExcess a p * lam + Bdef p) :
    (2 ^ (a - 2) < p₀ ∧ L₀ ≤ cExcess (a - 1) p₀ * lam + Bdef p₀) ∨
    (2 ^ (a - 2) < p₁ ∧ L₁ ≤ cExcess (a - 1) p₁ * lam + Bdef p₁) := by
  -- real ↔ nat bridge for the powers `2^(a-1)`, `2^(a-2)`
  have hcast : ((2 ^ (a - 2) : ℕ) : ℝ) = (2 : ℝ) ^ (a - 2) := by push_cast; ring
  have hA : cExcess a p = (p : ℝ) - 2 * (2 : ℝ) ^ (a - 2) := by
    unfold cExcess
    rw [show (a : ℤ) - 1 = ((a - 1 : ℕ) : ℤ) by omega, zpow_natCast,
        show a - 1 = (a - 2) + 1 by omega, pow_succ']
  have hI : ∀ q : ℕ, cExcess (a - 1) q = (q : ℝ) - (2 : ℝ) ^ (a - 2) := by
    intro q; unfold cExcess
    rw [show ((a - 1 : ℕ) : ℤ) - 1 = ((a - 2 : ℕ) : ℤ) by omega, zpow_natCast]
  have hpow_nat : (2 : ℕ) ^ (a - 1) = 2 * 2 ^ (a - 2) := by
    rw [show a - 1 = (a - 2) + 1 by omega, pow_succ']
  have hBp : 0 ≤ Bdef p := by
    unfold Bdef
    exact mul_nonneg (by positivity) (Real.log_nonneg (by norm_num))
  have hp_real : (p₀ : ℝ) + (p₁ : ℝ) = (p : ℝ) := by exact_mod_cast hsum
  -- `B(p) ≤ B(q)` for an eligible child `q` (then `q ≥ 3 ≥ 2`, `q ≤ p`)
  have hant : ∀ q : ℕ, 2 ^ (a - 2) < q → q ≤ p → Bdef p ≤ Bdef q := by
    intro q hq hqp
    have h2q : 2 ≤ q := by
      have : (2 : ℕ) ≤ 2 ^ (a - 2) := by
        calc (2 : ℕ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (a - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact Bdef_antitone p q h2q hqp
  rw [hA] at hadd
  have hexp : ((p : ℝ) - 2 * (2 : ℝ) ^ (a - 2)) * lam =
      ((p₀ : ℝ) - (2 : ℝ) ^ (a - 2)) * lam +
      ((p₁ : ℝ) - (2 : ℝ) ^ (a - 2)) * lam := by
    rw [show (p : ℝ) = (p₀ : ℝ) + (p₁ : ℝ) from hp_real.symm]; ring
  by_contra hcon
  push_neg at hcon
  obtain ⟨hc0, hc1⟩ := hcon
  by_cases he0 : 2 ^ (a - 2) < p₀ <;> by_cases he1 : 2 ^ (a - 2) < p₁
  · -- both children eligible
    have hb0 := hc0 he0; rw [hI p₀] at hb0
    have hb1 := hc1 he1; rw [hI p₁] at hb1
    have hant0 := hant p₀ he0 (by omega)
    have hant1 := hant p₁ he1 (by omega)
    linarith
  · -- only child 0 eligible
    have hb0 := hc0 he0; rw [hI p₀] at hb0
    have hant0 := hant p₀ he0 (by omega)
    have hp1le : (p₁ : ℝ) ≤ (2 : ℝ) ^ (a - 2) := by
      rw [← hcast]; exact_mod_cast (by omega : p₁ ≤ 2 ^ (a - 2))
    have hnp1 : ((p₁ : ℝ) - (2 : ℝ) ^ (a - 2)) * lam ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hlam.le
    linarith
  · -- only child 1 eligible
    have hb1 := hc1 he1; rw [hI p₁] at hb1
    have hant1 := hant p₁ he1 (by omega)
    have hp0le : (p₀ : ℝ) ≤ (2 : ℝ) ^ (a - 2) := by
      rw [← hcast]; exact_mod_cast (by omega : p₀ ≤ 2 ^ (a - 2))
    have hnp0 : ((p₀ : ℝ) - (2 : ℝ) ^ (a - 2)) * lam ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hlam.le
    linarith
  · -- neither eligible: impossible since `p₀+p₁ = p > 2^(a-1) = 2·2^(a-2)`
    omega

/-- Density-product → defect-sum glue: the `−ln` reading of note (14).
From `y₀·y₁ ≥ e^{-S}` (the product-of-projections conclusion) the absolute
defects `L_i = −ln y_i` satisfy `L₀ + L₁ ≤ S`. Feeds
`pigeonhole_child_selection` with `S = c_a(p)·λ + B(p)`. -/
theorem neg_log_sum_le (y₀ y₁ S : ℝ) (h₀ : 0 < y₀) (h₁ : 0 < y₁)
    (h : Real.exp (-S) ≤ y₀ * y₁) :
    -Real.log y₀ + -Real.log y₁ ≤ S := by
  have hmono := Real.log_le_log (Real.exp_pos (-S)) h
  rw [Real.log_exp, Real.log_mul (ne_of_gt h₀) (ne_of_gt h₁)] at hmono
  linarith

/-! ## Nat helpers for the Bob step -/

/-- Bob step, "Since `p > 2^(a-1)`, we have `q > 2^(a-2)`" (note §4), with
`q = ⌈p/2⌉` encoded as the Nat `(p+1)/2` (the `EthBridge.Arith` convention,
cf. `Bdef_ceil_halving` / `cExcess_ceil_halving`). -/
theorem two_pow_pred_lt_ceil_half (a p : ℕ) (ha : 2 ≤ a)
    (hp : 2 ^ (a - 1) < p) :
    2 ^ (a - 2) < (p + 1) / 2 := by
  have h2 : (2 : ℕ) ^ (a - 1) = 2 * 2 ^ (a - 2) := by
    conv_lhs => rw [show a - 1 = (a - 2) + 1 by omega]
    rw [pow_succ']
  omega

/-- Row-threshold monotonicity in the level: `A_a ≤ A_(a')` for `a ≤ a'`,
`0 ≤ x`. Bob-step bookkeeping: a state with `≥ A_a` rows per block is in
particular a candidate level-(a−1) state (`A_(a-1) ≤ A_a`). -/
theorem rowThreshold_mono (m : ℕ) (x : ℝ) (hx : 0 ≤ x) {a a' : ℕ}
    (haa : a ≤ a') :
    rowThreshold m x a ≤ rowThreshold m x a' := by
  unfold rowThreshold
  apply Nat.ceil_le_ceil
  apply mul_le_mul_of_nonneg_right _ hx
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_right₀ (by norm_num) haa

/-! ## The protocol first-bit layer

Note §4: "consider the first bit of a protocol. Suppose Alice speaks. …
Suppose instead that Bob speaks."

`subgame_first_bit_dichotomy` is the typed, de-privatized composite of the
flattened primitives `D_pos_split` (BracketLemmas.lean:1458, `private`) with
`Dmat_row_part_le` (:1517) / `Dmat_col_part_le` (:1594): a nonconstant game
has a first bit; the two row-halves (Alice) or column-halves (Bob) it induces
each lose at least one unit of complexity.

JUDGE FLAGS.
* The split is recorded by the speaking player's first-bit FUNCTION
  (`α : rows → Bool` / `β : cols → Bool`) and `Finset.filter`, exactly as in
  `D_pos_split`; this avoids `DecidableEq` instance baggage and makes the
  two children literally the fibers of the first bit.
* Child bounds in the truncation-free form `D(child) + 1 ≤ D(parent)`
  (classically equivalent to the note's "cost ≤ D f − 1" given
  `1 ≤ D(parent)`).
* Stated over arbitrary row/column types with an ambient game `f` and
  extraction data `(R, C)`, so it applies directly to
  `f = interlaceFun W p`, `(R, C) = RC` — no subgame-of-subgame bridge is
  needed by the consumers. -/

open Workspace.Types.Protocol Workspace.UpperBound in
/-- **First-bit dichotomy** (typed `D_pos_split` + row/col-class bounds).
Either Alice speaks first — her bit `α` splits the rows into two fibers,
each a strictly simpler subgame — or Bob does, with `β` on columns. -/
theorem subgame_first_bit_dichotomy {A B : Type*} (f : A → B → Bool)
    (R : Finset A) (C : Finset B)
    (h : 1 ≤ D (subgame f R C)) :
    (∃ α : A → Bool, ∀ b : Bool,
        D (subgame f (R.filter fun r => α r = b) C) + 1 ≤
          D (subgame f R C)) ∨
    (∃ β : B → Bool, ∀ b : Bool,
        D (subgame f R (C.filter fun c => β c = b)) + 1 ≤
          D (subgame f R C)) := by
  classical
  set g := subgame f R C with hg
  have hne : (AchievableCosts g).Nonempty := AchievableCosts_nonempty g
  have hmem : D g ∈ AchievableCosts g := by
    have := Nat.sInf_mem hne
    simpa [D] using this
  obtain ⟨P, hcost, hcomp⟩ := hmem
  cases P with
  | leaf z =>
      exfalso
      simp only [Protocol.cost] at hcost
      omega
  | aNode a l r =>
      left
      set α : A → Bool := fun r0 => if hr : r0 ∈ R then a ⟨r0, hr⟩ else false with hα
      refine ⟨α, ?_⟩
      have ecost : Protocol.cost (Protocol.aNode a l r)
          = 1 + max (Protocol.cost l) (Protocol.cost r) := rfl
      rw [ecost] at hcost
      have branch : ∀ (b : Bool)
          (Pb : Protocol {r0 // r0 ∈ R} {c // c ∈ C} Bool),
          (∀ x y, a x = b → Protocol.eval Pb x y = g x y) →
          Protocol.cost Pb ≤ D g - 1 →
          D (subgame f (R.filter fun r0 => α r0 = b) C) + 1 ≤ D g := by
        intro b Pb hPb hPbc
        have hincl : ∀ i : {r0 // r0 ∈ R.filter fun r0 => α r0 = b}, i.val ∈ R :=
          fun i => Finset.filter_subset _ _ i.property
        have haρ : ∀ i : {r0 // r0 ∈ R.filter fun r0 => α r0 = b},
            a ⟨i.val, hincl i⟩ = b := by
          intro i
          have hib : α i.val = b := (Finset.mem_filter.mp i.property).2
          have hval : α i.val = a ⟨i.val, hincl i⟩ := dif_pos (hincl i)
          exact hval.symm.trans hib
        have hcomp2 : Protocol.Computes
            (Protocol.comap
              (fun i => (⟨i.val, hincl i⟩ : {r0 // r0 ∈ R})) (fun j => j) Pb)
            (subgame f (R.filter fun r0 => α r0 = b) C) := by
          intro i j
          calc Protocol.eval
                (Protocol.comap (fun i => (⟨i.val, hincl i⟩ : {r0 // r0 ∈ R}))
                  (fun j => j) Pb) i j
              = Protocol.eval Pb ⟨i.val, hincl i⟩ j := Protocol.comap_eval _ _ Pb i j
            _ = g ⟨i.val, hincl i⟩ j := hPb _ _ (haρ i)
            _ = subgame f (R.filter fun r0 => α r0 = b) C i j := by
                  simp only [hg, subgame]
        have hmemA : Protocol.cost
            (Protocol.comap
              (fun i => (⟨i.val, hincl i⟩ : {r0 // r0 ∈ R})) (fun j => j) Pb) ∈
            AchievableCosts (subgame f (R.filter fun r0 => α r0 = b) C) :=
          ⟨_, rfl, hcomp2⟩
        have hle : D (subgame f (R.filter fun r0 => α r0 = b) C) ≤
            Protocol.cost
              (Protocol.comap
                (fun i => (⟨i.val, hincl i⟩ : {r0 // r0 ∈ R})) (fun j => j) Pb) := by
          simpa [D] using Nat.sInf_le hmemA
        rw [Protocol.comap_cost] at hle
        omega
      intro b
      cases b with
      | false =>
          refine branch false l ?_ ?_
          · intro x y hx
            have hev := hcomp x y
            simp only [Protocol.eval, hx, Bool.false_eq_true, if_false] at hev
            exact hev
          · omega
      | true =>
          refine branch true r ?_ ?_
          · intro x y hx
            have hev := hcomp x y
            simp only [Protocol.eval, hx, if_true] at hev
            exact hev
          · omega
  | bNode bb l r =>
      right
      set β : B → Bool := fun c0 => if hc : c0 ∈ C then bb ⟨c0, hc⟩ else false with hβ
      refine ⟨β, ?_⟩
      have ecost : Protocol.cost (Protocol.bNode bb l r)
          = 1 + max (Protocol.cost l) (Protocol.cost r) := rfl
      rw [ecost] at hcost
      have branch : ∀ (b : Bool)
          (Pb : Protocol {r0 // r0 ∈ R} {c // c ∈ C} Bool),
          (∀ x y, bb y = b → Protocol.eval Pb x y = g x y) →
          Protocol.cost Pb ≤ D g - 1 →
          D (subgame f R (C.filter fun c0 => β c0 = b)) + 1 ≤ D g := by
        intro b Pb hPb hPbc
        have hincl : ∀ j : {c0 // c0 ∈ C.filter fun c0 => β c0 = b}, j.val ∈ C :=
          fun j => Finset.filter_subset _ _ j.property
        have hbρ : ∀ j : {c0 // c0 ∈ C.filter fun c0 => β c0 = b},
            bb ⟨j.val, hincl j⟩ = b := by
          intro j
          have hjb : β j.val = b := (Finset.mem_filter.mp j.property).2
          have hval : β j.val = bb ⟨j.val, hincl j⟩ := dif_pos (hincl j)
          exact hval.symm.trans hjb
        have hcomp2 : Protocol.Computes
            (Protocol.comap
              (fun i => i) (fun j => (⟨j.val, hincl j⟩ : {c0 // c0 ∈ C})) Pb)
            (subgame f R (C.filter fun c0 => β c0 = b)) := by
          intro i j
          calc Protocol.eval
                (Protocol.comap (fun i => i)
                  (fun j => (⟨j.val, hincl j⟩ : {c0 // c0 ∈ C})) Pb) i j
              = Protocol.eval Pb i ⟨j.val, hincl j⟩ := Protocol.comap_eval _ _ Pb i j
            _ = g i ⟨j.val, hincl j⟩ := hPb _ _ (hbρ j)
            _ = subgame f R (C.filter fun c0 => β c0 = b) i j := by
                  simp only [hg, subgame]
        have hmemA : Protocol.cost
            (Protocol.comap
              (fun i => i) (fun j => (⟨j.val, hincl j⟩ : {c0 // c0 ∈ C})) Pb) ∈
            AchievableCosts (subgame f R (C.filter fun c0 => β c0 = b)) :=
          ⟨_, rfl, hcomp2⟩
        have hle : D (subgame f R (C.filter fun c0 => β c0 = b)) ≤
            Protocol.cost
              (Protocol.comap
                (fun i => i) (fun j => (⟨j.val, hincl j⟩ : {c0 // c0 ∈ C})) Pb) := by
          simpa [D] using Nat.sInf_le hmemA
        rw [Protocol.comap_cost] at hle
        omega
      intro b
      cases b with
      | false =>
          refine branch false l ?_ ?_
          · intro x y hy
            have hev := hcomp x y
            simp only [Protocol.eval, hy, Bool.false_eq_true, if_false] at hev
            exact hev
          · omega
      | true =>
          refine branch true r ?_ ?_
          · intro x y hy
            have hev := hcomp x y
            simp only [Protocol.eval, hy, if_true] at hev
            exact hev
          · omega

/-- Bob step, "One child has column defect at most `Def(K) + ln 2`" — in
density form: one fiber of Bob's first bit retains at least half the
columns. Pure pigeonhole on `Finset.filter`. -/
theorem exists_denser_child {B : Type*} (C : Finset B) (β : B → Bool) :
    ∃ b : Bool,
      (C.card : ℝ) / 2 ≤ ((C.filter fun c => β c = b).card : ℝ) := by
  classical
  have hpart :
      (C.filter fun c => β c = true).card +
        (C.filter fun c => β c = false).card = C.card := by
    have h := Finset.filter_card_add_filter_neg_card_eq_card
      (s := C) (p := fun c => β c = true)
    simp only [Bool.not_eq_true] at h
    exact h
  rcases le_total ((C.filter fun c => β c = false).card : ℝ)
      ((C.filter fun c => β c = true).card : ℝ) with h | h
  · refine ⟨true, ?_⟩
    have : (C.card : ℝ) =
        (C.filter fun c => β c = true).card +
          (C.filter fun c => β c = false).card := by exact_mod_cast hpart.symm
    rw [this]; linarith
  · refine ⟨false, ?_⟩
    have : (C.card : ℝ) =
        (C.filter fun c => β c = true).card +
          (C.filter fun c => β c = false).card := by exact_mod_cast hpart.symm
    rw [this]; linarith

/-- Alice step, block assignment (note §4): "In each active block, assign
the block to a child containing at least `⌈A_a/2⌉` of its rows. Break ties
arbitrarily." Given `≥ T` rows per block and Alice's bit `α`, some
assignment `σ : Fin p → Bool` picks, for every block `q`, a fiber holding
at least `⌈T/2⌉` of that block's rows. The real-ceiling `⌈(T:ℝ)/2⌉₊` matches
`rowThreshold_ceil_halving` (note (1)), which turns it into `A_(a-1)` at the
call site. -/
theorem exists_block_assignment {X : Type*} (p T : ℕ)
    (R : Finset (Fin p × X)) (α : (Fin p × X) → Bool)
    (hrows : IsEquipartitionedGE R (Finset.univ : Finset (Fin p)) T) :
    ∃ σ : Fin p → Bool, ∀ q : Fin p,
      ⌈(T : ℝ) / 2⌉₊ ≤
        (((R.filter fun r => α r = σ q).filter fun r => r.1 = q).card) := by
  classical
  have key : ∀ q : Fin p, ∃ b : Bool,
      ⌈(T : ℝ) / 2⌉₊ ≤
        (((R.filter fun r => α r = b).filter fun r => r.1 = q).card) := by
    intro q
    have hFqT : T ≤ (R.filter fun r => r.1 = q).card := hrows q (Finset.mem_univ q)
    have hsplit :
        ((R.filter fun r => r.1 = q).filter fun r => α r = true).card +
          ((R.filter fun r => r.1 = q).filter fun r => α r = false).card =
          (R.filter fun r => r.1 = q).card := by
      have h := Finset.filter_card_add_filter_neg_card_eq_card
        (s := R.filter fun r => r.1 = q) (p := fun r => α r = true)
      simpa only [Bool.not_eq_true] using h
    have hcomm : ∀ b : Bool,
        ((R.filter fun r => α r = b).filter fun r => r.1 = q) =
          (R.filter fun r => r.1 = q).filter fun r => α r = b := by
      intro b; rw [Finset.filter_comm]
    have hmax :
        ⌈(T : ℝ) / 2⌉₊ ≤ ((R.filter fun r => r.1 = q).filter fun r => α r = true).card ∨
        ⌈(T : ℝ) / 2⌉₊ ≤ ((R.filter fun r => r.1 = q).filter fun r => α r = false).card := by
      by_contra hc
      push_neg at hc
      obtain ⟨hct, hcf⟩ := hc
      have h1 := Nat.lt_ceil.mp hct
      have h2 := Nat.lt_ceil.mp hcf
      have h3 : ((R.filter fun r => r.1 = q).card : ℝ) =
          (((R.filter fun r => r.1 = q).filter fun r => α r = true).card : ℝ) +
          (((R.filter fun r => r.1 = q).filter fun r => α r = false).card : ℝ) := by
        exact_mod_cast hsplit.symm
      have h4 : (T : ℝ) ≤ ((R.filter fun r => r.1 = q).card : ℝ) := by exact_mod_cast hFqT
      linarith
    rcases hmax with hb | hb
    · exact ⟨true, by rw [hcomm true]; exact hb⟩
    · exact ⟨false, by rw [hcomm false]; exact hb⟩
  choose σ hσ using key
  exact ⟨σ, hσ⟩

/-! ## Projection engines -/

/-- **Exact↔GE equipartition adapter** (scout FLAG (c-1)). The ETH states
carry `IsEquipartitionedGE` (≥ `T` per block); the flattened M&S engines
(`extended_product_of_projection`, `maximum_projection_lemma`) require EXACT
equipartition. Shrinking each block to exactly `T` rows produces the exact
sub-extraction the engines eat; the induced subgame is a subgame of the
original, so all complexity upper bounds transport. -/
theorem equipartitionGE_exists_exact_subset {ι X : Type*} [DecidableEq ι]
    (R : Finset (ι × X)) (Q : Finset ι) (T : ℕ)
    (h : IsEquipartitionedGE R Q T) :
    ∃ R' ⊆ R, ∀ q ∈ Q, ((R'.filter fun r => r.1 = q).card = T) := by
  classical
  -- pick an exact-`T` subset of each `q`-fiber (`q ∈ Q`)
  have key : ∀ q, q ∈ Q → ∃ t : Finset (ι × X),
      t ⊆ (R.filter fun r => r.1 = q) ∧ t.card = T := by
    intro q hq
    obtain ⟨t, hts, htc⟩ :=
      Finset.exists_subset_card_eq (h q hq)
    exact ⟨t, hts, htc⟩
  choose! S hSsub hScard using key
  refine ⟨Q.biUnion S, ?_, ?_⟩
  · -- `⋃_{q∈Q} S q ⊆ R`
    intro r hr
    rw [Finset.mem_biUnion] at hr
    obtain ⟨q, hq, hrq⟩ := hr
    exact Finset.filter_subset _ _ (hSsub q hq hrq)
  · -- every `q ∈ Q` fiber of the union is exactly `S q`, card `T`
    intro q hq
    have hfib : ((Q.biUnion S).filter fun r => r.1 = q) = S q := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_biUnion]
      constructor
      · rintro ⟨⟨q', hq', hr'⟩, hrq⟩
        have e1 : r.1 = q' := (Finset.mem_filter.mp (hSsub q' hq' hr')).2
        have : q' = q := e1.symm.trans hrq
        subst this
        exact hr'
      · intro hr
        have hsub := hSsub q hq hr
        rw [Finset.mem_filter] at hsub
        exact ⟨⟨q, hq, hr⟩, hsub.2⟩
    rw [hfib]
    exact hScard q hq

/-- **Per-member maximum projection** (note §8: "maximum projection
multiplies absolute defect by the retained coordinate ratio"; the per-member
form of `dfamily_extended_projection` / `extended_maximum_projection`
(BracketLemmas.lean:1142) with an arbitrary block threshold `T`). From a
`p`-copy extraction with `≥ T` rows per block and column density `≥ y`,
maximum projection to `ℓ ≤ p` coordinates yields an `ℓ`-copy extraction with
the SAME per-block threshold `T`, density `≥ y^{ℓ/p}` (defect `×(ℓ/p)`), and
no larger complexity.

Consumers: the a = 2 base at `ℓ = 3` (`T = A_2`), the Bob step at
`ℓ = q = ⌈p/2⌉` (`T = A_a`).

JUDGE FLAGS.
* Row threshold PRESERVED (not halved) under max-projection — scout report
  on `maximum_projection_lemma` (Projections.lean:2081).
* `hX`/`hY` are the `Dfamily_eq_DSet`-transfer conditions
  (`1 ≤ card X`) plus the column-nonemptiness guard (`1 ≤ card Y`, which
  with `hy0` forces `0 < |C|`); the judge may weaken. -/
theorem member_max_projection {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (p ℓ : ℕ) (T : ℕ) (y : ℝ)
    (hℓ1 : 1 ≤ ℓ) (hℓp : ℓ ≤ p) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y)
    (R : Finset (Fin p × X)) (C : Finset (Fin p → Y))
    (hrows : IsEquipartitionedGE R (Finset.univ : Finset (Fin p)) T)
    (hcols : ((Fintype.card Y : ℝ) ^ p) * y ≤ (C.card : ℝ)) :
    ∃ (R' : Finset (Fin ℓ × X)) (C' : Finset (Fin ℓ → Y)),
      IsEquipartitionedGE R' (Finset.univ : Finset (Fin ℓ)) T ∧
      ((Fintype.card Y : ℝ) ^ ℓ) * Real.rpow y ((ℓ : ℝ) / (p : ℝ)) ≤
        (C'.card : ℝ) ∧
      D (subgame (interlaceFun W ℓ) R' C') ≤
        D (subgame (interlaceFun W p) R C) := by
  classical
  have _hy_bounds : 0 < y ∧ y ≤ 1 := ⟨hy0, hy1⟩
  have _hX_pos : 0 < Fintype.card X := lt_of_lt_of_le Nat.zero_lt_one hX
  let eY : Fin (Fintype.card Y) ≃ Y := (Fintype.equivFin Y).symm
  let graph : (Fin p → Y) → Finset (Fin (Fintype.card Y) × Fin p) :=
    fun c => Finset.univ.filter fun z => eY z.1 = c z.2
  let F : Finset (Finset (Fin (Fintype.card Y) × Fin p)) := C.image graph
  have hgraph_inj : Function.Injective graph := by
    intro c d hcd
    funext q
    have hc : (eY.symm (c q), q) ∈ graph c := by
      simp [graph]
    rw [hcd] at hc
    simpa [graph] using hc
  have hFcard : F.card = C.card := by
    simp only [F]
    exact Finset.card_image_of_injective _ hgraph_inj
  obtain ⟨Q, hQcard, hQbound⟩ :=
    Workspace.Projections.corollary_3_19 F ℓ hℓ1 hℓp
  let eQ : Fin ℓ ≃ {q : Fin p // q ∈ Q} :=
    (finCongr hQcard.symm).trans Q.equivFin.symm
  let ι : Fin ℓ → Fin p := fun i => (eQ i).1
  let π : (Fin p → Y) → (Fin ℓ → Y) := fun c i => c (ι i)
  let C' : Finset (Fin ℓ → Y) := C.image π
  let R' : Finset (Fin ℓ × X) :=
    Finset.univ.filter fun r => (ι r.1, r.2) ∈ R
  let pgraph : (Fin ℓ → Y) → Finset (Fin (Fintype.card Y) × Fin p) :=
    fun d => Finset.univ.image fun i : Fin ℓ => (eY.symm (d i), ι i)
  have hι_inj : Function.Injective ι := by
    intro i j hij
    exact eQ.injective (Subtype.ext hij)
  have hpgraph_inj : Function.Injective pgraph := by
    intro d d' hdd'
    funext i
    have hm : (eY.symm (d i), ι i) ∈ pgraph d := by
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    rw [hdd'] at hm
    simp only [pgraph, Finset.mem_image, Finset.mem_univ, true_and] at hm
    obtain ⟨j, hj⟩ := hm
    have hij : j = i := hι_inj (congrArg Prod.snd hj)
    subst j
    exact eY.symm.injective (congrArg Prod.fst hj).symm
  have hfiltered : ∀ c : Fin p → Y,
      (graph c).filter (fun z => z.2 ∈ Q) = pgraph (π c) := by
    intro c
    ext z
    constructor
    · intro hz
      obtain ⟨hzgraph, hzQ⟩ := Finset.mem_filter.mp hz
      have hzval : eY z.1 = c z.2 := by simpa [graph] using hzgraph
      let i : Fin ℓ := eQ.symm ⟨z.2, hzQ⟩
      have hi : ι i = z.2 :=
        congrArg Subtype.val (eQ.apply_symm_apply ⟨z.2, hzQ⟩)
      simp only [pgraph, Finset.mem_image]
      refine ⟨i, Finset.mem_univ _, ?_⟩
      apply Prod.ext
      · simp only
        apply eY.injective
        simp only [Equiv.apply_symm_apply, π]
        rw [hi, hzval]
      · exact hi
    · intro hz
      simp only [pgraph, Finset.mem_image] at hz
      obtain ⟨i, _, hi⟩ := hz
      have hi1 := congrArg Prod.fst hi
      have hi2 := congrArg Prod.snd hi
      have hi2' : ι i = z.2 := by simpa using hi2
      have hzQ : z.2 ∈ Q := by
        rw [← hi2']
        exact (eQ i).2
      apply Finset.mem_filter.mpr
      refine ⟨?_, hzQ⟩
      simp only [graph, Finset.mem_filter, Finset.mem_univ, true_and]
      have hval : π c i = eY z.1 := by
        simpa using congrArg eY hi1
      change c (ι i) = eY z.1 at hval
      rw [← hval, hi2']
  have hproj_eq :
      F.image (fun S => S.filter (fun z => z.2 ∈ Q)) = C'.image pgraph := by
    rw [show F = C.image graph from rfl, Finset.image_image]
    rw [show C' = C.image π from rfl, Finset.image_image]
    apply Finset.image_congr
    intro c hc
    exact hfiltered c
  have hprojcard :
      (F.image (fun S => S.filter (fun z => z.2 ∈ Q))).card = C'.card := by
    rw [hproj_eq, Finset.card_image_of_injective _ hpgraph_inj]
  have hC'pow : Real.rpow (C.card : ℝ) ((ℓ : ℝ) / (p : ℝ)) ≤ (C'.card : ℝ) := by
    rw [← hprojcard, ← hFcard]
    exact hQbound
  have hp1 : 1 ≤ p := le_trans hℓ1 hℓp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp1
  have he0 : 0 ≤ (ℓ : ℝ) / (p : ℝ) := by positivity
  have hn0 : (0 : ℝ) < Fintype.card Y := by exact_mod_cast hY
  have hbase0 : 0 ≤ ((Fintype.card Y : ℝ) ^ p) * y := by positivity
  have hpowmono :
      Real.rpow (((Fintype.card Y : ℝ) ^ p) * y) ((ℓ : ℝ) / (p : ℝ)) ≤
        Real.rpow (C.card : ℝ) ((ℓ : ℝ) / (p : ℝ)) :=
    Real.rpow_le_rpow hbase0 hcols he0
  have hnpow :
      Real.rpow ((Fintype.card Y : ℝ) ^ p) ((ℓ : ℝ) / (p : ℝ)) =
        (Fintype.card Y : ℝ) ^ ℓ := by
    rw [show (Fintype.card Y : ℝ) ^ p =
      Real.rpow (Fintype.card Y : ℝ) (p : ℝ) by
        exact (Real.rpow_natCast _ _).symm]
    calc
      Real.rpow (Real.rpow (Fintype.card Y : ℝ) (p : ℝ))
          ((ℓ : ℝ) / (p : ℝ)) =
          Real.rpow (Fintype.card Y : ℝ)
            ((p : ℝ) * ((ℓ : ℝ) / (p : ℝ))) :=
        (Real.rpow_mul (le_of_lt hn0) _ _).symm
      _ = Real.rpow (Fintype.card Y : ℝ) (ℓ : ℝ) := by
        congr 1
        field_simp
      _ = (Fintype.card Y : ℝ) ^ ℓ := Real.rpow_natCast _ _
  have hcolC' :
      ((Fintype.card Y : ℝ) ^ ℓ) * Real.rpow y ((ℓ : ℝ) / (p : ℝ)) ≤
        (C'.card : ℝ) := by
    calc
      ((Fintype.card Y : ℝ) ^ ℓ) * Real.rpow y ((ℓ : ℝ) / (p : ℝ)) =
          Real.rpow (((Fintype.card Y : ℝ) ^ p) * y)
            ((ℓ : ℝ) / (p : ℝ)) := by
        rw [← hnpow]
        exact (Real.mul_rpow (by positivity) hy0.le).symm
      _ ≤ Real.rpow (C.card : ℝ) ((ℓ : ℝ) / (p : ℝ)) := hpowmono
      _ ≤ (C'.card : ℝ) := hC'pow
  have hrowR' : IsEquipartitionedGE R' (Finset.univ : Finset (Fin ℓ)) T := by
    intro q' _
    refine le_trans (hrows (ι q') (Finset.mem_univ _)) ?_
    apply Finset.card_le_card_of_injOn (fun r => (q', r.2))
    · rintro ⟨r1, r2⟩ hr
      simp only [Finset.mem_coe, Finset.mem_filter] at hr
      obtain ⟨hrR, hr1⟩ := hr
      have hr1' : r1 = ι q' := hr1
      subst r1
      change (q', r2) ∈ ↑(R'.filter fun s : Fin ℓ × X => s.1 = q')
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrR⟩, rfl⟩
    · rintro ⟨r1, r2⟩ hr ⟨r1', r2'⟩ hr' hrr
      simp only [Finset.mem_coe, Finset.mem_filter] at hr hr'
      have h2 : r2 = r2' := congrArg Prod.snd hrr
      have h1 : r1 = r1' := hr.2.trans hr'.2.symm
      exact Prod.ext h1 h2
  have hcomp : D (subgame (interlaceFun W ℓ) R' C') ≤
      D (subgame (interlaceFun W p) R C) := by
    have hpre : ∀ d ∈ C', ∃ c ∈ C, π c = d := fun d hd => Finset.mem_image.mp hd
    choose g hgC hgπ using hpre
    let ρ : {s // s ∈ R'} → {r // r ∈ R} := fun s =>
      ⟨(ι s.1.1, s.1.2), (Finset.mem_filter.mp s.2).2⟩
    let τ : {d // d ∈ C'} → {c // c ∈ C} := fun d => ⟨g d.1 d.2, hgC d.1 d.2⟩
    have heq : subgame (interlaceFun W ℓ) R' C' = fun s d =>
        subgame (interlaceFun W p) R C (ρ s) (τ d) := by
      funext s d
      change W s.1.2 (d.1 s.1.1) = W s.1.2 (g d.1 d.2 (ι s.1.1))
      exact congrArg (W s.1.2) (congrFun (hgπ d.1 d.2) s.1.1).symm
    rw [heq]
    exact D_mapNodes_le _ ρ τ
  exact ⟨R', C', hrowR', hcolC', hcomp⟩

/-- **Note (14): the typed product-of-projections engine** (the per-member,
`ℕ`-threshold form of `extended_product_of_projection`, Lemma 4.3,
BracketLemmas.lean:934). Alice's first bit `α` splits the rows of a `p`-copy
extraction; assigning each block to a fiber holding `≥ ⌈T/2⌉` of its rows
(`exists_block_assignment`) splits the coordinates into complementary sets
of sizes `p₀ + p₁ = p`; projecting the columns to each side gives densities
`y₀·y₁ ≥ y` — note (14) `L₀ + L₁ ≤ Def(K)` in density form — and each
projected game embeds in the corresponding row-fiber child, so its
complexity is bounded by that child's.

JUDGE FLAGS.
* Row threshold HALVES (`T → ⌈(T:ℝ)/2⌉₊`): the typed rendering of the
  BoolMat lemma's `x → x/2` (note (1) then gives `A_(a-1) ≤ ⌈A_a/2⌉` at the
  call site). Ceiling form matches `rowThreshold_ceil_halving`.
* GE-equipartition in AND out; the exact-equipartition demand of the
  BoolMat engine is discharged internally via
  `equipartitionGE_exists_exact_subset` (scout FLAG (c-1)) — shrinking rows
  only shrinks the subgame, so the child complexity bounds survive.
* Degenerate sides (`p_b = 0`) are guarded by `1 ≤ p_b →`, mirroring the
  BoolMat lemma; the note's "`L_i = 0` for an empty coordinate set" is
  exported EXPLICITLY as `p_b = 0 → y_b = 1` (so `L_b = -ln y_b = 0`),
  which discharges `pigeonhole_child_selection`'s `hE₀/hE₁` at the call site.
* The children's rows are drawn from the assigned blocks of the
  corresponding fiber, which is exactly what
  `D(child_b) ≤ D(subgame f (R.filter (α · = b)) C)` records; no explicit
  coordinate-set data is exported (the complexity comparisons carry all the
  downstream content). -/
theorem alice_coordinate_split {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (p : ℕ) (T : ℕ) (y : ℝ)
    (hp : 1 ≤ p) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y)
    (R : Finset (Fin p × X)) (C : Finset (Fin p → Y))
    (α : (Fin p × X) → Bool)
    (hrows : IsEquipartitionedGE R (Finset.univ : Finset (Fin p)) T)
    (hcols : ((Fintype.card Y : ℝ) ^ p) * y ≤ (C.card : ℝ)) :
    ∃ (p₀ p₁ : ℕ) (y₀ y₁ : ℝ)
      (S₀ : Finset (Fin p₀ × X)) (K₀ : Finset (Fin p₀ → Y))
      (S₁ : Finset (Fin p₁ × X)) (K₁ : Finset (Fin p₁ → Y)),
      p₀ + p₁ = p ∧
      y ≤ y₀ * y₁ ∧
      0 < y₀ ∧ y₀ ≤ 1 ∧ 0 < y₁ ∧ y₁ ≤ 1 ∧
      (p₀ = 0 → y₀ = 1) ∧ (p₁ = 0 → y₁ = 1) ∧
      (1 ≤ p₀ →
        IsEquipartitionedGE S₀ (Finset.univ : Finset (Fin p₀))
          ⌈(T : ℝ) / 2⌉₊ ∧
        ((Fintype.card Y : ℝ) ^ p₀) * y₀ ≤ (K₀.card : ℝ) ∧
        D (subgame (interlaceFun W p₀) S₀ K₀) ≤
          D (subgame (interlaceFun W p)
              (R.filter fun r => α r = false) C)) ∧
      (1 ≤ p₁ →
        IsEquipartitionedGE S₁ (Finset.univ : Finset (Fin p₁))
          ⌈(T : ℝ) / 2⌉₊ ∧
        ((Fintype.card Y : ℝ) ^ p₁) * y₁ ≤ (K₁.card : ℝ) ∧
        D (subgame (interlaceFun W p₁) S₁ K₁) ≤
          D (subgame (interlaceFun W p)
              (R.filter fun r => α r = true) C)) := by
  classical
  obtain ⟨σ, hσ⟩ := exists_block_assignment p T R α hrows
  -- the complementary coordinate classes of the block assignment, enumerated
  set p₀ := Fintype.card {q : Fin p // σ q = false} with hp₀def
  set p₁ := Fintype.card {q : Fin p // σ q = true} with hp₁def
  let e₀ : Fin p₀ ≃ {q : Fin p // σ q = false} := (Fintype.equivFin _).symm
  let e₁ : Fin p₁ ≃ {q : Fin p // σ q = true} := (Fintype.equivFin _).symm
  let ι₀ : Fin p₀ → Fin p := fun i => (e₀ i).1
  let ι₁ : Fin p₁ → Fin p := fun i => (e₁ i).1
  let π₀ : (Fin p → Y) → (Fin p₀ → Y) := fun c i => c (ι₀ i)
  let π₁ : (Fin p → Y) → (Fin p₁ → Y) := fun c i => c (ι₁ i)
  let K₀ : Finset (Fin p₀ → Y) := C.image π₀
  let K₁ : Finset (Fin p₁ → Y) := C.image π₁
  let S₀ : Finset (Fin p₀ × X) :=
    Finset.univ.filter fun s => (ι₀ s.1, s.2) ∈ R ∧ α (ι₀ s.1, s.2) = false
  let S₁ : Finset (Fin p₁ × X) :=
    Finset.univ.filter fun s => (ι₁ s.1, s.2) ∈ R ∧ α (ι₁ s.1, s.2) = true
  have hn1 : (1 : ℝ) ≤ (Fintype.card Y : ℝ) := by exact_mod_cast hY
  have hn0 : (0 : ℝ) < (Fintype.card Y : ℝ) := lt_of_lt_of_le one_pos hn1
  have hι₀b : ∀ i, σ (ι₀ i) = false := fun i => (e₀ i).2
  have hι₁b : ∀ i, σ (ι₁ i) = true := fun i => (e₁ i).2
  -- the two class sizes are complementary: `p₀ + p₁ = p`
  have hpsum : p₀ + p₁ = p := by
    rw [hp₀def, hp₁def, Fintype.card_subtype, Fintype.card_subtype]
    have hneg : ((Finset.univ : Finset (Fin p)).filter fun q => ¬ σ q = false) =
        ((Finset.univ : Finset (Fin p)).filter fun q => σ q = true) := by
      apply Finset.filter_congr
      intro q _
      cases hq : σ q <;> simp
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset (Fin p))) (p := fun q => σ q = false)
    rw [hneg] at hsplit
    rw [hsplit]
    simp
  -- restriction along `(π₀, π₁)` is injective (every coordinate is on a side)
  have hcover : ∀ c c' : Fin p → Y, π₀ c = π₀ c' → π₁ c = π₁ c' → c = c' := by
    intro c c' h0 h1
    funext j
    cases hj : σ j with
    | false =>
        have hi : ι₀ (e₀.symm ⟨j, hj⟩) = j := by
          show (e₀ (e₀.symm ⟨j, hj⟩)).1 = j
          rw [Equiv.apply_symm_apply]
        have hc : c (ι₀ (e₀.symm ⟨j, hj⟩)) = c' (ι₀ (e₀.symm ⟨j, hj⟩)) :=
          congrFun h0 (e₀.symm ⟨j, hj⟩)
        rwa [hi] at hc
    | true =>
        have hi : ι₁ (e₁.symm ⟨j, hj⟩) = j := by
          show (e₁ (e₁.symm ⟨j, hj⟩)).1 = j
          rw [Equiv.apply_symm_apply]
        have hc : c (ι₁ (e₁.symm ⟨j, hj⟩)) = c' (ι₁ (e₁.symm ⟨j, hj⟩)) :=
          congrFun h1 (e₁.symm ⟨j, hj⟩)
        rwa [hi] at hc
  -- positivity / size bookkeeping for the projected column sets
  have hCpos : 0 < C.card := by
    have hpos : (0 : ℝ) < ((Fintype.card Y : ℝ) ^ p) * y :=
      mul_pos (pow_pos hn0 p) hy0
    exact_mod_cast lt_of_lt_of_le hpos hcols
  have hCne : C.Nonempty := Finset.card_pos.mp hCpos
  have hK₀ne : K₀.Nonempty := hCne.image _
  have hK₁ne : K₁.Nonempty := hCne.image _
  have hK₀pos : (0 : ℝ) < (K₀.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hK₀ne
  have hK₁pos : (0 : ℝ) < (K₁.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hK₁ne
  have hK₀le : K₀.card ≤ Fintype.card Y ^ p₀ := by
    calc K₀.card ≤ Fintype.card (Fin p₀ → Y) := Finset.card_le_univ _
      _ = Fintype.card Y ^ p₀ := by rw [Fintype.card_fun, Fintype.card_fin]
  have hK₁le : K₁.card ≤ Fintype.card Y ^ p₁ := by
    calc K₁.card ≤ Fintype.card (Fin p₁ → Y) := Finset.card_le_univ _
      _ = Fintype.card Y ^ p₁ := by rw [Fintype.card_fun, Fintype.card_fin]
  set y₀ : ℝ := (K₀.card : ℝ) / (Fintype.card Y : ℝ) ^ p₀ with hy₀def
  set y₁ : ℝ := (K₁.card : ℝ) / (Fintype.card Y : ℝ) ^ p₁ with hy₁def
  have hy₀pos : 0 < y₀ := div_pos hK₀pos (pow_pos hn0 _)
  have hy₁pos : 0 < y₁ := div_pos hK₁pos (pow_pos hn0 _)
  have hy₀le1 : y₀ ≤ 1 := by
    rw [hy₀def, div_le_one (pow_pos hn0 _)]
    exact_mod_cast hK₀le
  have hy₁le1 : y₁ ≤ 1 := by
    rw [hy₁def, div_le_one (pow_pos hn0 _)]
    exact_mod_cast hK₁le
  -- degenerate sides: an empty coordinate class projects to the one-point set
  have hdeg₀ : p₀ = 0 → y₀ = 1 := by
    intro h0
    have hle : K₀.card ≤ 1 := by
      have hpow : Fintype.card Y ^ p₀ = 1 := by rw [h0, pow_zero]
      rw [← hpow]; exact hK₀le
    have hcard : K₀.card = 1 :=
      le_antisymm hle (Finset.card_pos.mpr hK₀ne)
    have hpowR : (Fintype.card Y : ℝ) ^ p₀ = 1 := by rw [h0, pow_zero]
    rw [hy₀def, hcard, hpowR]
    norm_num
  have hdeg₁ : p₁ = 0 → y₁ = 1 := by
    intro h1
    have hle : K₁.card ≤ 1 := by
      have hpow : Fintype.card Y ^ p₁ = 1 := by rw [h1, pow_zero]
      rw [← hpow]; exact hK₁le
    have hcard : K₁.card = 1 :=
      le_antisymm hle (Finset.card_pos.mpr hK₁ne)
    have hpowR : (Fintype.card Y : ℝ) ^ p₁ = 1 := by rw [h1, pow_zero]
    rw [hy₁def, hcard, hpowR]
    norm_num
  -- note (14) in density form: `y ≤ y₀ · y₁` via the pair injection
  have hCcard : C.card ≤ K₀.card * K₁.card := by
    rw [← Finset.card_product]
    apply Finset.card_le_card_of_injOn (fun c => (π₀ c, π₁ c))
    · intro c hc
      simp only [Finset.mem_coe] at hc
      exact Finset.mem_coe.mpr (Finset.mem_product.mpr
        ⟨Finset.mem_image_of_mem _ hc, Finset.mem_image_of_mem _ hc⟩)
    · intro c _ c' _ hcc
      exact hcover c c' (congrArg Prod.fst hcc) (congrArg Prod.snd hcc)
  have hyy : y ≤ y₀ * y₁ := by
    rw [hy₀def, hy₁def, div_mul_div_comm, ← pow_add, hpsum,
      le_div_iff₀ (pow_pos hn0 p)]
    calc y * (Fintype.card Y : ℝ) ^ p = ((Fintype.card Y : ℝ) ^ p) * y := by
          ring
      _ ≤ (C.card : ℝ) := hcols
      _ ≤ (K₀.card : ℝ) * (K₁.card : ℝ) := by exact_mod_cast hCcard
  -- rows: each side keeps `≥ ⌈T/2⌉` rows per block (the assigned fibers)
  have hequi₀ : IsEquipartitionedGE S₀ (Finset.univ : Finset (Fin p₀))
      ⌈(T : ℝ) / 2⌉₊ := by
    intro q' _
    have hass := hσ (ι₀ q')
    rw [hι₀b q'] at hass
    refine le_trans hass ?_
    apply Finset.card_le_card_of_injOn (fun r => (q', r.2))
    · rintro ⟨r1, r2⟩ hr
      simp only [Finset.mem_coe, Finset.mem_filter] at hr
      obtain ⟨⟨hrR, hrα⟩, hr1⟩ := hr
      have hr1' : r1 = ι₀ q' := hr1
      subst hr1'
      show (q', r2) ∈ ↑(S₀.filter fun s : Fin p₀ × X => s.1 = q')
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrR, hrα⟩, rfl⟩
    · rintro ⟨r1, r2⟩ hr ⟨r1', r2'⟩ hr' hrr
      simp only [Finset.mem_coe, Finset.mem_filter] at hr hr'
      have h2 : r2 = r2' :=
        congrArg Prod.snd
          (show ((q', r2) : Fin p₀ × X) = (q', r2') from hrr)
      have h1 : r1 = r1' := hr.2.trans hr'.2.symm
      exact Prod.ext h1 h2
  have hequi₁ : IsEquipartitionedGE S₁ (Finset.univ : Finset (Fin p₁))
      ⌈(T : ℝ) / 2⌉₊ := by
    intro q' _
    have hass := hσ (ι₁ q')
    rw [hι₁b q'] at hass
    refine le_trans hass ?_
    apply Finset.card_le_card_of_injOn (fun r => (q', r.2))
    · rintro ⟨r1, r2⟩ hr
      simp only [Finset.mem_coe, Finset.mem_filter] at hr
      obtain ⟨⟨hrR, hrα⟩, hr1⟩ := hr
      have hr1' : r1 = ι₁ q' := hr1
      subst hr1'
      show (q', r2) ∈ ↑(S₁.filter fun s : Fin p₁ × X => s.1 = q')
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrR, hrα⟩, rfl⟩
    · rintro ⟨r1, r2⟩ hr ⟨r1', r2'⟩ hr' hrr
      simp only [Finset.mem_coe, Finset.mem_filter] at hr hr'
      have h2 : r2 = r2' :=
        congrArg Prod.snd
          (show ((q', r2) : Fin p₁ × X) = (q', r2') from hrr)
      have h1 : r1 = r1' := hr.2.trans hr'.2.symm
      exact Prod.ext h1 h2
  -- columns: the density bounds hold by construction of `y_b`
  have hcols₀ : ((Fintype.card Y : ℝ) ^ p₀) * y₀ ≤ (K₀.card : ℝ) := by
    rw [hy₀def, mul_comm, div_mul_cancel₀ _ (ne_of_gt (pow_pos hn0 p₀))]
  have hcols₁ : ((Fintype.card Y : ℝ) ^ p₁) * y₁ ≤ (K₁.card : ℝ) := by
    rw [hy₁def, mul_comm, div_mul_cancel₀ _ (ne_of_gt (pow_pos hn0 p₁))]
  -- complexity: the projected game pulls back into the row-fiber child
  have hcomp₀ : D (subgame (interlaceFun W p₀) S₀ K₀) ≤
      D (subgame (interlaceFun W p) (R.filter fun r => α r = false) C) := by
    have hpre : ∀ d ∈ K₀, ∃ c ∈ C, π₀ c = d := fun d hd =>
      Finset.mem_image.mp hd
    choose g hgC hgπ using hpre
    let ρ : {s // s ∈ S₀} → {r // r ∈ R.filter fun r => α r = false} :=
      fun s => ⟨(ι₀ s.1.1, s.1.2), by
        have hs := (Finset.mem_filter.mp s.2).2
        exact Finset.mem_filter.mpr ⟨hs.1, hs.2⟩⟩
    let τ : {d // d ∈ K₀} → {c // c ∈ C} := fun d => ⟨g d.1 d.2, hgC d.1 d.2⟩
    have heq : subgame (interlaceFun W p₀) S₀ K₀ = fun s d =>
        subgame (interlaceFun W p) (R.filter fun r => α r = false) C
          (ρ s) (τ d) := by
      funext s d
      show W s.1.2 (d.1 s.1.1) = W s.1.2 (g d.1 d.2 (ι₀ s.1.1))
      exact congrArg (W s.1.2) (congrFun (hgπ d.1 d.2) s.1.1).symm
    rw [heq]
    exact D_mapNodes_le _ ρ τ
  have hcomp₁ : D (subgame (interlaceFun W p₁) S₁ K₁) ≤
      D (subgame (interlaceFun W p) (R.filter fun r => α r = true) C) := by
    have hpre : ∀ d ∈ K₁, ∃ c ∈ C, π₁ c = d := fun d hd =>
      Finset.mem_image.mp hd
    choose g hgC hgπ using hpre
    let ρ : {s // s ∈ S₁} → {r // r ∈ R.filter fun r => α r = true} :=
      fun s => ⟨(ι₁ s.1.1, s.1.2), by
        have hs := (Finset.mem_filter.mp s.2).2
        exact Finset.mem_filter.mpr ⟨hs.1, hs.2⟩⟩
    let τ : {d // d ∈ K₁} → {c // c ∈ C} := fun d => ⟨g d.1 d.2, hgC d.1 d.2⟩
    have heq : subgame (interlaceFun W p₁) S₁ K₁ = fun s d =>
        subgame (interlaceFun W p) (R.filter fun r => α r = true) C
          (ρ s) (τ d) := by
      funext s d
      show W s.1.2 (d.1 s.1.1) = W s.1.2 (g d.1 d.2 (ι₁ s.1.1))
      exact congrArg (W s.1.2) (congrFun (hgπ d.1 d.2) s.1.1).symm
    rw [heq]
    exact D_mapNodes_le _ ρ τ
  exact ⟨p₀, p₁, y₀, y₁, S₀, K₀, S₁, K₁, hpsum, hyy, hy₀pos, hy₀le1, hy₁pos,
    hy₁le1, hdeg₀, hdeg₁, fun _ => ⟨hequi₀, hcols₀, hcomp₀⟩,
    fun _ => ⟨hequi₁, hcols₁, hcomp₁⟩⟩

/-! ## `eth:lem-obd-base` — the a = 2 base of the one-bit-down statement

Note §4 "Base of the one-bit-down statement": `a = 2`, so `p ≥ 3`. Maximum
projection to THREE coordinates (`member_max_projection`, `ℓ = 3`,
`T = A_2`) gives a three-copy restriction with defect at most

  `(3/p)·Def(K) ≤ (3/p)(p-2)λ + (3/p)B(p) ≤ 3λ + (7/5)ln 2 ≤ -2 ln y`

(`Bdef_three` (8), then `hmargin` (2)), hence column density `≥ y²`, with
`≥ A_2 = ⌈4mx⌉` rows per block — a member of `bracketGE X Y 3 (4x) (y²)`.
The three-copy base `(Three)` (`three_copy_base_top_rung`, Bases.lean:121)
gives complexity `≥ C+1 = C+a-1`.

This is the `ℓ = 2 → ℓ = 3`, `1 ≤ D → C+1 ≤ D` re-parameterization of the
landed `nonconstant` (Bases.lean:390) — same skeleton, LOW risk.

JUDGE FLAGS.
* `hp : 2 < p` is `p > 2^(a-1)` at `a = 2`.
* Hypothesis set = `nonconstant`'s (in particular `hC : 3 ≤ C`, needed by
  `(Three)`'s side condition, and `hmargin` in the general-`y` form (2));
  `hY` omitted (derivable from `hTwo` + `hC`).
* `rowThreshold (card X) x 2 = ⌈(card X : ℝ)·(4x)⌉₊` (the `bracketGE`
  threshold at row parameter `4x`) holds by `ring`-normalization; the proof
  consumes it silently. -/

/-- **`eth:lem-obd-base` (note §4, one-bit-down base `a = 2`).** Every
`(12)`-state at level `2` has complexity `≥ C+1`. -/
theorem one_bit_down_base {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (C p : ℕ) (x y lam : ℝ)
    (hp : 2 < p)
    (hx0 : 0 < x) (hx : x ≤ 1 / 4) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hlam : 0 < lam) (hX : 1 ≤ Fintype.card X) (hC : 3 ≤ C)
    (hmargin : 3 * lam + (7 / 5) * Real.log 2 ≤ -2 * Real.log y)
    (hTwo : TwoCopyBundle W C x y)
    (RC : Finset (Fin p × X) × Finset (Fin p → Y))
    (hmem : RC ∈ obdState X Y p 2 x lam) :
    C + 1 ≤ D (subgame (interlaceFun W p) RC.1 RC.2) := by
  classical
  obtain ⟨hrows, hcols⟩ := hmem
  -- `hY` is derivable: empty `Y` would force the two-copy family complexity
  -- to `0`, contradicting `hTwo` + `hC : 3 ≤ C`.
  have hY : 1 ≤ Fintype.card Y := by
    by_contra hY0
    have hY0' : Fintype.card Y = 0 := by omega
    have hdeg : Dfamily (interlaceFun W 2) (bracketGE X Y 2 (2 * x) (y ^ 2)) = 0 :=
      Dfamily_zero_degenerate W (by linarith) (by nlinarith) hX
        (Or.inr ⟨by norm_num, hY0'⟩)
    have htop : C ≤ Dfamily (interlaceFun W 2) (bracketGE X Y 2 (2 * x) (y ^ 2)) :=
      le_trans hTwo (min_le_left _ _)
    rw [hdeg] at htop
    omega
  have hp3 : 3 ≤ p := by omega
  have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  -- arithmetic facts about the level-2 budget
  have hc2 : cExcess 2 p = (p : ℝ) - 2 := by
    unfold cExcess
    norm_num
  have hc_nonneg : 0 ≤ cExcess 2 p := by rw [hc2]; linarith
  have hB_nonneg : 0 ≤ Bdef p :=
    le_trans (Real.log_nonneg (by norm_num)) (Bdef_ge_log2 p (by omega))
  have hyp_one : Real.exp (-(cExcess 2 p * lam + Bdef p)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ cExcess 2 p * lam := mul_nonneg hc_nonneg hlam.le
    linarith
  -- maximum projection to THREE coordinates (`ℓ = 3`, `T = A_2`)
  obtain ⟨R', C', hrows', hcols', hDle⟩ :=
    member_max_projection W p 3 (rowThreshold (Fintype.card X) x 2)
      (Real.exp (-(cExcess 2 p * lam + Bdef p)))
      (by norm_num) (by omega) (Real.exp_pos _) hyp_one hX hY
      RC.1 RC.2 hrows hcols
  -- `(3/p)·(c_2(p)λ + B(p)) ≤ 3λ + (7/5)ln 2 ≤ -2 ln y`
  have hc_scaled : 3 / (p : ℝ) * cExcess 2 p ≤ 3 := by
    rw [hc2, div_mul_eq_mul_div, div_le_iff₀ hp0]
    nlinarith
  have hbudget : 3 / (p : ℝ) * (cExcess 2 p * lam + Bdef p) ≤ -2 * Real.log y := by
    calc
      3 / (p : ℝ) * (cExcess 2 p * lam + Bdef p)
          = (3 / (p : ℝ) * cExcess 2 p) * lam + 3 / (p : ℝ) * Bdef p := by ring
      _ ≤ 3 * lam + (7 / 5) * Real.log 2 :=
        add_le_add (mul_le_mul_of_nonneg_right hc_scaled hlam.le)
          (Bdef_three p hp3)
      _ ≤ -2 * Real.log y := hmargin
  -- hence the projected density dominates `y²`
  have hrpow_eq :
      Real.rpow (Real.exp (-(cExcess 2 p * lam + Bdef p))) (3 / (p : ℝ)) =
        Real.exp (-(cExcess 2 p * lam + Bdef p) * (3 / (p : ℝ))) := by
    change (Real.exp _) ^ (3 / (p : ℝ)) = _
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  have hy_sq_exp : y ^ 2 = Real.exp (2 * Real.log y) := by
    calc
      y ^ 2 = (Real.exp (Real.log y)) ^ 2 := by rw [Real.exp_log hy0]
      _ = Real.exp (2 * Real.log y) := by
        rw [← Real.exp_nat_mul]
        norm_num
  have hy2_le :
      y ^ 2 ≤ Real.rpow (Real.exp (-(cExcess 2 p * lam + Bdef p))) (3 / (p : ℝ)) := by
    rw [hy_sq_exp, hrpow_eq, Real.exp_le_exp,
      show -(cExcess 2 p * lam + Bdef p) * (3 / (p : ℝ)) =
        -(3 / (p : ℝ) * (cExcess 2 p * lam + Bdef p)) from by ring]
    linarith
  -- the projected member lands in `bracketGE X Y 3 (4x) (y²)`
  have hmem3 : (R', C') ∈ bracketGE X Y 3 (4 * x) (y ^ 2) := by
    refine ⟨?_, ?_⟩
    · intro j hj
      refine le_trans (le_of_eq ?_) (hrows' j hj)
      unfold rowThreshold
      congr 1
      ring
    · apply Nat.ceil_le.mpr
      calc
        ((Fintype.card Y : ℝ) ^ 3) * y ^ 2
            ≤ ((Fintype.card Y : ℝ) ^ 3) *
                Real.rpow (Real.exp (-(cExcess 2 p * lam + Bdef p))) (3 / (p : ℝ)) :=
          mul_le_mul_of_nonneg_left hy2_le (by positivity)
        _ ≤ (C'.card : ℝ) := by exact_mod_cast hcols'
  -- chain through the three-copy base `(Three)`
  calc
    C + 1 ≤ Dfamily (interlaceFun W 3) (bracketGE X Y 3 (4 * x) (y ^ 2)) :=
      three_copy_base_top_rung W C x y hC hx0 hx hy0 hy1 hX hTwo
    _ ≤ Dfamily (interlaceFun W 3) {(R', C')} :=
      Dfamily.anti_mono _ (Set.singleton_subset_iff.mpr hmem3)
        (Set.singleton_nonempty _)
    _ = D (subgame (interlaceFun W 3) R' C') := Dfamily.singleton _ _
    _ ≤ D (subgame (interlaceFun W p) RC.1 RC.2) := hDle

/-! ## `eth:lem-obd-alice` — the Alice step (a ≥ 3)

Note §4 "Alice step for the one-bit-down statement". Given Alice's first
bit `α` (children one unit simpler, `hchild`) and the level-(a−1) induction
hypothesis `IH`:

1. `exists_block_assignment` + `alice_coordinate_split` (note (14)): the
   coordinates split `p₀ + p₁ = p`, each side with `≥ ⌈A_a/2⌉` rows per
   block and densities `y₀·y₁ ≥ e^{-(c_a(p)λ + B(p))}`;
2. `neg_log_sum_le`: defects `L_i = -ln y_i` satisfy
   `L₀ + L₁ ≤ c_a(p)λ + B(p)`                                       (14);
3. `pigeonhole_child_selection` (via (15), (6)): some eligible `i` has
   `p_i > 2^(a-2)` and `L_i ≤ c_(a-1)(p_i)λ + B(p_i)`               (16);
4. `rowThreshold_ceil_halving` (1): `A_(a-1) ≤ ⌈A_a/2⌉`, so child `i` is a
   `(12)`-state at level `a-1`; `IH` gives `≥ C+a-2`; `hchild` adds the
   Alice bit: parent `≥ C+a-1`.

JUDGE FLAGS.
* HIGHEST-RISK E2 item (scout): consumes the two new engines.
* `IH` quantifies over ALL copy counts `p' > 2^(a-2)` — the coordinate
  split changes `p`, so the induction is on `a` alone with `p` universally
  quantified (as in the note, where (12) is stated for every `p > 2^(a-1)`).
* No `y`/`hTwo`/`hmargin` hypotheses: the Alice step never touches the
  terminal bases (matching `eth-obligations.json` deps: only (6)+(1)-side
  arithmetic). `hx0` appears only through `obdState`'s threshold and is not
  needed; omitted.
* `hY` retained: the engine of step 1 requires it and no `hTwo` is present
  to derive it. -/

/-- **`eth:lem-obd-alice` (note §4, Alice step, `a ≥ 3`).** If Alice speaks
first and the one-bit-down statement holds at level `a-1` (hypothesis `IH`),
then a `(12)`-state at level `a` has complexity `≥ C+a-1`. -/
theorem one_bit_down_alice {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (C p a : ℕ) (x lam : ℝ)
    (ha : 3 ≤ a) (hp : 2 ^ (a - 1) < p)
    (hlam : 0 < lam)
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y)
    (RC : Finset (Fin p × X) × Finset (Fin p → Y))
    (hmem : RC ∈ obdState X Y p a x lam)
    (α : (Fin p × X) → Bool)
    (hchild : ∀ b : Bool,
      D (subgame (interlaceFun W p)
          (RC.1.filter fun r => α r = b) RC.2) + 1 ≤
        D (subgame (interlaceFun W p) RC.1 RC.2))
    (IH : ∀ p' : ℕ, 2 ^ (a - 2) < p' →
      ∀ RC' : Finset (Fin p' × X) × Finset (Fin p' → Y),
        RC' ∈ obdState X Y p' (a - 1) x lam →
        C + (a - 2) ≤ D (subgame (interlaceFun W p') RC'.1 RC'.2)) :
    C + (a - 1) ≤ D (subgame (interlaceFun W p) RC.1 RC.2) := by
  classical
  obtain ⟨hrows, hcols⟩ := hmem
  have hpow4 : 4 ≤ 2 ^ (a - 1) := by
    calc
      (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (a - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hp3 : 3 ≤ p := by omega
  have hcast_exp : ((a : ℤ) - 1) = ((a - 1 : ℕ) : ℤ) := by omega
  have hc_pos : 0 < cExcess a p := by
    have hp_cast : (2 : ℝ) ^ (a - 1) < (p : ℝ) := by exact_mod_cast hp
    unfold cExcess
    rw [hcast_exp, zpow_natCast]
    linarith
  have hB_nonneg : 0 ≤ Bdef p :=
    le_trans (Real.log_nonneg (by norm_num)) (Bdef_ge_log2 p (by omega))
  have hyp_one : Real.exp (-(cExcess a p * lam + Bdef p)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have h1 : 0 ≤ cExcess a p * lam := mul_nonneg hc_pos.le hlam.le
    linarith
  -- note (14): split the coordinates along Alice's bit (product of
  -- projections; the `(12)` state supplies rows at `A_a`, density `y_p`)
  obtain ⟨p₀, p₁, y₀, y₁, S₀, K₀, S₁, K₁, hpsum, hyy, hy₀pos, hy₀le1,
      hy₁pos, hy₁le1, hdeg₀, hdeg₁, hside₀, hside₁⟩ :=
    alice_coordinate_split W p (rowThreshold (Fintype.card X) x a)
      (Real.exp (-(cExcess a p * lam + Bdef p)))
      (by omega) (Real.exp_pos _) hyp_one hX hY RC.1 RC.2 α hrows hcols
  -- note (14) in defect form: `L₀ + L₁ ≤ c_a(p)λ + B(p)`
  have hadd : -Real.log y₀ + -Real.log y₁ ≤ cExcess a p * lam + Bdef p :=
    neg_log_sum_le y₀ y₁ _ hy₀pos hy₁pos hyy
  -- note (16): pigeonhole an ELIGIBLE child carrying its level-(a−1) budget
  have hsel := pigeonhole_child_selection a p p₀ p₁
    (-Real.log y₀) (-Real.log y₁) lam ha hp hpsum hlam
    (neg_nonneg.mpr (Real.log_nonpos hy₀pos.le hy₀le1))
    (neg_nonneg.mpr (Real.log_nonpos hy₁pos.le hy₁le1))
    (fun h0 => by rw [hdeg₀ h0, Real.log_one, neg_zero])
    (fun h1 => by rw [hdeg₁ h1, Real.log_one, neg_zero])
    hadd
  -- note (1): the halved row threshold dominates `A_(a-1)`
  have hAhalf := rowThreshold_ceil_halving (Fintype.card X) x a (by omega)
  rcases hsel with ⟨helig, hbud⟩ | ⟨helig, hbud⟩
  · -- child 0 selected: a `(12)`-state at level `a−1` inside the
    -- `α = false` fiber
    obtain ⟨hequi, hcolsb, hDle⟩ := hside₀
      (lt_of_le_of_lt (Nat.zero_le _) helig)
    have hexp : Real.exp (-(cExcess (a - 1) p₀ * lam + Bdef p₀)) ≤ y₀ := by
      have hlog : -(cExcess (a - 1) p₀ * lam + Bdef p₀) ≤ Real.log y₀ := by
        linarith
      calc
        Real.exp (-(cExcess (a - 1) p₀ * lam + Bdef p₀))
            ≤ Real.exp (Real.log y₀) := Real.exp_le_exp.mpr hlog
        _ = y₀ := Real.exp_log hy₀pos
    have hmem' : (S₀, K₀) ∈ obdState X Y p₀ (a - 1) x lam := by
      refine ⟨?_, ?_⟩
      · intro j hj
        exact le_trans hAhalf (hequi j hj)
      · calc
          ((Fintype.card Y : ℝ) ^ p₀) *
              Real.exp (-(cExcess (a - 1) p₀ * lam + Bdef p₀))
              ≤ ((Fintype.card Y : ℝ) ^ p₀) * y₀ :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
          _ ≤ (K₀.card : ℝ) := hcolsb
    have hIH := IH p₀ helig (S₀, K₀) hmem'
    calc
      C + (a - 1) = (C + (a - 2)) + 1 := by omega
      _ ≤ D (subgame (interlaceFun W p₀) S₀ K₀) + 1 :=
        Nat.add_le_add_right hIH 1
      _ ≤ D (subgame (interlaceFun W p)
            (RC.1.filter fun r => α r = false) RC.2) + 1 :=
        Nat.add_le_add_right hDle 1
      _ ≤ D (subgame (interlaceFun W p) RC.1 RC.2) := hchild false
  · -- child 1 selected: symmetric, the `α = true` fiber
    obtain ⟨hequi, hcolsb, hDle⟩ := hside₁
      (lt_of_le_of_lt (Nat.zero_le _) helig)
    have hexp : Real.exp (-(cExcess (a - 1) p₁ * lam + Bdef p₁)) ≤ y₁ := by
      have hlog : -(cExcess (a - 1) p₁ * lam + Bdef p₁) ≤ Real.log y₁ := by
        linarith
      calc
        Real.exp (-(cExcess (a - 1) p₁ * lam + Bdef p₁))
            ≤ Real.exp (Real.log y₁) := Real.exp_le_exp.mpr hlog
        _ = y₁ := Real.exp_log hy₁pos
    have hmem' : (S₁, K₁) ∈ obdState X Y p₁ (a - 1) x lam := by
      refine ⟨?_, ?_⟩
      · intro j hj
        exact le_trans hAhalf (hequi j hj)
      · calc
          ((Fintype.card Y : ℝ) ^ p₁) *
              Real.exp (-(cExcess (a - 1) p₁ * lam + Bdef p₁))
              ≤ ((Fintype.card Y : ℝ) ^ p₁) * y₁ :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
          _ ≤ (K₁.card : ℝ) := hcolsb
    have hIH := IH p₁ helig (S₁, K₁) hmem'
    calc
      C + (a - 1) = (C + (a - 2)) + 1 := by omega
      _ ≤ D (subgame (interlaceFun W p₁) S₁ K₁) + 1 :=
        Nat.add_le_add_right hIH 1
      _ ≤ D (subgame (interlaceFun W p)
            (RC.1.filter fun r => α r = true) RC.2) + 1 :=
        Nat.add_le_add_right hDle 1
      _ ≤ D (subgame (interlaceFun W p) RC.1 RC.2) := hchild true

/-! ## `eth:lem-obd-bob` — the Bob step (a ≥ 3)

Note §4 "Bob step for the one-bit-down statement". Given Bob's first bit
`β` (children one unit simpler, `hchild`) and the level-(a−1) `IH`:

1. `exists_denser_child`: one fiber keeps `≥ |K|/2` columns — defect
   `≤ Def(K) + ln 2` (density `y_p/2`);
2. `member_max_projection` at `ℓ = q = ⌈p/2⌉ = (p+1)/2`, `T = A_a`:
   projected defect `≤ (q/p)(Def(K) + ln 2)`, rows still `≥ A_a` per block;
3. `cExcess_ceil_halving` (17) and `Bdef_ceil_halving` (18/7):
   `(q/p)·c_a(p)·λ + (q/p)(B(p) + ln 2) ≤ c_(a-1)(q)·λ + B(q)`;
4. `two_pow_pred_lt_ceil_half`: `q > 2^(a-2)`; `rowThreshold_mono`:
   `A_(a-1) ≤ A_a` — the projected child is a `(12)`-state at level `a-1`;
   `IH` gives `≥ C+a-2`, and Bob's bit closes `≥ C+a-1`.

JUDGE FLAGS.
* MEDIUM risk (scout): no product-of-projections; both scaling
  inequalities (17)/(18) are LANDED in `EthBridge.Arith`.
* `hx0 : 0 ≤ x` would suffice for `rowThreshold_mono`; stated `0 < x` for
  uniformity with the note's global `0 < x`. The judge may weaken.
* No `hTwo`/`hmargin`/`hC`: as with the Alice step, the terminal bases are
  not consumed (deps per ledger: (7)+(17)). -/

/-- **`eth:lem-obd-bob` (note §4, Bob step, `a ≥ 3`).** If Bob speaks first
and the one-bit-down statement holds at level `a-1` (hypothesis `IH`), then
a `(12)`-state at level `a` has complexity `≥ C+a-1`. -/
theorem one_bit_down_bob {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (C p a : ℕ) (x lam : ℝ)
    (ha : 3 ≤ a) (hp : 2 ^ (a - 1) < p)
    (hx0 : 0 < x) (hlam : 0 < lam)
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y)
    (RC : Finset (Fin p × X) × Finset (Fin p → Y))
    (hmem : RC ∈ obdState X Y p a x lam)
    (β : (Fin p → Y) → Bool)
    (hchild : ∀ b : Bool,
      D (subgame (interlaceFun W p)
          RC.1 (RC.2.filter fun c => β c = b)) + 1 ≤
        D (subgame (interlaceFun W p) RC.1 RC.2))
    (IH : ∀ p' : ℕ, 2 ^ (a - 2) < p' →
      ∀ RC' : Finset (Fin p' × X) × Finset (Fin p' → Y),
        RC' ∈ obdState X Y p' (a - 1) x lam →
        C + (a - 2) ≤ D (subgame (interlaceFun W p') RC'.1 RC'.2)) :
    C + (a - 1) ≤ D (subgame (interlaceFun W p) RC.1 RC.2) := by
  classical
  obtain ⟨hrows, hcols⟩ := hmem
  have ha2 : 2 ≤ a := by omega
  have hpow4 : 4 ≤ 2 ^ (a - 1) := by
    calc
      (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (a - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hp3 : 3 ≤ p := by omega
  have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hcast_exp : ((a : ℤ) - 1) = ((a - 1 : ℕ) : ℤ) := by omega
  have hc_pos : 0 < cExcess a p := by
    have hp_cast : (2 : ℝ) ^ (a - 1) < (p : ℝ) := by exact_mod_cast hp
    unfold cExcess
    rw [hcast_exp, zpow_natCast]
    linarith
  have hB_nonneg : 0 ≤ Bdef p :=
    le_trans (Real.log_nonneg (by norm_num)) (Bdef_ge_log2 p (by omega))
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hyc_one : Real.exp (-(cExcess a p * lam + (Bdef p + Real.log 2))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have h1 : 0 ≤ cExcess a p * lam := mul_nonneg hc_pos.le hlam.le
    linarith
  -- Bob's first bit: one fiber keeps at least half the columns —
  -- column density `y_p / 2`, i.e. defect budget `+ ln 2`
  obtain ⟨b, hb⟩ := exists_denser_child RC.2 β
  have hKb_cols :
      ((Fintype.card Y : ℝ) ^ p) *
          Real.exp (-(cExcess a p * lam + (Bdef p + Real.log 2))) ≤
        (((RC.2.filter fun c => β c = b).card : ℝ)) := by
    have hsplit :
        Real.exp (-(cExcess a p * lam + (Bdef p + Real.log 2))) =
          Real.exp (-(cExcess a p * lam + Bdef p)) / 2 := by
      rw [show -(cExcess a p * lam + (Bdef p + Real.log 2)) =
          -(cExcess a p * lam + Bdef p) + -Real.log 2 from by ring,
        Real.exp_add, Real.exp_neg (Real.log 2),
        Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      ring
    calc
      ((Fintype.card Y : ℝ) ^ p) *
          Real.exp (-(cExcess a p * lam + (Bdef p + Real.log 2)))
          = (((Fintype.card Y : ℝ) ^ p) *
              Real.exp (-(cExcess a p * lam + Bdef p))) / 2 := by
            rw [hsplit]; ring
      _ ≤ (RC.2.card : ℝ) / 2 := by linarith
      _ ≤ ((RC.2.filter fun c => β c = b).card : ℝ) := hb
  -- maximum projection to `q = ⌈p/2⌉ = (p+1)/2` coordinates, `T = A_a`
  obtain ⟨R', C', hrows', hcols', hDle⟩ :=
    member_max_projection W p ((p + 1) / 2) (rowThreshold (Fintype.card X) x a)
      (Real.exp (-(cExcess a p * lam + (Bdef p + Real.log 2))))
      (by omega) (by omega) (Real.exp_pos _) hyc_one hX hY
      RC.1 (RC.2.filter fun c => β c = b) hrows hKb_cols
  -- the scaled budget: (17) + (18/7)
  have hpz : (2 : ℝ) ^ ((a : ℤ) - 1) < (p : ℝ) := by
    rw [hcast_exp, zpow_natCast]
    exact_mod_cast hp
  have hcc := cExcess_ceil_halving a p (by omega) hpz
  have hBB := Bdef_ceil_halving p hp3
  have hbudget :
      ((((p + 1) / 2 : ℕ) : ℝ) / (p : ℝ)) *
          (cExcess a p * lam + (Bdef p + Real.log 2)) ≤
        cExcess (a - 1) ((p + 1) / 2) * lam + Bdef ((p + 1) / 2) := by
    calc
      ((((p + 1) / 2 : ℕ) : ℝ) / (p : ℝ)) *
          (cExcess a p * lam + (Bdef p + Real.log 2))
          = (((((p + 1) / 2 : ℕ) : ℝ) / (p : ℝ)) * cExcess a p) * lam +
              ((((p + 1) / 2 : ℕ) : ℝ) / (p : ℝ)) * (Bdef p + Real.log 2) := by
            ring
      _ ≤ cExcess (a - 1) ((p + 1) / 2) * lam + Bdef ((p + 1) / 2) :=
        add_le_add (mul_le_mul_of_nonneg_right hcc hlam.le) hBB
  -- projected density dominates the level-(a−1) `(12)` budget
  have hrpow_eq :
      Real.rpow (Real.exp (-(cExcess a p * lam + (Bdef p + Real.log 2))))
          ((((p + 1) / 2 : ℕ) : ℝ) / (p : ℝ)) =
        Real.exp (-(cExcess a p * lam + (Bdef p + Real.log 2)) *
          ((((p + 1) / 2 : ℕ) : ℝ) / (p : ℝ))) := by
    change (Real.exp _) ^ ((((p + 1) / 2 : ℕ) : ℝ) / (p : ℝ)) = _
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  have hdens :
      Real.exp (-(cExcess (a - 1) ((p + 1) / 2) * lam + Bdef ((p + 1) / 2))) ≤
        Real.rpow (Real.exp (-(cExcess a p * lam + (Bdef p + Real.log 2))))
          ((((p + 1) / 2 : ℕ) : ℝ) / (p : ℝ)) := by
    rw [hrpow_eq, Real.exp_le_exp,
      show -(cExcess a p * lam + (Bdef p + Real.log 2)) *
          ((((p + 1) / 2 : ℕ) : ℝ) / (p : ℝ)) =
        -(((((p + 1) / 2 : ℕ) : ℝ) / (p : ℝ)) *
          (cExcess a p * lam + (Bdef p + Real.log 2))) from by ring]
    linarith
  -- the projected child is a `(12)`-state at level `a−1`
  have hmem' : (R', C') ∈ obdState X Y ((p + 1) / 2) (a - 1) x lam := by
    refine ⟨?_, ?_⟩
    · intro j hj
      exact le_trans
        (rowThreshold_mono (Fintype.card X) x hx0.le (by omega : a - 1 ≤ a))
        (hrows' j hj)
    · calc
        ((Fintype.card Y : ℝ) ^ ((p + 1) / 2)) *
            Real.exp (-(cExcess (a - 1) ((p + 1) / 2) * lam +
              Bdef ((p + 1) / 2)))
            ≤ ((Fintype.card Y : ℝ) ^ ((p + 1) / 2)) *
                Real.rpow
                  (Real.exp (-(cExcess a p * lam + (Bdef p + Real.log 2))))
                  ((((p + 1) / 2 : ℕ) : ℝ) / (p : ℝ)) :=
          mul_le_mul_of_nonneg_left hdens (by positivity)
        _ ≤ (C'.card : ℝ) := hcols'
  -- IH at `q > 2^(a-2)`, then Bob's bit closes
  have hq_big : 2 ^ (a - 2) < (p + 1) / 2 :=
    two_pow_pred_lt_ceil_half a p ha2 hp
  have hIH := IH ((p + 1) / 2) hq_big (R', C') hmem'
  calc
    C + (a - 1) = (C + (a - 2)) + 1 := by omega
    _ ≤ D (subgame (interlaceFun W ((p + 1) / 2)) R' C') + 1 :=
      Nat.add_le_add_right hIH 1
    _ ≤ D (subgame (interlaceFun W p) RC.1
          (RC.2.filter fun c => β c = b)) + 1 :=
      Nat.add_le_add_right hDle 1
    _ ≤ D (subgame (interlaceFun W p) RC.1 RC.2) := hchild b

/-! ## `eth:thm-obd` — the one-bit-down statement (12) → (13)

Note §4: "For `a ≥ 2`, every state with `p > 2^(a-1)`, at least `A_a` rows
in every active block, and `Def(K) ≤ c_a(p)λ + B(p)` (12) has complexity at
least `C+a-1` (13)."

Proof route: induction on `a` from `a = 2` (`Nat.le_induction`), with `p`
universally quantified inside the induction.
* `a = 2`: `one_bit_down_base`.
* `a+1 ≥ 3`: the state is nonconstant (`nonconstant`, Bases.lean:390 —
  its `hrows`/`hcols` are literally the `obdState` conjuncts), so
  `subgame_first_bit_dichotomy` yields Alice's or Bob's first bit; route to
  `one_bit_down_alice` / `one_bit_down_bob` with the inductive hypothesis.

JUDGE FLAGS.
* Conclusion `C + (a - 1)` uses ℕ-subtraction; `ha : 2 ≤ a` keeps it
  faithful (`a - 1 ≥ 1`).
* Hypothesis set is the UNION of the branch needs: `hx ≤ 1/4`, `hmargin`,
  `hTwo`, `hC : 3 ≤ C` (base + nonconstancy), `hx0`, `hlam`, `hX`, `hY`
  (steps). The note's §2 `2^a·x ≤ 1` is not needed (see file header).
* Per-member form, matching Theorem 1's per-restriction phrasing; E3
  (`eth:thm-main`) consumes this at its `a ≥ 2` Bob case and via its own
  Alice recursion. -/

/-- **`eth:thm-obd` (note §4, the auxiliary one-bit-down statement,
(12)→(13)).** For `a ≥ 2` and `p > 2^(a-1)`, every `(12)`-state at level `a`
has communication complexity at least `C + a - 1`. -/
theorem one_bit_down {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (C p a : ℕ) (x y lam : ℝ)
    (ha : 2 ≤ a) (hp : 2 ^ (a - 1) < p)
    (hx0 : 0 < x) (hx : x ≤ 1 / 4) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hlam : 0 < lam)
    (hX : 1 ≤ Fintype.card X) (hY : 1 ≤ Fintype.card Y) (hC : 3 ≤ C)
    (hmargin : 3 * lam + (7 / 5) * Real.log 2 ≤ -2 * Real.log y)
    (hTwo : TwoCopyBundle W C x y)
    (RC : Finset (Fin p × X) × Finset (Fin p → Y))
    (hmem : RC ∈ obdState X Y p a x lam) :
    C + (a - 1) ≤ D (subgame (interlaceFun W p) RC.1 RC.2) := by
  classical
  -- strong induction on `a` from `a = 2`, with `p` and the state
  -- universally quantified inside the induction (both steps re-enter the
  -- statement at a different `p'`)
  have H : ∀ a : ℕ, 2 ≤ a → ∀ p : ℕ, 2 ^ (a - 1) < p →
      ∀ RC : Finset (Fin p × X) × Finset (Fin p → Y),
        RC ∈ obdState X Y p a x lam →
        C + (a - 1) ≤ D (subgame (interlaceFun W p) RC.1 RC.2) := by
    intro a ha
    induction a, ha using Nat.le_induction with
    | base =>
        -- `a = 2`: `one_bit_down_base`
        intro p hp RC hmem
        have hp2 : 2 < p := by simpa using hp
        simpa using
          one_bit_down_base W C p x y lam hp2 hx0 hx hy0 hy1 hlam hX hC
            hmargin hTwo RC hmem
    | succ a ha IH =>
        -- `a+1 ≥ 3`: nonconstancy → first bit → Alice/Bob step with the IH
        intro p hp RC hmem
        obtain ⟨hrows, hcols⟩ := hmem
        have hmem' : RC ∈ obdState X Y p (a + 1) x lam := ⟨hrows, hcols⟩
        -- the `(12)` conjuncts are literally `nonconstant`'s hypotheses
        have hpos : 1 ≤ D (subgame (interlaceFun W p) RC.1 RC.2) :=
          nonconstant W C p (a + 1) x y lam (by omega) hp hx0 hx hy0 hy1
            hlam hX hC hmargin hTwo RC hrows hcols
        -- re-shape the IH to the exponent forms the steps expect
        have IH' : ∀ p' : ℕ, 2 ^ (a + 1 - 2) < p' →
            ∀ RC' : Finset (Fin p' × X) × Finset (Fin p' → Y),
              RC' ∈ obdState X Y p' (a + 1 - 1) x lam →
              C + (a + 1 - 2) ≤
                D (subgame (interlaceFun W p') RC'.1 RC'.2) := by
          have e1 : a + 1 - 2 = a - 1 := by omega
          have e2 : a + 1 - 1 = a := by omega
          simp only [e1, e2]
          exact IH
        rcases subgame_first_bit_dichotomy (interlaceFun W p) RC.1 RC.2 hpos
            with ⟨α, hchild⟩ | ⟨β, hchild⟩
        · exact one_bit_down_alice W C p (a + 1) x lam (by omega) hp hlam
            hX hY RC hmem' α hchild IH'
        · exact one_bit_down_bob W C p (a + 1) x lam (by omega) hp hx0 hlam
            hX hY RC hmem' β hchild IH'
  exact H a ha p hp RC hmem

/-! ## Proved glue: `stateDensity ⊆ obdState` (note (5)-adjacent, E3)

The `obdState` inhabitation and statement-fidelity unit tests (BtL discipline)
are discharged in `EthBridge.UnitTests`. The one proved item retained here is
the subset glue lemma E3 consumes, together with its private `B(p) ≥ 0`
helper. -/

/-- `B(p) ≥ 0` for every `p` (at `p = 0` Lean's `6/0 = 0` gives
`Bdef 0 = ln 2 ≥ 0`). -/
private theorem Bdef_nonneg (p : ℕ) : 0 ≤ Bdef p := by
  unfold Bdef
  have hfac : (0 : ℝ) ≤ 1 + 6 / (5 * (p : ℝ)) := by positivity
  exact mul_nonneg hfac (Real.log_nonneg (by norm_num))

/-- Budget sanity (and E3 glue, note (5)-adjacent): every Theorem-1 MAIN
state is in particular a one-bit-down state at the same level — the `(12)`
budget is LARGER by `B(p) ≥ 0`. -/
theorem stateDensity_subset_obdState (X Y : Type*) [Fintype X] [Fintype Y]
    (p a : ℕ) (x lam : ℝ) :
    stateDensity X Y p a x lam ⊆ obdState X Y p a x lam := by
  rintro RC ⟨hrows, hcols⟩
  refine ⟨hrows, le_trans ?_ hcols⟩
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Real.exp_le_exp]
  have := Bdef_nonneg p
  linarith

end EthBridge
