import NPCC.Engine

/-!
# Current paper: two-bound robustness and the two-copy argument

This is a new trace of `papers/interlacing-np-eth/versions/
2026-09-22-complete-replacement-v8`, not a retargeting of attempt-01.
Source anchors: `sections/02-foundations.tex`, `def:paper-robust`, and
`sections/C-classical-calculus.tex`, `app:foundation-two-copy`.

The current definition has TWO one-copy lower bounds.  In particular this
module does not invoke `NPCC.two_copy_ladder`, whose third one-copy premise
is absent from the current paper.  The lowest two-copy bound is obtained by
maximum projection, then the middle and top bounds by first-message analysis.
The existing protocol, matrix, bracket, and family-complexity definitions are
reused without changing their semantics or their integer-ceiling convention.

The only inherited mathematical steps are the concrete matrix projection and
partition recurrences, and the equivalence between typed games and matrices.
There is no claim here about the construction, repeated amplification, or ETH.
-/

namespace EthInapproximability.CurrentPaper

open NPCC
open Workspace.Types.CommComplexity Workspace.Types.Interlace
open Workspace.Types.BoolMat Workspace.Types.Bracket
open Workspace.Types.MatComplexity
open Workspace.Types.Lambda
open Workspace.BracketLemmas Workspace.Appendix

/-- Current-paper robustness at integer depths, `def:paper-robust`.
This is the integer-depth specialization used by the construction.
The value `D f` is the
actual minimum protocol depth.  No bound at column density `3/20` is assumed.
The paper's guard `b ≥ 1` is included in the predicate. -/
def IsRobustAt {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) (b : ℕ) : Prop :=
  1 ≤ b ∧ 2 ≤ D f ∧
    D f ≤ Dfamily (interlaceFun f 1)
      (bracketGE X Y 1 ((2 : ℝ) ^ (-(b : ℝ))) (3 / 5)) ∧
    D f - 1 ≤ Dfamily (interlaceFun f 1)
      (bracketGE X Y 1 ((2 : ℝ) ^ (-(b : ℝ))) (3 / 10))

/-- The literal first-message estimate used twice in the two-copy proof.
The nonconstancy premise prevents applying first-message analysis to a leaf.
It is derived below, not an extra input to the two-copy theorem. -/
theorem twoCopyFirstMessage (M : BoolMat) {x d : ℝ}
    (hx0 : 0 < x) (hx : x ≤ 1 / 2) (hd0 : 0 < d) (hd1 : d ≤ 1)
    (hpos : 1 ≤ DSet (bracket M 2 (2 * x) d)) :
    1 + min (DSet (bracket M 1 x (Real.sqrt d)))
      (DSet (bracket M 2 (2 * x) (d / 2))) ≤
      DSet (bracket M 2 (2 * x) d) := by
  have h := lemma_A1_partition_recurrence M 1 (by omega) 1
    ⟨by norm_num, le_refl _⟩ 0 (by omega) x d ⟨hx0, hx, hd0, hd1⟩ hpos
  norm_num only [Nat.cast_one, Nat.cast_zero, Nat.add_zero, add_zero,
    one_mul, one_add_one_eq_two, sub_self, mul_zero, Nat.floor_zero,
    zero_add] at h
  have hs : Real.rpow d (1 / 2) = Real.sqrt d := by
    exact (Real.sqrt_eq_rpow d).symm
  rw [hs] at h
  simpa only [← min_assoc, min_self] using h

/-- The matrix-form two-copy theorem with only two input rungs.
Source: `app:foundation-two-copy`.  The real level need not be exact. -/
theorem twoCopyBoundsMatrix (M : BoolMat) {x z H : ℝ}
    (hH : 2 ≤ H) (hx0 : 0 < x) (hx : x ≤ 1 / 2)
    (hz0 : 0 < z) (hz1 : z ≤ 1)
    (h1 : H ≤ (DSet (bracket M 1 x z) : ℝ))
    (h2 : H - 1 ≤ (DSet (bracket M 1 x (z / 2)) : ℝ)) :
    H - 1 ≤ (DSet (bracket M 2 (2 * x) (z ^ 2 / 4)) : ℝ) ∧
    H ≤ (DSet (bracket M 2 (2 * x) (z ^ 2 / 2)) : ℝ) ∧
    H + 1 ≤ (DSet (bracket M 2 (2 * x) (z ^ 2)) : ℝ) := by
  have hx1 : x ≤ 1 := by linarith
  have h2x1 : 2 * x ≤ 1 := by linarith
  have hzsq1 : z ^ 2 ≤ 1 := by nlinarith
  have hbottom : H - 1 ≤
      (DSet (bracket M 2 (2 * x) (z ^ 2 / 4)) : ℝ) := by
    have hp := extended_maximum_projection M 2 1 (2 * x) (z ^ 2 / 4)
      (by omega) (by omega) (by positivity)
    norm_num only [Nat.cast_one, Nat.cast_ofNat] at hp
    have hs : Real.rpow (z ^ 2 / 4) (1 / 2) = Real.sqrt (z ^ 2 / 4) := by
      exact (Real.sqrt_eq_rpow (z ^ 2 / 4)).symm
    rw [hs,
      show z ^ 2 / 4 = (z / 2) ^ 2 by ring,
      Real.sqrt_sq (by positivity : 0 ≤ z / 2)] at hp
    rw [show (z / 2) ^ 2 = z ^ 2 / 4 by ring] at hp
    have hm := monotonicity M 1 1 x (2 * x) (z / 2) (z / 2)
      (by omega) (le_refl _) hx0 (by linarith) h2x1
      (by positivity) (le_refl _) (by linarith)
    exact h2.trans (by exact_mod_cast hm.trans hp)
  have hbottom_pos : 1 ≤ DSet (bracket M 2 (2 * x) (z ^ 2 / 4)) := by
    have hh : (1 : ℝ) ≤ (DSet (bracket M 2 (2 * x) (z ^ 2 / 4)) : ℝ) :=
      (by linarith : (1 : ℝ) ≤ H - 1).trans hbottom
    exact_mod_cast hh
  have hmiddle_pos : 1 ≤ DSet (bracket M 2 (2 * x) (z ^ 2 / 2)) := by
    refine hbottom_pos.trans (monotonicity M 2 2 (2 * x) (2 * x)
      (z ^ 2 / 4) (z ^ 2 / 2) (by omega) (le_refl _)
      (by positivity) (le_refl _) h2x1 (by positivity) ?_ ?_)
    · nlinarith [sq_nonneg z]
    · linarith
  have htop_pos : 1 ≤ DSet (bracket M 2 (2 * x) (z ^ 2)) := by
    refine hmiddle_pos.trans (monotonicity M 2 2 (2 * x) (2 * x)
      (z ^ 2 / 2) (z ^ 2) (by omega) (le_refl _)
      (by positivity) (le_refl _) h2x1 (by positivity) ?_ hzsq1)
    nlinarith [sq_nonneg z]
  have hsqrt_lower : z / 2 ≤ Real.sqrt (z ^ 2 / 2) := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ z / 2)]
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg z]
  have hsqrt_upper : Real.sqrt (z ^ 2 / 2) ≤ 1 := by
    rw [Real.sqrt_le_one]
    linarith
  have hmiddle_alice : H - 1 ≤
      (DSet (bracket M 1 x (Real.sqrt (z ^ 2 / 2))) : ℝ) := by
    refine h2.trans ?_
    exact_mod_cast monotonicity M 1 1 x x (z / 2) (Real.sqrt (z ^ 2 / 2))
      (by omega) (le_refl _) hx0 (le_refl _) hx1
      (by positivity) hsqrt_lower hsqrt_upper
  have hmid_step := twoCopyFirstMessage M hx0 hx (by positivity)
    (by linarith : z ^ 2 / 2 ≤ 1) hmiddle_pos
  rw [show z ^ 2 / 2 / 2 = z ^ 2 / 4 by ring] at hmid_step
  have hmid_step_real := (Nat.cast_le (α := ℝ)).mpr hmid_step
  push_cast [Nat.cast_min] at hmid_step_real
  have hmiddle : H ≤ (DSet (bracket M 2 (2 * x) (z ^ 2 / 2)) : ℝ) := by
    have hh := le_min hmiddle_alice hbottom
    linarith
  have htop_step := twoCopyFirstMessage M hx0 hx (by positivity) hzsq1 htop_pos
  rw [Real.sqrt_sq (le_of_lt hz0)] at htop_step
  have htop_step_real := (Nat.cast_le (α := ℝ)).mpr htop_step
  push_cast [Nat.cast_min] at htop_step_real
  refine ⟨hbottom, hmiddle, ?_⟩
  have hh := le_min h1 hmiddle
  linarith

/-- Typed-game form of `app:foundation-two-copy`, with precisely the current
two one-copy hypotheses.  Finite nonempty carriers match the paper's matrix
convention.  The third output rung is proved, not assumed. -/
theorem twoCopyBounds {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (f : X → Y → Bool) {x z H : ℝ}
    (hH : 2 ≤ H) (hx0 : 0 < x) (hx : x ≤ 1 / 2)
    (hz0 : 0 < z) (hz1 : z ≤ 1)
    (h1 : H ≤ (Dfamily (interlaceFun f 1) (bracketGE X Y 1 x z) : ℝ))
    (h2 : H - 1 ≤ (Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (z / 2)) : ℝ)) :
    H - 1 ≤ (Dfamily (interlaceFun f 2)
      (bracketGE X Y 2 (2 * x) (z ^ 2 / 4)) : ℝ) ∧
    H ≤ (Dfamily (interlaceFun f 2)
      (bracketGE X Y 2 (2 * x) (z ^ 2 / 2)) : ℝ) ∧
    H + 1 ≤ (Dfamily (interlaceFun f 2)
      (bracketGE X Y 2 (2 * x) (z ^ 2)) : ℝ) := by
  classical
  let eX : Fin (Fintype.card X) ≃ X := (Fintype.equivFin X).symm
  let eY : Fin (Fintype.card Y) ≃ Y := (Fintype.equivFin Y).symm
  let M : BoolMat := ⟨Fintype.card X, Fintype.card Y, fun i j => f (eX i) (eY j)⟩
  have he : ∀ i j, M.e i j = f (eX i) (eY j) := fun _ _ => rfl
  have hX : 1 ≤ Fintype.card X := Fintype.card_pos
  have transfer (p : ℕ) (a d : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1)
      (hd0 : 0 < d) (hd1 : d ≤ 1) :
      Dfamily (interlaceFun f p) (bracketGE X Y p a d) =
        DSet (bracket M p a d) :=
    Dfamily_eq_DSet f M eX eY he ha0 ha1 hd0 hd1 hX
  have hzsq1 : z ^ 2 ≤ 1 := by nlinarith
  rw [transfer 1 x z hx0 (by linarith) hz0 hz1] at h1
  rw [transfer 1 x (z / 2) hx0 (by linarith) (by positivity) (by linarith)] at h2
  rw [transfer 2 (2 * x) (z ^ 2 / 4) (by positivity) (by linarith)
    (by positivity) (by linarith),
    transfer 2 (2 * x) (z ^ 2 / 2) (by positivity) (by linarith)
    (by positivity) (by linarith),
    transfer 2 (2 * x) (z ^ 2) (by positivity) (by linarith)
    (by positivity) hzsq1]
  exact twoCopyBoundsMatrix M hH hx0 hx hz0 hz1 h1 h2

/-- The natural-number level used by the iterative construction, bundled in
the existing `LambdaGE` readout.  Its inputs remain only two bounds. -/
theorem twoCopyLambda {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (f : X → Y → Bool) {x z : ℝ} {H : ℕ}
    (hH : 2 ≤ H) (hx0 : 0 < x) (hx : x ≤ 1 / 2)
    (hz0 : 0 < z) (hz1 : z ≤ 1)
    (h1 : H ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x z))
    (h2 : H - 1 ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (z / 2))) :
    H + 1 ≤ LambdaGE f 2 (2 * x) (z ^ 2) := by
  have h2r : (H : ℝ) - 1 ≤
      (Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (z / 2)) : ℝ) := by
    have hh := (Nat.cast_le (α := ℝ)).mpr h2
    rw [Nat.cast_sub (by omega : 1 ≤ H), Nat.cast_one] at hh
    exact hh
  obtain ⟨hbottom, hmiddle, htop⟩ := twoCopyBounds f
    (by exact_mod_cast hH) hx0 hx hz0 hz1 (by exact_mod_cast h1) h2r
  unfold LambdaGE
  refine le_min (by exact_mod_cast htop) (le_min ?_ ?_)
  · have hh : H ≤ Dfamily (interlaceFun f 2)
        (bracketGE X Y 2 (2 * x) (z ^ 2 / 2)) := by exact_mod_cast hmiddle
    omega
  · have hh : (H : ℝ) + 1 ≤ 2 +
        (Dfamily (interlaceFun f 2) (bracketGE X Y 2 (2 * x) (z ^ 2 / 4)) : ℝ) := by
      linarith
    exact_mod_cast hh

/-- The first amplification step for exactly the current robustness
definition (`def:paper-robust`), without an inherited third-rung premise. -/
theorem IsRobustAt.twoCopy {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] {f : X → Y → Bool} {b : ℕ}
    (h : IsRobustAt f b) :
    D f + 1 ≤ LambdaGE f 2 (2 * (2 : ℝ) ^ (-(b : ℝ))) (9 / 25) := by
  obtain ⟨hb, hD, htop, hhalf⟩ := h
  have hx0 : 0 < (2 : ℝ) ^ (-(b : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hx : (2 : ℝ) ^ (-(b : ℝ)) ≤ 1 / 2 := by
    calc (2 : ℝ) ^ (-(b : ℝ)) ≤ (2 : ℝ) ^ (-1 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          have hbr : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
          linarith
      _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
  have hhalf' : D f - 1 ≤ Dfamily (interlaceFun f 1)
      (bracketGE X Y 1 ((2 : ℝ) ^ (-(b : ℝ))) ((3 / 5) / 2)) := by
    convert hhalf using 1
    norm_num
  have hh := twoCopyLambda f hD hx0 hx (by norm_num : (0 : ℝ) < 3 / 5)
    (by norm_num : (3 / 5 : ℝ) ≤ 1) htop hhalf'
  norm_num only [show (3 / 5 : ℝ) ^ 2 = 9 / 25 by norm_num] at hh
  exact hh

/-- Boundary guards are simultaneously satisfiable at the paper's values.
This checks arithmetic guards only; a semantic nonvacuity example is separate. -/
theorem twoCopy_numeric_guards :
    (2 : ℝ) ≤ 2 ∧ 0 < (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) ≤ 1 / 2 ∧
    0 < (3 / 5 : ℝ) ∧ (3 / 5 : ℝ) ≤ 1 ∧ ¬ (2 : ℝ) ≤ 1 := by
  norm_num

/-- Matrix-form repeated row doubling at a natural-number certified level.
The initial two-copy theorem supplies
the three output bounds; the inherited row step propagates that output, never
adding a third assumption on the original one-copy restrictions.
Source: `lem:paper-certified-row-ladder`.  The proof also works for `z ≤ 1`;
the source's stronger `z ≤ 1 / sqrt 2` is not needed by the reused row step. -/
theorem repeatedRowDoublingMatrix (M : BoolMat) {x z : ℝ} {H : ℕ}
    (hH : 2 ≤ H) (hx0 : 0 < x) (hz0 : 0 < z) (hz1 : z ≤ 1)
    (h1 : H ≤ DSet (bracket M 1 x z))
    (h2 : H - 1 ≤ DSet (bracket M 1 x (z / 2)))
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hrow : (2 : ℝ) ^ ℓ * x ≤ 1) :
    H + ℓ ≤ Lambda M (2 ^ (ℓ - 1) + 1) ((2 : ℝ) ^ ℓ * x) (z ^ 2) := by
  have hzsq1 : z ^ 2 ≤ 1 := by nlinarith
  have h2r : (H : ℝ) - 1 ≤ (DSet (bracket M 1 x (z / 2)) : ℝ) := by
    have hh := (Nat.cast_le (α := ℝ)).mpr h2
    rw [Nat.cast_sub (by omega : 1 ≤ H), Nat.cast_one] at hh
    exact hh
  have base (hx : x ≤ 1 / 2) :
      H + 1 ≤ Lambda M 2 (2 * x) (z ^ 2) ∧
      1 ≤ DSet (bracket M 2 (2 * x) (z ^ 2 / 4)) := by
    obtain ⟨hb, hm, ht⟩ := twoCopyBoundsMatrix M
      (by exact_mod_cast hH) hx0 hx hz0 hz1 (by exact_mod_cast h1) h2r
    have hb1 : (1 : ℝ) ≤ (DSet (bracket M 2 (2 * x) (z ^ 2 / 4)) : ℝ) := by
      have hHr : (2 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
      linarith
    refine ⟨?_, by exact_mod_cast hb1⟩
    unfold Lambda
    refine le_min (by exact_mod_cast ht) (le_min ?_ ?_)
    · have hmN : H ≤ DSet (bracket M 2 (2 * x) (z ^ 2 / 2)) := by exact_mod_cast hm
      omega
    · have hh : (H : ℝ) + 1 ≤ 2 + (DSet (bracket M 2 (2 * x) (z ^ 2 / 4)) : ℝ) := by
        linarith
      exact_mod_cast hh
  induction ℓ with
  | zero => omega
  | succ n ih =>
    by_cases hn : n = 0
    · subst n
      norm_num at hrow ⊢
      exact (base (by linarith)).1
    · have hn1 : 1 ≤ n := by omega
      have hp : 1 ≤ 2 ^ (n - 1) := Nat.one_le_pow _ _ (by omega)
      have hpR : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
      have hrows : (2 : ℝ) ^ (n + 1) * x = 2 * ((2 : ℝ) ^ n * x) := by
        rw [pow_succ]
        ring
      have hxn0 : 0 < (2 : ℝ) ^ n * x := by positivity
      have hxn : (2 : ℝ) ^ n * x ≤ 1 / 2 := by rw [hrows] at hrow; linarith
      have hx : x ≤ 1 / 2 := by nlinarith
      have hseed := (base hx).2
      have hmono := monotonicity M 2 (2 * 2 ^ (n - 1)) (2 * x)
        (2 * ((2 : ℝ) ^ n * x)) (z ^ 2 / 4) (z ^ 2 / 4)
        (by omega) (by omega) (by positivity) (by nlinarith)
        (by rw [← hrows]; exact hrow) (by positivity) (le_refl _) (by linarith)
      have hstep := lemma_A3_row_ladder_step M (2 ^ (n - 1)) hp 1 (by omega)
        ((2 : ℝ) ^ n * x) (z ^ 2)
        ⟨hxn0, hxn, by positivity, hzsq1⟩ (hseed.trans hmono)
      have hi := ih hn1 (by linarith)
      have hcopies : 2 * 2 ^ (n - 1) = 2 ^ n := by
        rw [← Nat.pow_succ', Nat.succ_eq_add_one, Nat.sub_add_cancel hn1]
      rw [hcopies, ← hrows] at hstep
      simpa only [Nat.add_sub_cancel] using
        (show H + (n + 1) ≤ Lambda M (2 ^ n + 1) ((2 : ℝ) ^ (n + 1) * x) (z ^ 2) by
          omega)

/-- Typed current-paper row ladder at a natural-number certified level, from
TWO initial one-copy bounds.
This is `lem:paper-certified-row-ladder`, with a slightly weaker density
guard `z ≤ 1` justified by the existing three-rung row step. -/
theorem repeatedRowDoubling {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (f : X → Y → Bool) {x z : ℝ} {H : ℕ}
    (hH : 2 ≤ H) (hx0 : 0 < x) (hz0 : 0 < z) (hz1 : z ≤ 1)
    (h1 : H ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x z))
    (h2 : H - 1 ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (z / 2)))
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hrow : (2 : ℝ) ^ ℓ * x ≤ 1) :
    H + ℓ ≤ LambdaGE f (2 ^ (ℓ - 1) + 1) ((2 : ℝ) ^ ℓ * x) (z ^ 2) := by
  classical
  let eX : Fin (Fintype.card X) ≃ X := (Fintype.equivFin X).symm
  let eY : Fin (Fintype.card Y) ≃ Y := (Fintype.equivFin Y).symm
  let M : BoolMat := ⟨Fintype.card X, Fintype.card Y, fun i j => f (eX i) (eY j)⟩
  have he : ∀ i j, M.e i j = f (eX i) (eY j) := fun _ _ => rfl
  have hX : 1 ≤ Fintype.card X := Fintype.card_pos
  have hx1 : x ≤ 1 := by
    have hh : (1 : ℝ) ≤ (2 : ℝ) ^ ℓ := one_le_pow₀ (by norm_num)
    nlinarith
  rw [Dfamily_eq_DSet f M eX eY he hx0 hx1 hz0 hz1 hX] at h1
  rw [Dfamily_eq_DSet f M eX eY he hx0 hx1 (by positivity)
    (by linarith : z / 2 ≤ 1) hX] at h2
  rw [LambdaGE_eq_Lambda f M eX eY he (by positivity) hrow
    (by positivity) (by nlinarith : z ^ 2 ≤ 1) hX]
  exact repeatedRowDoublingMatrix M hH hx0 hz0 hz1 h1 h2 ℓ hℓ hrow

/-- Copy-count monotonicity on the concrete typed restriction families.
This is the fixed-density case of `prop:paper-projection-facts`, part 2. -/
theorem restrictionCost_mono_copies {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (f : X → Y → Bool) {p q : ℕ} {x z : ℝ}
    (hp : 1 ≤ p) (hpq : p ≤ q) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hz0 : 0 < z) (hz1 : z ≤ 1) :
    Dfamily (interlaceFun f p) (bracketGE X Y p x z) ≤
      Dfamily (interlaceFun f q) (bracketGE X Y q x z) := by
  classical
  let eX : Fin (Fintype.card X) ≃ X := (Fintype.equivFin X).symm
  let eY : Fin (Fintype.card Y) ≃ Y := (Fintype.equivFin Y).symm
  let M : BoolMat := ⟨Fintype.card X, Fintype.card Y, fun i j => f (eX i) (eY j)⟩
  have he : ∀ i j, M.e i j = f (eX i) (eY j) := fun _ _ => rfl
  have hX : 1 ≤ Fintype.card X := Fintype.card_pos
  rw [Dfamily_eq_DSet f M eX eY he hx0 hx1 hz0 hz1 hX,
    Dfamily_eq_DSet f M eX eY he hx0 hx1 hz0 hz1 hX]
  exact monotonicity M p q x x z z hp hpq hx0 (le_refl _) hx1 hz0 (le_refl _) hz1

/-- The power-of-two consequence of the new two-bound row ladder.
Source: `thm:paper-classical-amplification`, part 2, in exponent form. -/
theorem repeatedPowerOfTwo {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (f : X → Y → Bool) {x z : ℝ} {H : ℕ}
    (hH : 2 ≤ H) (hx0 : 0 < x) (hz0 : 0 < z) (hz1 : z ≤ 1)
    (h1 : H ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x z))
    (h2 : H - 1 ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (z / 2)))
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hrow : (2 : ℝ) ^ ℓ * x ≤ 1) :
    H + ℓ ≤ Dfamily (interlaceFun f (2 ^ ℓ))
      (bracketGE X Y (2 ^ ℓ) ((2 : ℝ) ^ ℓ * x) (z ^ 2)) := by
  have hh := repeatedRowDoubling f hH hx0 hz0 hz1 h1 h2 ℓ hℓ hrow
  have htop : H + ℓ ≤ Dfamily (interlaceFun f (2 ^ (ℓ - 1) + 1))
      (bracketGE X Y (2 ^ (ℓ - 1) + 1) ((2 : ℝ) ^ ℓ * x) (z ^ 2)) :=
    hh.trans (min_le_left _ _)
  have hp : 1 ≤ 2 ^ (ℓ - 1) := Nat.one_le_pow _ _ (by omega)
  have hpow : 2 * 2 ^ (ℓ - 1) = 2 ^ ℓ := by
    rw [← Nat.pow_succ', Nat.succ_eq_add_one, Nat.sub_add_cancel hℓ]
  exact htop.trans (restrictionCost_mono_copies f (by omega) (by omega)
    (by positivity) hrow (by positivity) (by nlinarith))

/-- Both advertised block-count bounds follow from the current robustness
definition.  Writing a power of two as `2^k` avoids any logarithm convention.
The first bound is valid already at `k=1` (where the block count is two).
Source: `thm:paper-classical-amplification`, `eq:paper-odd-copy`,
and `eq:paper-power-two`. -/
theorem IsRobustAt.classicalAmplification {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] {f : X → Y → Bool} {b : ℕ}
    (h : IsRobustAt f b) (k : ℕ) (hk : 1 ≤ k) (hkb : k ≤ b) :
    D f + k ≤ LambdaGE f (2 ^ (k - 1) + 1)
      ((2 : ℝ) ^ ((k : ℝ) - (b : ℝ))) (9 / 25) ∧
    D f + k ≤ Dfamily (interlaceFun f (2 ^ k))
      (bracketGE X Y (2 ^ k) ((2 : ℝ) ^ ((k : ℝ) - (b : ℝ))) (9 / 25)) := by
  obtain ⟨_, hD, htop, hhalf⟩ := h
  have hx0 : 0 < (2 : ℝ) ^ (-(b : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have heq : (2 : ℝ) ^ k * (2 : ℝ) ^ (-(b : ℝ)) =
      (2 : ℝ) ^ ((k : ℝ) - (b : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
  have hrow : (2 : ℝ) ^ k * (2 : ℝ) ^ (-(b : ℝ)) ≤ 1 := by
    rw [heq]
    calc (2 : ℝ) ^ ((k : ℝ) - (b : ℝ)) ≤ (2 : ℝ) ^ (0 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          have hh : (k : ℝ) ≤ (b : ℝ) := by exact_mod_cast hkb
          linarith
      _ = 1 := Real.rpow_zero _
  have hhalf' : D f - 1 ≤ Dfamily (interlaceFun f 1)
      (bracketGE X Y 1 ((2 : ℝ) ^ (-(b : ℝ))) ((3 / 5) / 2)) := by
    convert hhalf using 1
    norm_num
  have ha := repeatedRowDoubling f hD hx0 (by norm_num : (0 : ℝ) < 3 / 5)
    (by norm_num : (3 / 5 : ℝ) ≤ 1) htop hhalf' k hk hrow
  have hb := repeatedPowerOfTwo f hD hx0 (by norm_num : (0 : ℝ) < 3 / 5)
    (by norm_num : (3 / 5 : ℝ) ≤ 1) htop hhalf' k hk hrow
  rw [heq, show (3 / 5 : ℝ) ^ 2 = 9 / 25 by norm_num] at ha hb
  exact ⟨ha, hb⟩

/-! ## Concrete nonvacuity checks

The equality matrix on three symbols satisfies the two-copy input hypotheses
at `H = 2`, `x = 1/2`, `z = 1`.  This tests the general two-copy theorem,
not the stronger exact-cost `IsRobustAt` predicate at fixed density `3/5`.
Finite rectangle facts are checked by the kernel's `decide` tactic.
-/

namespace SanityChecks

open Workspace.Types.Protocol

theorem eval_const_of_cost_zero {A B Z : Type*} (P : Protocol A B Z)
    (h : P.cost = 0) : ∃ z, ∀ a b, P.eval a b = z := by
  cases P with
  | leaf z => exact ⟨z, fun _ _ => rfl⟩
  | aNode a l r => simp [Protocol.cost] at h
  | bNode b l r => simp [Protocol.cost] at h

theorem one_le_D_of_two_values_local {A B : Type*} [Fintype A] [Fintype B]
    (g : A → B → Bool) {a₁ a₂ : A} {b₁ b₂ : B}
    (hne : g a₁ b₁ ≠ g a₂ b₂) : 1 ≤ D g := by
  by_contra h
  have hzero : D g = 0 := by omega
  have hm : D g ∈ AchievableCosts g :=
    Nat.sInf_mem (Workspace.UpperBound.AchievableCosts_nonempty g)
  obtain ⟨P, hcost, hcomp⟩ := hm
  obtain ⟨z, hz⟩ := eval_const_of_cost_zero P (hcost.trans hzero)
  exact hne ((hcomp a₁ b₁).symm.trans ((hz a₁ b₁).trans
    ((hz a₂ b₂).symm.trans (hcomp a₂ b₂))))

theorem two_le_D_of_variations {A B : Type*} [Fintype A] [Fintype B]
    (g : A → B → Bool)
    (hr : ∃ a b₀ b₁, g a b₀ ≠ g a b₁)
    (hc : ∃ a₀ a₁ b, g a₀ b ≠ g a₁ b) : 2 ≤ D g := by
  obtain ⟨a, b₀, b₁, hab⟩ := hr
  obtain ⟨a₀, a₁, b, hba⟩ := hc
  by_contra h
  have hd : D g ≤ 1 := by omega
  have hm : D g ∈ AchievableCosts g :=
    Nat.sInf_mem (Workspace.UpperBound.AchievableCosts_nonempty g)
  obtain ⟨P, hcost, hcomp⟩ := hm
  cases P with
  | leaf z => exact hab ((hcomp a b₀).symm.trans (hcomp a b₁))
  | aNode q l r =>
    have hl : l.cost = 0 := by simp only [Protocol.cost] at hcost; omega
    have hr : r.cost = 0 := by simp only [Protocol.cost] at hcost; omega
    obtain ⟨zl, hzl⟩ := eval_const_of_cost_zero l hl
    obtain ⟨zr, hzr⟩ := eval_const_of_cost_zero r hr
    have e₀ := hcomp a b₀
    have e₁ := hcomp a b₁
    simp only [Protocol.eval, hzl, hzr] at e₀ e₁
    exact hab (e₀.symm.trans e₁)
  | bNode q l r =>
    have hl : l.cost = 0 := by simp only [Protocol.cost] at hcost; omega
    have hr : r.cost = 0 := by simp only [Protocol.cost] at hcost; omega
    obtain ⟨zl, hzl⟩ := eval_const_of_cost_zero l hl
    obtain ⟨zr, hzr⟩ := eval_const_of_cost_zero r hr
    have e₀ := hcomp a₀ b
    have e₁ := hcomp a₁ b
    simp only [Protocol.eval, hzl, hzr] at e₀ e₁
    exact hba (e₀.symm.trans e₁)

def eqThree (a b : Fin 3) : Bool := decide (a = b)

theorem eqThree_finite_full :
    ∀ R ∈ (Finset.univ : Finset (Fin 1 × Fin 3)).powerset,
    ∀ C ∈ (Finset.univ : Finset (Fin 1 → Fin 3)).powerset,
      2 ≤ R.card → 3 ≤ C.card →
      (∃ a ∈ R, ∃ b₀ ∈ C, ∃ b₁ ∈ C,
        interlaceFun eqThree 1 a b₀ ≠ interlaceFun eqThree 1 a b₁) ∧
      (∃ a₀ ∈ R, ∃ a₁ ∈ R, ∃ b ∈ C,
        interlaceFun eqThree 1 a₀ b ≠ interlaceFun eqThree 1 a₁ b) := by
  decide

theorem eqThree_finite_half :
    ∀ R ∈ (Finset.univ : Finset (Fin 1 × Fin 3)).powerset,
    ∀ C ∈ (Finset.univ : Finset (Fin 1 → Fin 3)).powerset,
      2 ≤ R.card → 2 ≤ C.card →
      ∃ a₀ ∈ R, ∃ a₁ ∈ R, ∃ b₀ ∈ C, ∃ b₁ ∈ C,
        interlaceFun eqThree 1 a₀ b₀ ≠ interlaceFun eqThree 1 a₁ b₁ := by
  decide

theorem eqThree_full_bound :
    2 ≤ Dfamily (interlaceFun eqThree 1)
      (bracketGE (Fin 3) (Fin 3) 1 (1/2) 1) := by
  classical
  apply le_csInf
  · obtain ⟨RC, hRC⟩ := bracketGE.nonempty (X := Fin 3) (Y := Fin 3)
      1 (1/2) 1 (by norm_num) (by norm_num) (by norm_num)
    exact ⟨_, RC, hRC, rfl⟩
  · rintro n ⟨⟨R,C⟩, ⟨hR,hC⟩, rfl⟩
    have hr := hR 0 (Finset.mem_univ 0)
    have hrf : R.filter (fun p => p.1 = (0 : Fin 1)) = R := by
      apply Finset.filter_eq_self.mpr
      intro x hx
      exact Subsingleton.elim _ _
    rw [hrf] at hr
    norm_num at hr hC
    have hv := eqThree_finite_full R (by simp) C (by simp) hr hC
    obtain ⟨⟨a,ha,b₀,hb₀,b₁,hb₁,hab⟩,⟨a₀,ha₀,a₁,ha₁,b,hb,hba⟩⟩ := hv
    exact two_le_D_of_variations _
      ⟨⟨a,ha⟩,⟨b₀,hb₀⟩,⟨b₁,hb₁⟩,hab⟩
      ⟨⟨a₀,ha₀⟩,⟨a₁,ha₁⟩,⟨b,hb⟩,hba⟩

theorem eqThree_half_bound :
    1 ≤ Dfamily (interlaceFun eqThree 1)
      (bracketGE (Fin 3) (Fin 3) 1 (1/2) (1/2)) := by
  classical
  apply le_csInf
  · obtain ⟨RC, hRC⟩ := bracketGE.nonempty (X := Fin 3) (Y := Fin 3)
      1 (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num)
    exact ⟨_, RC, hRC, rfl⟩
  · rintro n ⟨⟨R,C⟩, ⟨hR,hC⟩, rfl⟩
    have hr := hR 0 (Finset.mem_univ 0)
    have hrf : R.filter (fun p => p.1 = (0 : Fin 1)) = R := by
      apply Finset.filter_eq_self.mpr
      intro x hx
      exact Subsingleton.elim _ _
    rw [hrf] at hr
    norm_num at hr hC
    obtain ⟨a₀,ha₀,a₁,ha₁,b₀,hb₀,b₁,hb₁,hab⟩ :=
      eqThree_finite_half R (by simp) C (by simp) hr hC
    exact one_le_D_of_two_values_local _
      (a₁ := ⟨a₀,ha₀⟩) (a₂ := ⟨a₁,ha₁⟩)
      (b₁ := ⟨b₀,hb₀⟩) (b₂ := ⟨b₁,hb₁⟩) hab

theorem twoCopy_at_eqThree :
    3 ≤ LambdaGE eqThree 2 1 1 := by
  have h := twoCopyLambda eqThree (by norm_num : 2 ≤ (2 : ℕ))
    (by norm_num : (0 : ℝ) < 1 / 2) (le_refl _)
    (by norm_num : (0 : ℝ) < 1) (le_refl _)
    eqThree_full_bound eqThree_half_bound
  norm_num at h ⊢
  exact h

end SanityChecks

end EthInapproximability.CurrentPaper
