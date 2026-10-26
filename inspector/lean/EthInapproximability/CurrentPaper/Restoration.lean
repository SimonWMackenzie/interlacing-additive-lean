import EthInapproximability.CurrentPaper.Foundations
import EthInapproximability.CurrentPaper.Parameters
import EthInapproximability.ParameterizedNP.DirectOutputLower

/-!
# Robustness restoration for the current interlacing construction

Source: v8 `04-bridge.tex`, `eq:bridge-common-input`,
`thm:near-to-robust`, `eq:bridge-output`, `eq:bridge-carriers`, and
`cor:one-level-amplifier`.

The output is literally the transpose of the full power-of-two interlace.
The input consists of the actual three restriction bounds printed in the
paper: one near-full bound and TWO moderate-density bounds. The current
two-copy lemma supplies the bundle needed by the independently proved generic
column-loss induction in `EthBridge.Entry`. No third one-copy assumption,
older parameter search, or protected-hardness certificate is imported.

The generic entry proof uses natural logarithms and an internal ceiling of
`b*log(2)/(-log(1-delta))`; these are proof-local parameters, not changes to
the output matrix or to the current width. Its numerical premises are derived
from exactly the current gates `80*b <= 2^r*delta`, `delta <= 1/64`, and
`2^r*theta < 1/20`. Minimality of the chosen power of two is unnecessary for
the conclusion, so the theorem also holds for any power meeting those gates.

The source-dependent proof that the constructed W satisfies the input profiles
remains separate. This module is the full universal restoration implication,
not an assertion that the protected-matrix obligation has already been closed.
-/

namespace EthInapproximability.CurrentPaper.Restoration

open NPCC
open Workspace.Types.Interlace Workspace.Types.CommComplexity
open EthInapproximability.ParameterizedNP
open EthInapproximability.ParameterizedNP.EntryGates
open EthInapproximability.ParameterizedNP.DirectOutputLower

/-- The exact matrix `Int_(2^r)(W)^T`, with its actual finite input types. -/
def output {X Y : Type*} (W : X → Y → Bool) (r : ℕ) :
    (Fin (2 ^ r) → Y) → (Fin (2 ^ r) × X) → Bool :=
  EthBridge.Rnext W (2 ^ r)

@[simp] theorem output_apply {X Y : Type*} (W : X → Y → Bool) (r : ℕ)
    (γ : Fin (2 ^ r) → Y) (i : Fin (2 ^ r)) (x : X) :
    output W r γ (i, x) = W x (γ i) := rfl

theorem output_eq_transpose {X Y : Type*} (W : X → Y → Bool) (r : ℕ) :
    output W r = fun γ row => interlaceFun W (2 ^ r) row γ := rfl

theorem output_upper {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (r : ℕ) : D (output W r) ≤ D W + r := by
  change D (fun γ row => interlaceFun W (2 ^ r) row γ) ≤ _
  rw [comp_transpose]
  exact powerOfTwoInterlace_upper W r

theorem output_upper_of_bound {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → Bool) (r U : ℕ) (hU : D W ≤ U) :
    D (output W r) ≤ U + r :=
  (output_upper W r).trans (Nat.add_le_add_right hU r)

theorem output_rows {Y : Type*} [Fintype Y] (r : ℕ) :
    Fintype.card (Fin (2 ^ r) → Y) = Fintype.card Y ^ (2 ^ r) := by simp

theorem output_columns {X : Type*} [Fintype X] (r : ℕ) :
    Fintype.card (Fin (2 ^ r) × X) = 2 ^ r * Fintype.card X := by simp

/-- The old numeric dyadic notation is exactly the current robustness density. -/
theorem density_eq_rpow (b : ℕ) : xOut b = (2 : ℝ) ^ (-(b : ℝ)) := by
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  rfl

/-- Derive the required TWO-copy package from only the current TWO one-copy
moderate-density bounds. This is not the old three-input ladder. -/
theorem two_copy_input {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (W : X → Y → Bool) (C : ℕ) {θ : ℝ}
    (hC : 3 ≤ C) (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 4)
    (hmoderate : C - 1 ≤ Dfamily (interlaceFun W 1) (bracketGE X Y 1 θ (3 / 5)))
    (hhalf : C - 2 ≤ Dfamily (interlaceFun W 1) (bracketGE X Y 1 θ (3 / 10))) :
    EthBridge.TwoCopyBundle W C θ (3 / 5) := by
  have hh : (C - 1) - 1 ≤ Dfamily (interlaceFun W 1)
      (bracketGE X Y 1 θ ((3 / 5) / 2)) := by
    norm_num only [show (3 / 5 : ℝ) / 2 = 3 / 10 by norm_num]
    omega
  have h := twoCopyLambda W (H := C - 1) (by omega) hθ0 (by linarith)
    (by norm_num : (0 : ℝ) < 3 / 5) (by norm_num : (3 / 5 : ℝ) ≤ 1)
    hmoderate hh
  unfold EthBridge.TwoCopyBundle
  omega

/-- The current numerical gates imply every premise of the generic
column-loss entry theorem. The auxiliary `1/10` is the margin `3/5-1/2`,
not the deletion tolerance `delta`. -/
theorem numerical_gates {b r : ℕ} {δ θ : ℝ}
    (hb : 1 ≤ b) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 64) (hθ0 : 0 < θ)
    (hwidth : 80 * (b : ℝ) ≤ (2 : ℝ) ^ r * δ)
    (hscale : (2 : ℝ) ^ r * θ < 1 / 20) :
    4 ≤ r ∧ θ ≤ 1 / 4 ∧ 0 < lambdaU δ ∧
    (3 * lambdaU δ + (7 / 5) * Real.log 2 ≤ -2 * Real.log (3 / 5)) ∧
    (8 * EthBridge.entryDefect (xOut b) / ((1 / 10) * lambdaU δ) ≤ (2 : ℝ) ^ r) ∧
    (8 / (1 / 10) ≤ (2 : ℝ) ^ r) ∧
    ((2 : ℝ) ^ r * θ < (1 / 10) / 2) ∧
    (∀ t : ℕ, (2 : ℝ) ^ (r - t) * θ ≤ 1) := by
  have hδ1 : δ < 1 := by linarith
  have hlam := (lambdaU_spec hδ0 hδ1).2
  have hbR : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hQpos : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
  have hQ5120 : (5120 : ℝ) ≤ (2 : ℝ) ^ r := by
    nlinarith [mul_nonneg hQpos.le (sub_nonneg.mpr hδ)]
  have hr : 4 ≤ r := by
    by_contra hn
    have hr3 : r ≤ 3 := by omega
    have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hr3
    norm_num at hp
    linarith
  have hθ : θ ≤ 1 / 4 := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ (2 : ℝ) ^ r - 1 by linarith) hθ0.le]
  have hmargin := secondEntryGate_of_deltaU_small hδ0 (show δ ≤ 1 / 60 by linarith)
  have hQL :
      8 * EthBridge.entryDefect (xOut b) / ((1 / 10) * lambdaU δ) ≤ (2 : ℝ) ^ r := by
    rw [div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 1 / 10) hlam)]
    have hL : EthBridge.entryDefect (xOut b) ≤ (b : ℝ) := by
      rw [entryDefect_eq]
      exact entryDefectL_le_depth b
    have hdeltalam := deltaU_le_lambdaU hδ1
    nlinarith [mul_nonneg hQpos.le (sub_nonneg.mpr hdeltalam)]
  refine ⟨hr, hθ, hlam, hmargin, hQL, ?_, ?_, ?_⟩
  · norm_num
    linarith
  · norm_num at hscale ⊢
    exact hscale
  · intro t
    have hp : (2 : ℝ) ^ (r - t) ≤ (2 : ℝ) ^ r :=
      pow_le_pow_right₀ (by norm_num) (Nat.sub_le r t)
    have hm := mul_le_mul_of_nonneg_right hp hθ0.le
    linarith

/-- The exact finite entry count, including all ceiling corrections, is
derived simultaneously for the three output restriction fractions. -/
theorem entry_gates {b r m : ℕ} {δ θ : ℝ}
    (hb : 1 ≤ b) (hm : 1 ≤ m) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 64)
    (hθ0 : 0 < θ) (hwidth : 80 * (b : ℝ) ≤ (2 : ℝ) ^ r * δ)
    (hscale : (2 : ℝ) ^ r * θ < 1 / 20) :
    ∀ t : ℕ, t ≤ 2 →
      EthBridge.entryCopies r t (xOut b) (lambdaU δ) ≤ 2 ^ r ∧
      ((EthBridge.entryRowBound (2 ^ r) m
          (EthBridge.entryCopies r t (xOut b) (lambdaU δ))
          (EthBridge.rowThreshold m θ (EthBridge.entryLevel r t)) : ℕ) : ℝ)
        < (2 : ℝ) ^ r * (m : ℝ) * (3 / 5) / 2 ^ t := by
  obtain ⟨hr, _, hlam, _, hQL, hQδ, hQθ, _⟩ :=
    numerical_gates hb hδ0 hδ hθ0 hwidth hscale
  exact EthBridge.uniform_package r m θ (lambdaU δ) (xOut b) (1 / 10) (3 / 5)
    hr hm (by norm_num) (by norm_num) (by norm_num) hlam hθ0
    (xOut_pos b) (xOut_lt_one hb) hQL hQδ hQθ

/-- Every one-copy restriction of the literal output has the stated lower
bound. The only matrix premises are the three current-paper input profiles. -/
theorem output_rung {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (W : X → Y → Bool) (C b r : ℕ) {δ θ : ℝ}
    (hC : 3 ≤ C) (hb : 1 ≤ b) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 64)
    (hθ0 : 0 < θ) (hwidth : 80 * (b : ℝ) ≤ (2 : ℝ) ^ r * δ)
    (hscale : (2 : ℝ) ^ r * θ < 1 / 20)
    (hnear : C ≤ Dfamily (interlaceFun W 1) (bracketGE X Y 1 θ (1 - δ)))
    (hmoderate : C - 1 ≤ Dfamily (interlaceFun W 1) (bracketGE X Y 1 θ (3 / 5)))
    (hhalf : C - 2 ≤ Dfamily (interlaceFun W 1) (bracketGE X Y 1 θ (3 / 10)))
    (t : ℕ) (ht : t ≤ 2) :
    C + (r - t) ≤ Dfamily (interlaceFun (output W r) 1)
      (bracketGE (Fin (2 ^ r) → Y) (Fin (2 ^ r) × X) 1 (xOut b) ((3 / 5) / 2 ^ t)) := by
  obtain ⟨hr, hθ, hlam, hmargin, _, _, _, hrow⟩ :=
    numerical_gates hb hδ0 hδ hθ0 hwidth hscale
  obtain ⟨hpQ, hcount⟩ :=
    entry_gates hb (Fintype.card_pos : 1 ≤ Fintype.card X)
      hδ0 hδ hθ0 hwidth hscale t ht
  have hnear' : EthBridge.NearFull W C θ (lambdaU δ) := by
    unfold EthBridge.NearFull
    rw [(lambdaU_spec hδ0 (by linarith : δ < 1)).1]
    exact hnear
  exact EthBridge.theorem_two W C r t θ (3 / 5) (lambdaU δ) (xOut b)
    hr ht (xOut_pos b) (xOut_lt_one hb) (hrow t) hθ0 hθ (by norm_num)
    (by norm_num) hlam Fintype.card_pos Fintype.card_pos hC hmargin hnear'
    (two_copy_input W C hC hθ0 hθ hmoderate hhalf) hpQ hcount

/-- Full current-paper robustness restoration, including exact complexity and
the stronger third restriction bound. All conclusions concern one literal
matrix. The actual proof of its input profiles belongs upstream. -/
theorem restore {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (W : X → Y → Bool) (C b r : ℕ) {δ θ : ℝ}
    (hcost : D W = C) (hC : 3 ≤ C) (hb : 1 ≤ b)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 64) (hθ0 : 0 < θ)
    (hwidth : 80 * (b : ℝ) ≤ (2 : ℝ) ^ r * δ)
    (hscale : (2 : ℝ) ^ r * θ < 1 / 20)
    (hnear : C ≤ Dfamily (interlaceFun W 1) (bracketGE X Y 1 θ (1 - δ)))
    (hmoderate : C - 1 ≤ Dfamily (interlaceFun W 1) (bracketGE X Y 1 θ (3 / 5)))
    (hhalf : C - 2 ≤ Dfamily (interlaceFun W 1) (bracketGE X Y 1 θ (3 / 10))) :
    D (output W r) = C + r ∧ IsRobustAt (output W r) b ∧
      C + r ≤ LambdaGE (output W r) 1 ((2 : ℝ) ^ (-(b : ℝ))) (3 / 5) := by
  classical
  have hr := (numerical_gates hb hδ0 hδ hθ0 hwidth hscale).1
  have h0 := output_rung W C b r hC hb hδ0 hδ hθ0 hwidth hscale
    hnear hmoderate hhalf 0 (by omega)
  have h1 := output_rung W C b r hC hb hδ0 hδ hθ0 hwidth hscale
    hnear hmoderate hhalf 1 (by omega)
  have h2 := output_rung W C b r hC hb hδ0 hδ hθ0 hwidth hscale
    hnear hmoderate hhalf 2 (by omega)
  norm_num only [Nat.sub_zero, pow_zero, div_one] at h0
  have hne : (bracketGE (Fin (2 ^ r) → Y) (Fin (2 ^ r) × X)
      1 (xOut b) ((3 : ℝ) / 5)).Nonempty :=
    bracketGE.nonempty 1 (xOut b) (3 / 5) (xOut_le_one b) (by norm_num)
      Fintype.card_pos
  have hlow := familyComplexity_le_ambient (interlaceFun (output W r) 1) hne
  have hone : D (interlaceFun (output W r) 1) ≤ D (output W r) := by
    simpa using powerOfTwoInterlace_upper (output W r) 0
  have hupper := output_upper W r
  have hEq : D (output W r) = C + r := by omega
  rw [density_eq_rpow] at h0 h1 h2
  refine ⟨hEq, ?_, ?_⟩
  · refine ⟨hb, by omega, ?_, ?_⟩
    · rw [hEq]
      exact h0
    · norm_num only [pow_one, show (3 / 5 : ℝ) / 2 = 3 / 10 by norm_num] at h1
      rw [hEq]
      omega
  · unfold LambdaGE
    refine le_min h0 (le_min ?_ ?_)
    · norm_num at h1 ⊢
      omega
    · norm_num at h2 ⊢
      omega

end EthInapproximability.CurrentPaper.Restoration
