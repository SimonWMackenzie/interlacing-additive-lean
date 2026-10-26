import EthInapproximability.CurrentPaper.Foundations
import EthInapproximability.ParameterizedNP.SeedSpanLeg

/-!
# Current paper: the robust indexing seed

Source: v8 `sections/05-iteration.tex`, `lem:paper-full-cube-seed`.
The width is the least POWER OF TWO above `64 (b+1)`.  In particular this is
not the older route's width `2^a - 2`.  Only the older generic Boolean-span,
fixed-output-rank, and literal indexing-protocol lemmas are reused.
-/

namespace EthInapproximability.CurrentPaper.IndexSeed

open NPCC Workspace.Types.CommComplexity Workspace.Types.Interlace
open EthInapproximability.ParameterizedNP.OneLevelCompletion
open EthInapproximability.ParameterizedNP.SeedSpanLeg
open EthInapproximability.ParameterizedNP.SeedAnchoredFold
open EthInapproximability.ParameterizedNP.DirectOutputLower

/-- Exponent of the least admissible power of two. -/
def exponent (b : ℕ) : ℕ := Nat.clog 2 (64 * (b + 1))

/-- Length of Alice's string in the current paper. -/
def width (b : ℕ) : ℕ := 2 ^ exponent b

/-- The literal indexing matrix, with the entire Boolean cube as row set. -/
def seed (b : ℕ) : (Fin (width b) → Bool) → Fin (width b) → Bool :=
  fun γ j => γ j

theorem seed_apply (b : ℕ) (γ : Fin (width b) → Bool) (j : Fin (width b)) :
    seed b γ j = γ j := rfl

theorem width_lower (b : ℕ) : 64 * (b + 1) ≤ width b :=
  Nat.le_pow_clog (by norm_num) _

theorem exponent_minimal (b a : ℕ) (ha : 64 * (b + 1) ≤ 2 ^ a) :
    exponent b ≤ a := Nat.clog_le_of_le_pow ha

theorem exponent_ge_six (b : ℕ) : 6 ≤ exponent b := by
  have h : 5 < Nat.clog 2 (64 * (b + 1)) := by
    apply (Nat.lt_clog_iff_pow_lt (by norm_num)).2
    norm_num
    omega
  exact h

theorem width_lt (b : ℕ) : width b < 128 * (b + 1) := by
  have ha := exponent_ge_six b
  have hp : 2 ^ (exponent b - 1) < 64 * (b + 1) :=
    Nat.pow_pred_clog_lt_self (b := 2) (x := 64 * (b + 1)) (by norm_num) (by omega)
  have heq : width b = 2 * 2 ^ (exponent b - 1) := by
    rw [width, ← Nat.pow_succ', Nat.succ_eq_add_one,
      Nat.sub_add_cancel (by omega : 1 ≤ exponent b)]
  omega

/-- The two density notations are definitionally different but equal. -/
theorem rowDensity_eq (b : ℕ) :
    (2 : ℝ) ^ (-(b : ℝ)) = xOut b := by
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
  rfl

/-- Boolean row counting followed by projection onto the retained columns.
The bound is generic in the width, not an assumption about the new seed. -/
theorem indexing_rank_floor (q b : ℕ) (y : ℝ)
    (RC : Finset (Fin 1 × (Fin q → Bool)) × Finset (Fin 1 → Fin q))
    (hRC : RC ∈ bracketGE (Fin q → Bool) (Fin q) 1
      ((2 : ℝ) ^ (-(b : ℝ))) y) :
    RC.2.card ≤ b +
      (indR (subgame (interlaceFun (fullCube q) 1) RC.1 RC.2) true).rank := by
  rw [rowDensity_eq] at hRC
  exact fullCube_rankFloor q b y RC hRC

/-- A usable rank-to-communication consequence for arbitrary indexing widths. -/
theorem indexing_restriction_lower (q b d : ℕ) (hd : 1 ≤ d) (y : ℝ)
    (hy : y ≤ 1) (hthr : b + 2 ^ (d - 1) < ⌈(q : ℝ) * y⌉₊) :
    d + 1 ≤ Dfamily (interlaceFun (fullCube q) 1)
      (bracketGE (Fin q → Bool) (Fin q) 1 ((2 : ℝ) ^ (-(b : ℝ))) y) := by
  rw [rowDensity_eq]
  exact fullCube_bracket_ge_of_rankFloor q b d hd y hy
    (by simpa using hthr) (fun RC hRC => fullCube_rankFloor q b y RC hRC)

theorem seed_D_eq (b : ℕ) : D (seed b) = exponent b + 1 := by
  have ha := exponent_ge_six b
  apply fullCube_D_eq (width b) (exponent b) (by omega)
  · change 2 ^ (exponent b - 1) < 2 ^ exponent b
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).2 (by omega)
  · exact le_rfl

/-- The numerical margin for all three column densities, before rounding. -/
theorem rung_margin (b t : ℕ) (ht : t ≤ 2) :
    (b : ℝ) + 2 ^ (exponent b - t - 1) <
      (width b : ℝ) * ((3 / 5) / 2 ^ t) := by
  have ha := exponent_ge_six b
  have hsplitN : (2 : ℕ) ^ (exponent b - t - 1) * 2 ^ (t + 1) = width b := by
    rw [← pow_add, width]
    congr 1
    omega
  have hsplit : (2 : ℝ) ^ (exponent b - t - 1) * 2 ^ (t + 1) = (width b : ℝ) := by
    exact_mod_cast hsplitN
  have hupos : (0 : ℝ) < 2 ^ t := by positivity
  have hu4 : (2 : ℝ) ^ t ≤ 4 := by
    calc (2 : ℝ) ^ t ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) ht
      _ = 4 := by norm_num
  have hq : (64 : ℝ) * ((b : ℝ) + 1) ≤ (width b : ℝ) := by
    exact_mod_cast width_lower b
  have hb4 : (b : ℝ) * 2 ^ t ≤ (b : ℝ) * 4 :=
    mul_le_mul_of_nonneg_left hu4 (Nat.cast_nonneg b)
  have hP : (2 : ℝ) ^ (exponent b - t - 1) * 2 ^ t * 2 = (width b : ℝ) := by
    rw [pow_succ] at hsplit
    calc (2 : ℝ) ^ (exponent b - t - 1) * 2 ^ t * 2 =
        (2 : ℝ) ^ (exponent b - t - 1) * (2 ^ t * 2) := by ring
      _ = (width b : ℝ) := hsplit
  rw [← mul_div_assoc, lt_div_iff₀ hupos]
  linarith only [hb4, hP, hq]

/-- All three actual restriction costs, with their natural-number offsets. -/
theorem seed_rung (b t : ℕ) (ht : t ≤ 2) :
    exponent b - t + 1 ≤ Dfamily (interlaceFun (seed b) 1)
      (bracketGE (Fin (width b) → Bool) (Fin (width b)) 1
        ((2 : ℝ) ^ (-(b : ℝ))) ((3 : ℝ) / 5 / 2 ^ t)) := by
  have ha := exponent_ge_six b
  apply indexing_restriction_lower (width b) b (exponent b - t) (by omega)
  · have hp : (1 : ℝ) ≤ 2 ^ t := one_le_pow₀ (by norm_num)
    exact (div_le_iff₀ (by positivity)).2 (by linarith)
  · apply Nat.lt_ceil.mpr
    push_cast
    exact rung_margin b t ht

/-- The stronger three-bound statement in the paper. -/
theorem seed_lambda (b : ℕ) :
    exponent b + 1 ≤ LambdaGE (seed b) 1
      ((2 : ℝ) ^ (-(b : ℝ))) (3 / 5) := by
  have ha := exponent_ge_six b
  have h0 := seed_rung b 0 (by omega)
  have h1 := seed_rung b 1 (by omega)
  have h2 := seed_rung b 2 (by omega)
  unfold LambdaGE
  norm_num at h0 h1 h2 ⊢
  exact ⟨by omega, by omega, by omega⟩

/-- The initial matrix satisfies the CURRENT two-input robustness predicate. -/
theorem seed_isRobustAt (b : ℕ) (hb : 1 ≤ b) : IsRobustAt (seed b) b := by
  have ha := exponent_ge_six b
  have h0 := seed_rung b 0 (by omega)
  have h1 := seed_rung b 1 (by omega)
  unfold IsRobustAt
  rw [seed_D_eq]
  norm_num at h0 h1 ⊢
  exact ⟨hb, by omega, by omega, by omega⟩

/-- The input-length convention of Section 5, including its lower bound one. -/
def bits {X Y : Type*} [Fintype X] [Fintype Y] (_f : X → Y → Bool) : ℕ :=
  max 1 (max (Nat.clog 2 (Fintype.card X)) (Nat.clog 2 (Fintype.card Y)))

theorem seed_carriers (b : ℕ) :
    Fintype.card (Fin (width b) → Bool) = 2 ^ width b ∧
    Fintype.card (Fin (width b)) = width b := by simp

theorem seed_bits (b : ℕ) : bits (seed b) = width b := by
  have hpos : 1 ≤ width b := Nat.one_le_two_pow
  have hle : exponent b ≤ width b := Nat.le_of_lt (Nat.lt_two_pow_self)
  simp only [bits, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Nat.clog_pow 2 _ (by norm_num : 1 < 2)]
  change max 1 (max (width b) (Nat.clog 2 (2 ^ exponent b))) = width b
  rw [Nat.clog_pow 2 _ (by norm_num), max_eq_left hle, max_eq_right hpos]

/-- The full v8 seed theorem, with no restriction or rank hypotheses. -/
theorem robust_indexing_seed (b : ℕ) (hb : 1 ≤ b) :
    IsRobustAt (seed b) b ∧ D (seed b) = exponent b + 1 ∧
    exponent b + 1 ≤ LambdaGE (seed b) 1 ((2 : ℝ) ^ (-(b : ℝ))) (3 / 5) ∧
    bits (seed b) = width b ∧ width b < 128 * (b + 1) :=
  ⟨seed_isRobustAt b hb, seed_D_eq b, seed_lambda b, seed_bits b, width_lt b⟩

/-- The first permitted requested depth uses the new power-of-two width. -/
theorem depth_one_regression : exponent 1 = 7 ∧ width 1 = 128 := by
  decide

end EthInapproximability.CurrentPaper.IndexSeed
