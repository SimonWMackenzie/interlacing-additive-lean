import CurrentAdditive.V38FieldPadRun
import CurrentAdditive.V38PackedIdentity

/-! Public-only physical construction of the exact internal zero-sentinel
bank consumed by the v38 table renderer. The true array positions remain
H*K, and the fixed program (for fixed t) consumes unary public d,n. -/

namespace CurrentAdditive.V38FieldPad

open CurrentAdditive.SmallBias
open CurrentAdditive.V38Clock
open CurrentAdditive.V38Machine
open CurrentAdditive.FieldSearchCompletion

set_option maxHeartbeats 1000000

theorem public_prepBudget (b t : ℕ) :
    FieldUnaryUnifiedMachine.prepTime (v38FieldDegree b t) (v38PositionCount b t) ≤
      12 * (v38FieldTarget b t) ^ 5 := by
  let X := v38FieldTarget b t
  have hn : v38PositionCount b t ≤ X := position_le_target b t
  have hd : v38FieldDegree b t + 1 ≤ X := by
    change v38FieldDegree b t + 1 ≤ v38FieldTarget b t
    rw [← field_order_exact]
    exact degree_succ_le_order _
  have hX : 1 ≤ X := by omega
  have hpow : X ≤ X ^ 5 := by
    have h := Nat.pow_le_pow_right hX (by decide : 1 ≤ 5)
    simpa using h
  have hdiv := Nat.div_le_self (v38FieldDegree b t) 2
  change FieldUnaryUnifiedMachine.prepTime (v38FieldDegree b t)
    (v38PositionCount b t) ≤ 12 * X ^ 5
  unfold FieldUnaryUnifiedMachine.prepTime
  omega

theorem public_wholeBudget (b t : ℕ) (ht : 4 ≤ t) :
    FieldUnaryUnifiedMachine.prepTime (v38FieldDegree b t) (v38PositionCount b t) +
        paddedBudget (v38FieldDegree b t) (v38PositionCount b t) ≤
      100 * (v38FieldTarget b t) ^ 5 := by
  have hp := public_prepBudget b t
  have hb := public_paddedBudget_le b t ht
  omega

theorem public_wholeBudget_fixed_t (b t : ℕ) (ht : 4 ≤ t) :
    FieldUnaryUnifiedMachine.prepTime (v38FieldDegree b t) (v38PositionCount b t) +
        paddedBudget (v38FieldDegree b t) (v38PositionCount b t) ≤
      (100 * (2 ^ (14 * t)) ^ 5) * (2 ^ b) ^ 25 := by
  have h := public_wholeBudget b t ht
  rw [target_fixed_t, mul_pow] at h
  calc
    _ ≤ 100 * ((2 ^ (14 * t)) ^ 5 * ((2 ^ b) ^ 5) ^ 5) := h
    _ = _ := by ring

def publicStart (b t : ℕ) :=
  initialConfig (2 ^ t * 2 ^ t) (v38FieldDegree b t) (v38PositionCount b t)
    (by positivity)

/-- The modulus is found internally; none is supplied in the public input
bank. The final bank is literally the renderer's paddedBits, not a new
mathematical array family. This program is fixed for fixed t. -/
theorem physical_public_padded_bank (b t : ℕ) (ht : 4 ≤ t) :
    ∃ c < 2 ^ v38FieldDegree b t,
      FiniteFieldConstructor.TrialSearch.firstPassing (v38FieldDegree b t) =
        some (FiniteFieldConstructor.TrialSearch.monicBits (v38FieldDegree b t) c) ∧
      ∃ steps ≤ 100 * (v38FieldTarget b t) ^ 5,
        (run (2 ^ t * 2 ^ t) (by positivity) steps (publicStart b t)).l = none ∧
        (run (2 ^ t * 2 ^ t) (by positivity) steps (publicStart b t)).stk (.inr true) =
          paddedBits b t (v38FieldDegree b t)
            (FiniteFieldConstructor.TrialSearch.monicBits (v38FieldDegree b t) c) := by
  obtain ⟨c, hc, hfirst, steps, hsteps, hhalt, hout⟩ := physical_field_pad
    (2 ^ t * 2 ^ t) (v38FieldDegree b t) (v38PositionCount b t)
    (by positivity) (v38FieldDegree_pos b t ht)
  refine ⟨c, hc, hfirst, steps, hsteps.trans (public_wholeBudget b t ht), hhalt, ?_⟩
  exact hout.trans (V38ZeroPad.actual_padded_identity b t _ _)

theorem physical_public_selected_bank (b t : ℕ) (ht : 4 ≤ t) :
    ∃ steps ≤ 100 * (v38FieldTarget b t) ^ 5,
      (run (2 ^ t * 2 ^ t) (by positivity) steps (publicStart b t)).l = none ∧
      (run (2 ^ t * 2 ^ t) (by positivity) steps (publicStart b t)).stk (.inr true) =
        paddedBits b t (v38FieldDegree b t)
          ((FiniteFieldConstructor.TrialSearch.firstPassing (v38FieldDegree b t)).getD 0) := by
  obtain ⟨c, _, hfirst, steps, hsteps, hhalt, hout⟩ :=
    physical_public_padded_bank b t ht
  exact ⟨steps, hsteps, hhalt, by simpa only [hfirst, Option.getD_some] using hout⟩

theorem padded_output_length_le (b t modulus : ℕ) :
    (paddedBits b t (v38FieldDegree b t) modulus).length ≤
      2 * (v38FieldTarget b t) ^ 3 := by
  rw [paddedBits_size, field_order_exact]
  have hn := position_le_target b t
  have hH : 2 ^ b ≤ v38PositionCount b t := by
    unfold v38PositionCount
    exact Nat.le_mul_of_pos_right _ (by positivity)
  calc
    _ ≤ (v38FieldTarget b t) ^ 2 *
        (v38FieldTarget b t + v38FieldTarget b t) := by
          gcongr
          exact hH.trans hn
    _ = _ := by ring

#print axioms physical_public_padded_bank
#print axioms physical_public_selected_bank
#print axioms public_wholeBudget_fixed_t
#print axioms padded_output_length_le

end CurrentAdditive.V38FieldPad
