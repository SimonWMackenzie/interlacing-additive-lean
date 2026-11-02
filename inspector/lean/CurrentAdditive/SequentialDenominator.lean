import CurrentAdditive.AppendDenominator

set_option maxHeartbeats 1000000

namespace CurrentAdditive.RationalCandidateCompletion

open CurrentAdditive.SequentialCode
open CurrentAdditive.SequentialSourceCode
open CurrentAdditive.RationalBitBounds

theorem compressSourceOnce_source_denominator {α : Type*}
    (n : Nat) (φ : α → Fin n → ℚ)
    (source out : Array (α × ℚ))
    (hn : 0 < n)
    (hφ : ∀ x j, φ x j = 0 ∨ φ x j = 1)
    (h : compressSourceOnceMaterialized n φ source = some out)
    (enc : CommonDenominator
      (fun i : Fin source.size => source[i].2)) :
    ∃ next : CommonDenominator
        (fun j : Fin out.size => out[j].2),
      next.denominator ≤ enc.denominator *
        2 ^ (4 * n * Nat.size (n + 1)) := by
  let encWeights : CommonDenominator
      (fun i : Fin (source.map Prod.snd).size =>
        (source.map Prod.snd)[i]) :=
    { denominator := enc.denominator
      positive := enc.positive
      numerator := fun i => enc.numerator ⟨i.val, by simpa using i.isLt⟩
      represents := by
        intro i
        have hp := enc.represents ⟨i.val, by simpa using i.isLt⟩
        simpa using hp }
  obtain ⟨next, hbound⟩ :=
    compressSourceOnceMaterialized_denominator n φ source out hn hφ h encWeights
  refine ⟨next, ?_⟩
  exact hbound

/-- Successful repeated calls of the literal fuel-bounded compression routine
multiply the input common denominator by at most one manuscript-scale factor
per available fuel unit. The count is an upper bound; early stopping is
allowed. -/
theorem compressSourceFuel_denominator {α : Type*}
    (n : Nat) (φ : α → Fin n → ℚ)
    (hn : 0 < n) (hφ : ∀ x j, φ x j = 0 ∨ φ x j = 1) :
    ∀ (fuel : Nat) (source out : Array (α × ℚ)),
      compressSourceFuelMaterialized n φ source fuel = some out →
      (enc : CommonDenominator
        (fun i : Fin source.size => source[i].2)) →
      ∃ next : CommonDenominator
          (fun j : Fin out.size => out[j].2),
        next.denominator ≤ enc.denominator *
          (2 ^ (4 * n * Nat.size (n + 1))) ^ fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro source out h enc
      simp only [compressSourceFuelMaterialized] at h
      split_ifs at h
      cases h
      exact ⟨enc, by simp⟩
  | succ fuel ih =>
      intro source out h enc
      simp only [compressSourceFuelMaterialized] at h
      split_ifs at h with hs
      · cases h
        refine ⟨enc, ?_⟩
        have hp : 1 ≤ (2 ^ (4 * n * Nat.size (n + 1))) ^ (fuel + 1) := by
          have hpos : 0 < (2 ^ (4 * n * Nat.size (n + 1))) ^ (fuel + 1) := by
            exact pow_pos (pow_pos (by omega : 0 < (2 : ℕ)) _) _
          omega
        simpa only [mul_one] using Nat.mul_le_mul_left enc.denominator hp
      · cases hstep : compressSourceOnceMaterialized n φ source with
        | none => simp [hstep] at h
        | some nextSource =>
            simp [hstep] at h
            obtain ⟨encStep, hstepBound⟩ :=
              compressSourceOnce_source_denominator n φ source nextSource
                hn hφ hstep enc
            obtain ⟨encOut, hrecBound⟩ :=
              ih nextSource out h encStep
            refine ⟨encOut, ?_⟩
            calc
              encOut.denominator ≤
                  encStep.denominator *
                    (2 ^ (4 * n * Nat.size (n + 1))) ^ fuel := hrecBound
              _ ≤ (enc.denominator * 2 ^ (4 * n * Nat.size (n + 1))) *
                    (2 ^ (4 * n * Nat.size (n + 1))) ^ fuel :=
                  Nat.mul_le_mul_right _ hstepBound
              _ = enc.denominator *
                    (2 ^ (4 * n * Nat.size (n + 1))) ^ (fuel + 1) := by
                  rw [pow_succ]
                  ring

#print axioms compressSourceOnce_source_denominator
#print axioms compressSourceFuel_denominator

end CurrentAdditive.RationalCandidateCompletion
