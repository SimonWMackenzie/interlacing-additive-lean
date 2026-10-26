import CurrentAdditive.V38AmbientFieldFull

/-! Named end bank and foreign-cell preservation for source/scalar callers. -/

noncomputable section

namespace CurrentAdditive.V38AmbientFieldFull

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open CurrentAdditive.SmallBias CurrentAdditive.V38Machine CurrentAdditive.V38Clock
open CurrentAdditive.FieldSearchCompletion
open CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
open CurrentAdditive.V38AmbientFieldInstall

set_option maxHeartbeats 1000000

def finalBank (b t producerSteps modulus : ℕ) (S : Cell t 16 → List Bool) :
    Cell t 16 → List Bool :=
  Function.update
    (bank (producerEmbed t) (inputBank t (v38FieldDegree b t) (v38PositionCount b t) S)
      (V38FieldPad.run (2 ^ t * 2 ^ t) (by positivity) producerSteps
        (V38FieldPad.publicStart b t)).stk)
    (fieldBankCell t) (paddedBits b t (v38FieldDegree b t) modulus)

theorem finalBank_foreign (b t producerSteps modulus : ℕ)
    (S : Cell t 16 → List Bool) (j : Cell t 16)
    (hforeign : ¬ ∃ i : V38FieldPad.Stack, producerEmbed t i = j) :
    finalBank b t producerSteps modulus S j = S j := by
  have hfield : j ≠ fieldBankCell t := by
    intro hj
    exact hforeign ⟨.inl V38FieldPad.fieldOutput, hj.symm⟩
  have h0 : j ≠ .fieldInit 0 := by
    intro hj
    exact hforeign ⟨.inl (.inl 0), hj.symm⟩
  have h1 : j ≠ .fieldInit 1 := by
    intro hj
    exact hforeign ⟨.inl (.inl 1), hj.symm⟩
  unfold finalBank
  rw [Function.update_of_ne hfield, bank_outside _ _ _ _ hforeign]
  simp only [inputBank, Function.update_of_ne h1, Function.update_of_ne h0]

theorem finalBank_scratch_zero (b t producerSteps modulus : ℕ)
    (S : Cell t 16 → List Bool) :
    finalBank b t producerSteps modulus S (.copyScratch 0) = S (.copyScratch 0) :=
  finalBank_foreign b t producerSteps modulus S _ (producer_foreign_scratch t)

theorem finalBank_field (b t producerSteps modulus : ℕ)
    (S : Cell t 16 → List Bool) :
    finalBank b t producerSteps modulus S (fieldBankCell t) =
      paddedBits b t (v38FieldDegree b t) modulus := by
  exact Function.update_self _ _ _

theorem physical_full_bank (b t : ℕ) (ht : 4 ≤ t) (S : Cell t 16 → List Bool)
    (hd : S (.degree 3) = List.replicate (v38FieldDegree b t) true)
    (hn : S (.width 5) = List.replicate (v38PositionCount b t) true)
    (hblank : ∀ i : V38FieldPad.Stack, S (producerEmbed t i) = [])
    (hscratch : S (.copyScratch 0) = []) :
    ∃ modulus,
      FiniteFieldConstructor.TrialSearch.firstPassing (v38FieldDegree b t) = some modulus ∧
      ∃ producerSteps ≤ 100 * (v38FieldTarget b t) ^ 5,
      ∃ total ≤ fullClock b t,
        ((advance (fullProgram t))^[total])
          (⟨some (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
            ((none, none), (sourceControl, none)), S⟩ :
              TM2.Cfg (fun _ : Cell t 16 => Bool) _ _) =
          ⟨none, ((none, none), (sourceControl, none)),
            finalBank b t producerSteps modulus S⟩ := by
  exact physical_full b t ht S hd hn hblank hscratch

theorem fullClock_le (b t : ℕ) :
    fullClock b t ≤ 120 * (v38FieldTarget b t) ^ 5 := by
  have hd : v38FieldDegree b t + 1 ≤ v38FieldTarget b t := by
    rw [← field_order_exact]
    exact degree_succ_le_order _
  have hn := position_le_target b t
  have hX : 1 ≤ v38FieldTarget b t := by omega
  have hpow : v38FieldTarget b t ≤ (v38FieldTarget b t) ^ 5 := by
    have h := Nat.pow_le_pow_right hX (by decide : 1 ≤ 5)
    simpa using h
  unfold fullClock publicCopyClock
  omega

#print axioms finalBank_foreign
#print axioms finalBank_scratch_zero
#print axioms finalBank_field
#print axioms physical_full_bank
#print axioms fullClock_le

end CurrentAdditive.V38AmbientFieldFull
