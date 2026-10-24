import CurrentAdditive.CanonicalPhysicalSelectorDigitLift

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalTable

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding

noncomputable def selectorReadyDigitProgram :=
  BitMachineRawSequence.program selectorStrideProgram selectorDigitProgram12
    (BitMachineRawSequence.leftLabel MatrixUnaryDivision.Label.start)
    (none, (false, false)) (false, false)

/-- One fixed physical program computes the selected base-H digit from
blank stride space, the row's unary selector z, base H, and query g. -/
theorem physical_selector_digit_from_blank (q H : ℕ)
    (z : Fin (H ^ q)) (g : Fin q) (S : Fin 12 → List Bool)
    (h0 : S 0 = List.replicate z.val true)
    (h1 : S 1 = [])
    (h6 : S 6 = List.replicate H true)
    (h11 : S 11 = List.replicate g.val true)
    (hempty : ∀ k : Fin 11, k ≠ 0 → k ≠ 1 → k ≠ 6 →
      S (selectorDigitIncl k) = []) :
    ∃ steps ≤ MatrixWeightedPower.powerBound H g.val + 2 +
        ((8 * z.val + 3 * (H ^ g.val) + 4) +
        (8 * (z.val / H ^ g.val) + 3 * H + 4) + 1) + 1,
      ∃ finalBank : Fin 12 → List Bool,
        ((advance selectorReadyDigitProgram)^[steps])
          (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel ())),
            ((none, (false, false)), (false, false)), S⟩ :
            TM2.Cfg (fun _ : Fin 12 => Bool) _ _) =
          ⟨none, ((none, (false, false)), (false, false)), finalBank⟩ ∧
        finalBank 8 = List.replicate (selector q H z g).val true ∧
        finalBank 11 = [] := by
  let S1 := Function.update (Function.update S 1
    (List.replicate (H ^ g.val) true)) 11 []
  obtain ⟨t1, ht1, hr1⟩ := physical_selector_stride_from_blank H g.val S
    h1 h6
    (by simpa [selectorDigitIncl] using hempty 7 (by decide) (by decide) (by decide))
    (by simpa [selectorDigitIncl] using hempty 8 (by decide) (by decide) (by decide))
    (by simpa [selectorDigitIncl] using hempty 9 (by decide) (by decide) (by decide))
    (by simpa [selectorDigitIncl] using hempty 10 (by decide) (by decide) (by decide))
    h11
  have hr1' : ((advance selectorStrideProgram)^[t1])
      (⟨some (BitMachineRawSequence.leftLabel ()),
        (none, (false, false)), S⟩ : TM2.Cfg (fun _ : Fin 12 => Bool) _ _) =
      ⟨none, (none, (false, false)), S1⟩ := by simpa only [S1] using hr1
  have h0' : S1 0 = List.replicate z.val true := by simpa [S1] using h0
  have h1' : S1 1 = List.replicate (H ^ g.val) true := by simp [S1]
  have h6' : S1 6 = List.replicate H true := by simpa [S1] using h6
  have he' : ∀ k : Fin 11, k ≠ 0 → k ≠ 1 → k ≠ 6 →
      S1 (selectorDigitIncl k) = [] := by
    intro k hk0 hk1 hk6
    have hki : selectorDigitIncl k ≠ (1 : Fin 12) := by
      intro heq
      exact hk1 (Fin.ext (by simpa [selectorDigitIncl] using congrArg Fin.val heq))
    have hk11 : selectorDigitIncl k ≠ (11 : Fin 12) := by
      intro heq
      have h := congrArg Fin.val heq
      simp [selectorDigitIncl] at h
      omega
    simpa only [S1, Function.update_of_ne hki, Function.update_of_ne hk11] using
      hempty k hk0 hk1 hk6
  obtain ⟨t2, ht2, hr2⟩ := physical_selector_digit12 q H z g S1
    h0' h1' h6' he'
  let finalBank : Fin 12 → List Bool :=
    bank selectorDigitIncl S1
      (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update
          (fun k => S1 (selectorDigitIncl k)) 0 [])
          3 (List.replicate (z.val % H ^ g.val) true))
          4 (List.replicate (z.val / H ^ g.val) true))
          4 [])
          8 (List.replicate (selector q H z g).val true))
          9 (List.replicate ((z.val / H ^ g.val) / H) true))
  have hr2' : ((advance selectorDigitProgram12)^[t2])
      (⟨some (BitMachineRawSequence.leftLabel MatrixUnaryDivision.Label.start),
        (false, false), S1⟩ : TM2.Cfg (fun _ : Fin 12 => Bool) _ _) =
      ⟨none, (false, false), finalBank⟩ := by simpa only [finalBank] using hr2
  obtain ⟨steps, hsteps, hrun⟩ := BitMachineRawSequence.runs
    selectorStrideProgram selectorDigitProgram12
    (BitMachineRawSequence.leftLabel ())
    (BitMachineRawSequence.leftLabel MatrixUnaryDivision.Label.start)
    (none, (false, false)) (none, (false, false))
    (false, false) (false, false) S S1 finalBank t1 t2 hr1' hr2'
  refine ⟨steps, by omega, finalBank, ?_, ?_, ?_⟩
  · simpa only [selectorReadyDigitProgram] using hrun
  · have h8 : finalBank (selectorDigitIncl 8) =
        List.replicate (selector q H z g).val true := by
      simp only [finalBank, bank_at]
      simp
    simpa [selectorDigitIncl] using h8
  · have houtside : ¬ ∃ k : Fin 11, selectorDigitIncl k = (11 : Fin 12) := by
      rintro ⟨k, hk⟩
      have hv := congrArg Fin.val hk
      simp [selectorDigitIncl] at hv
      omega
    simp only [finalBank, bank_outside selectorDigitIncl S1 _ 11 houtside]
    simp [S1]

#print axioms physical_selector_digit_from_blank

end CurrentAdditive.FiniteFieldConstructor.CanonicalTable
