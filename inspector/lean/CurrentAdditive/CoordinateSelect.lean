import CurrentAdditive.CoordinateStages

namespace CurrentAdditive.FiniteFieldCoordinate

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open EthInapproximability.CurrentPaper.BitMachineStackRun
open CurrentAdditive.FiniteFieldConstructor.CanonicalTable

noncomputable def selectorProgram40 :=
  fun l => stackStmt selectorSlots (selectorReadyDigitProgram l)

def selectorClock (q H z g : ℕ) : ℕ :=
  MatrixWeightedPower.powerBound H g + 2 +
    ((8 * z + 3 * (H ^ g) + 4) +
      (8 * (z / H ^ g) + 3 * H + 4) + 1) + 1

theorem staged_selector_inputs (S : Stack → List Bool)
    (z g H : ℕ)
    (hz : S 0 = List.replicate z true)
    (hg : S 1 = List.replicate g true)
    (hH : S 2 = List.replicate H true)
    (hblank : ∀ k : Stack, 7 ≤ k.val → S k = []) :
    (staged S) (selectorSlots 0) = List.replicate z true ∧
    (staged S) (selectorSlots 1) = [] ∧
    (staged S) (selectorSlots 6) = List.replicate H true ∧
    (staged S) (selectorSlots 11) = List.replicate g true ∧
    (∀ k : Fin 11, k ≠ 0 → k ≠ 1 → k ≠ 6 →
      (staged S) (selectorSlots (selectorDigitIncl k)) = []) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [selectorSlots] using (staged_at_target S).1.trans hz
  · simp [selectorSlots, staged, jobs,
      EthInapproximability.CurrentPaper.CopyFill.fill, hblank]
  · simpa [selectorSlots] using (staged_at_target S).2.2.1.trans hH
  · simpa [selectorSlots] using (staged_at_target S).2.1.trans hg
  · intro k hk0 hk1 hk6
    fin_cases k <;> simp_all [selectorSlots, selectorDigitIncl, staged, jobs,
      EthInapproximability.CurrentPaper.CopyFill.fill, hblank]

/-- A literal embedded run, leaving the public input cells outside the selector region. -/
theorem selector_run40 (q H : ℕ) (z : Fin (H ^ q)) (g : Fin q)
    (S : Stack → List Bool)
    (hz : S 0 = List.replicate z.val true)
    (hg : S 1 = List.replicate g.val true)
    (hH : S 2 = List.replicate H true)
    (hblank : ∀ k : Stack, 7 ≤ k.val → S k = []) :
    ∃ steps ≤ selectorClock q H z.val g.val,
      ∃ F : Fin 12 → List Bool,
        ((advance selectorProgram40)^[steps])
          (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel ())),
            ((none, (false, false)), (false, false)), staged S⟩ :
            TM2.Cfg (fun _ : Stack => Bool) _ _) =
          ⟨none, ((none, (false, false)), (false, false)),
            bank selectorSlots (staged S) F⟩ ∧
        F 8 = List.replicate (selector q H z g).val true := by
  obtain ⟨h0,h1,h6,h11,he⟩ := staged_selector_inputs S z.val g.val H hz hg hH hblank
  let localS : Fin 12 → List Bool := fun k => (staged S) (selectorSlots k)
  obtain ⟨steps,ht,F,hr,hF,_⟩ := physical_selector_digit_from_blank
    q H z g localS
    (by simpa [localS] using h0)
    (by simpa [localS] using h1)
    (by simpa [localS] using h6)
    (by simpa [localS] using h11)
    (by simpa [localS] using he)
  refine ⟨steps, by simpa [selectorClock] using ht, F, ?_, ?_⟩
  · have hsim := BitMachineStackRun.run selectorSlots (staged S)
      selectorReadyDigitProgram
      (⟨some (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel ())),
        ((none, (false, false)), (false, false)), localS⟩ :
        TM2.Cfg (fun _ : Fin 12 => Bool) _ _) steps
    rw [hr] at hsim
    simpa only [selectorProgram40, localS, stackCfg, bank_restrict] using hsim
  · exact hF

end CurrentAdditive.FiniteFieldCoordinate
