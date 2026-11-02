import CurrentAdditive.CanonicalPhysicalSelectorStrideInit

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalTable

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding

def selectorDigitIncl : Fin 11 ↪ Fin 12 := Fin.castLEEmb (by decide)

noncomputable def selectorDigitProgram12 :=
  fun l => stackStmt selectorDigitIncl (selectorDigitProgram l)

/-- Lift the two physical unary divisions to the twelve-cell bank used by
the preceding stride producer, preserving the foreign query-fuel cell. -/
theorem physical_selector_digit12 (q H : ℕ)
    (z : Fin (H ^ q)) (g : Fin q) (S : Fin 12 → List Bool)
    (h0 : S 0 = List.replicate z.val true)
    (h1 : S 1 = List.replicate (H ^ g.val) true)
    (h6 : S 6 = List.replicate H true)
    (hempty : ∀ k : Fin 11, k ≠ 0 → k ≠ 1 → k ≠ 6 →
      S (selectorDigitIncl k) = []) :
    ∃ steps ≤ (8 * z.val + 3 * (H ^ g.val) + 4) +
        (8 * (z.val / H ^ g.val) + 3 * H + 4) + 1,
      ((advance selectorDigitProgram12)^[steps])
        (⟨some (BitMachineRawSequence.leftLabel
          MatrixUnaryDivision.Label.start), (false, false), S⟩ :
          TM2.Cfg (fun _ : Fin 12 => Bool) _ _) =
        ⟨none, (false, false),
          bank selectorDigitIncl S
            (Function.update (Function.update (Function.update
              (Function.update (Function.update (Function.update
                (fun k => S (selectorDigitIncl k)) 0 [])
                3 (List.replicate (z.val % H ^ g.val) true))
                4 (List.replicate (z.val / H ^ g.val) true))
                4 [])
                 8 (List.replicate (selector q H z g).val true))
                9 (List.replicate ((z.val / H ^ g.val) / H) true))⟩ := by
  let localS : Fin 11 → List Bool := fun k => S (selectorDigitIncl k)
  obtain ⟨steps, hsteps, hrun⟩ := physical_selector_digit q H z g localS
    (by simpa [localS, selectorDigitIncl] using h0)
    (by simpa [localS, selectorDigitIncl] using h1)
    (by simpa [localS, selectorDigitIncl] using h6)
    (by simpa [localS] using hempty)
  refine ⟨steps, hsteps, ?_⟩
  have he := BitMachineStackRun.run selectorDigitIncl S
    selectorDigitProgram
    (⟨some (BitMachineRawSequence.leftLabel MatrixUnaryDivision.Label.start),
      (false, false), localS⟩ : TM2.Cfg (fun _ : Fin 11 => Bool) _ _) steps
  rw [hrun] at he
  simpa only [selectorDigitProgram12, localS, stackCfg, bank_restrict] using he

#print axioms physical_selector_digit12

end CurrentAdditive.FiniteFieldConstructor.CanonicalTable
