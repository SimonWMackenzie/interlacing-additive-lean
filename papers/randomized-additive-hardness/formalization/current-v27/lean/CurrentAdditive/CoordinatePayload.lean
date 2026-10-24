import CurrentAdditive.CoordinatePosition

namespace CurrentAdditive.FiniteFieldCoordinate

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open EthInapproximability.CurrentPaper.BitMachineStackRun
open CurrentAdditive.FiniteFieldConstructor.CanonicalTable

noncomputable def positioned (S : Stack → List Bool) (F : Fin 12 → List Bool)
    (p : ℕ) : Stack → List Bool :=
  Function.update (selected S F) 29 (List.replicate p true)

noncomputable def widthReady (S : Stack → List Bool) (F : Fin 12 → List Bool)
    (p K : ℕ) : Stack → List Bool :=
  Function.update (positioned S F p) 33 (List.replicate (K + 1) true)

def widthPush : Unit → TM2.Stmt (fun _ : Stack => Bool) Unit Unit
  | () => .push 33 (fun _ => true) .halt

theorem width_run (S : Stack → List Bool) (F : Fin 12 → List Bool)
    (p K : ℕ)
    (hwidth : (positioned S F p) 33 = List.replicate K true) :
    (advance widthPush)
      (⟨some (), (), positioned S F p⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Unit Unit) =
      ⟨none, (), widthReady S F p K⟩ := by
  simp only [advance, TM2.step, TM2.stepAux, widthPush,
    Option.getD_some, widthReady]
  congr 1
  funext j
  by_cases hj : j = 33
  · subst j
    simp [hwidth, List.replicate_succ]
  · simp [Function.update_of_ne hj]

noncomputable def payloadProgram40 :=
  fun l => stackStmt payloadSlots (payloadIndexProgram l)

noncomputable def payloadOutput (H K : ℕ) (α : Fin H) (p : Fin (K + 1))
    (S : Stack → List Bool) (F : Fin 12 → List Bool) : Stack → List Bool :=
  bank payloadSlots (widthReady S F p.val K)
    (Function.update
      (Function.update
        (Function.update (fun k => (widthReady S F p.val K) (payloadSlots k)) 0 []) 1 [])
      2 (List.replicate (α.val * (K + 1) + p.val) true))

def payloadClock (K α p : ℕ) : ℕ :=
  (α * (2 * (K + 1) + 3) + 1 + ((K + 1) + 1)) +
    (2 * p + 2) + 1

theorem width_input (S : Stack → List Bool) (F : Fin 12 → List Bool)
    (p K : ℕ) (hK : S 6 = List.replicate K true) :
    (positioned S F p) 33 = List.replicate K true := by
  simp only [positioned, Function.update_of_ne (by decide : (33 : Stack) ≠ 29)]
  have h33 := selected_at_payload_fresh S F 0 (Or.inl rfl)
  have h33' : selected S F 33 = staged S 33 := by simpa [payloadSlots] using h33
  rw [h33']
  simpa [payloadSlots] using (staged_at_target S).2.2.2.2.2.2.2.trans hK

/-- The fixed physical multiplier/copy machine consumes private address and width
copies and leaves the exact row-major coordinate on public output cell 7. -/
theorem payload_run40 (H K : ℕ) (α : Fin H) (p : Fin (K + 1))
    (S : Stack → List Bool) (F : Fin 12 → List Bool)
    (hα : F 8 = List.replicate α.val true)
    (hblank : ∀ k : Stack, 7 ≤ k.val → S k = []) :
    ∃ steps ≤ payloadClock K α.val p.val,
      ((advance payloadProgram40)^[steps])
        (⟨some (BitMachineRawSequence.leftLabel
            MatrixUnaryArithmetic.Label.outer), (false, none),
          widthReady S F p.val K⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, (false, none), payloadOutput H K α p S F⟩ := by
  let W := widthReady S F p.val K
  let localW : Fin 6 → List Bool := fun k => W (payloadSlots k)
  have hw : localW 0 = List.replicate (K + 1) true := by
    simp [localW, W, widthReady, payloadSlots]
  have ha : localW 1 = List.replicate α.val true := by
    simp only [localW, W, payloadSlots, widthReady, positioned,
      Function.update_of_ne (by decide : (17 : Stack) ≠ 33),
      Function.update_of_ne (by decide : (17 : Stack) ≠ 29)]
    exact (selected_digit S F).trans hα
  have hp : localW 2 = [] := by
    have h7 := selected_at_payload_fresh S F 2 (Or.inr (Or.inl rfl))
    have h7' : selected S F 7 = [] := by
      have hx : selected S F 7 = staged S 7 := by simpa [payloadSlots] using h7
      rw [hx]
      simpa [staged, jobs, EthInapproximability.CurrentPaper.CopyFill.fill]
        using hblank 7 (by decide)
    simpa [localW, W, payloadSlots, widthReady, positioned] using h7'
  have hwork : localW 3 = [] := by
    have h34 := selected_at_payload_fresh S F 3 (Or.inr (Or.inr (Or.inl rfl)))
    have h34' : selected S F 34 = [] := by
      have hx : selected S F 34 = staged S 34 := by simpa [payloadSlots] using h34
      rw [hx]
      simpa [staged, jobs, EthInapproximability.CurrentPaper.CopyFill.fill]
        using hblank 34 (by decide)
    simpa [localW, W, payloadSlots, widthReady, positioned] using h34'
  have hslot : localW 4 = List.replicate p.val true := by
    simp [localW, W, widthReady, positioned, payloadSlots]
  have hcopy : localW 5 = [] := by
    have h35 := selected_at_payload_fresh S F 5 (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    have h35' : selected S F 35 = [] := by
      have hx : selected S F 35 = staged S 35 := by simpa [payloadSlots] using h35
      rw [hx]
      simpa [staged, jobs, EthInapproximability.CurrentPaper.CopyFill.fill]
        using hblank 35 (by decide)
    simpa [localW, W, payloadSlots, widthReady, positioned] using h35'
  obtain ⟨steps,ht,hr⟩ := physical_payload_index H K α p localW
    hw ha hp hwork hslot hcopy
  refine ⟨steps, by simpa [payloadClock] using ht, ?_⟩
  have hsim := BitMachineStackRun.run payloadSlots W payloadIndexProgram
    (⟨some (BitMachineRawSequence.leftLabel
      MatrixUnaryArithmetic.Label.outer), (false, none), localW⟩ :
      TM2.Cfg (fun _ : Fin 6 => Bool) _ _) steps
  rw [hr] at hsim
  simpa only [payloadProgram40, payloadOutput, W, localW,
    stackCfg, bank_restrict] using hsim

end CurrentAdditive.FiniteFieldCoordinate
