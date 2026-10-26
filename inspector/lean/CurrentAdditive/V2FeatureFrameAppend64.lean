import CurrentAdditive.V2ItemFrameForeign
import CurrentAdditive.V2FeatureFrameLayout64
import CurrentAdditive.GaussV2BodyAppend64

/-! One fixed Fin64 program frames a preserved payload and appends the V2
item to the existing row body. Append scratch 11/14 is blank at entry. -/

namespace CurrentAdditive.V2FeatureFrameAppend64

open Turing Turing.TM2 EthInapproximability.CurrentPaper BitMachineEncoding
open V2ItemFrameCore V2FeatureFrameLayout64

noncomputable def program := BitMachineRawSequence.program
  (V2ItemFrameCore.program V2FeatureFrameLayout64.slots) GaussV2BodyAppend64.program
  (CodeDAppendAtEnd15.Label.saveScan) (V2ItemFrameCore.control V2FeatureFrameLayout64.slots) ((), none)

theorem untouched (S : Fin 64 → List Bool) (raw : List Bool) (j : Fin 64)
    (hj5 : j ≠ 5) (hj7 : j ≠ 7)
    (hm : ∀ i, j ≠ V2FeatureFrameLayout64.slots.machine i) :
    (Function.update (cleared V2FeatureFrameLayout64.slots S) 5
      (EncodedCommunication.natField raw.length ++ raw)) j = S j := by
  exact V2ItemFrameForeign.framed_foreign V2FeatureFrameLayout64.slots S raw j hj5 hj7 hm

theorem run (S : Fin 64 → List Bool) (raw body : List Bool)
    (hs : S 36 = raw) (hb : S 9 = body)
    (h11 : S 11 = []) (h14 : S 14 = []) :
    ∃ t ≤ time V2FeatureFrameLayout64.slots S raw +
        (4*body.length + 2*(EncodedCommunication.natField raw.length ++ raw).length+7)+1,
      ∃ (v : GaussV2BodyAppend64.Control) (U : Fin 64 → List Bool),
        ((advance program)^[t])
          (⟨some (BitMachineRawSequence.leftLabel (V2ItemFrameCore.start V2FeatureFrameLayout64.slots)),
            (V2ItemFrameCore.control V2FeatureFrameLayout64.slots, ((), none)), S⟩ :
            TM2.Cfg (fun _ : Fin 64 => Bool) _ _) =
          ⟨none, (V2ItemFrameCore.control V2FeatureFrameLayout64.slots,v), U⟩ ∧
        U 9 = body ++ (EncodedCommunication.natField raw.length ++ raw) ∧
        U 5 = [] ∧
        U 7 = [] ∧
        (∀ j : Fin 64, j ≠ 5 → j ≠ 9 → j ≠ 11 → j ≠ 14 →
          j ≠ 7 → (∀ i, j ≠ V2FeatureFrameLayout64.slots.machine i) → U j = S j) := by
  let field := EncodedCommunication.natField raw.length ++ raw
  let F := Function.update (cleared V2FeatureFrameLayout64.slots S) 5 field
  have h9m : ∀ i, (9 : Fin 64) ≠ V2FeatureFrameLayout64.slots.machine i := by
    intro i; fin_cases i <;> decide
  have h11m : ∀ i, (11 : Fin 64) ≠ V2FeatureFrameLayout64.slots.machine i := by
    intro i; fin_cases i <;> decide
  have h14m : ∀ i, (14 : Fin 64) ≠ V2FeatureFrameLayout64.slots.machine i := by
    intro i; fin_cases i <;> decide
  have hF9 : F 9 = body := by
    calc F 9 = S 9 := untouched S raw 9 (by decide) (by decide) h9m
      _ = body := hb
  have hF11 : F 11 = [] := by
    exact (untouched S raw 11 (by decide) (by decide) h11m).trans h11
  have hF14 : F 14 = [] := by
    exact (untouched S raw 14 (by decide) (by decide) h14m).trans h14
  have hF5 : F 5 = field := by simp [F]
  obtain ⟨a, ha, hra⟩ := V2FeatureFrameLayout64.run S raw hs
  obtain ⟨b, hbnd, hhalt, hout, hpay, _h8, hforeign⟩ :=
    GaussV2BodyAppend64.append F body field hF9 hF5 hF11 hF14
  let U := (GaussV2BodyAppend64.run b
    ⟨some .saveScan, ((), none), F⟩).stk
  let v := (GaussV2BodyAppend64.run b
    ⟨some .saveScan, ((), none), F⟩).var
  have hrb : ((advance GaussV2BodyAppend64.program)^[b])
      (⟨some .saveScan, ((), none), F⟩ : GaussV2BodyAppend64.Config) =
      ⟨none, v, U⟩ := by
    change GaussV2BodyAppend64.run b ⟨some .saveScan, ((), none), F⟩ = _
    cases h : GaussV2BodyAppend64.run b ⟨some .saveScan, ((), none), F⟩ with
    | mk l w B =>
        cases l with
        | none => simp [v, U, h]
        | some l => simp [h] at hhalt
  obtain ⟨t, ht, hrun⟩ := BitMachineRawSequence.runs
    (V2ItemFrameCore.program V2FeatureFrameLayout64.slots) GaussV2BodyAppend64.program
    (V2ItemFrameCore.start V2FeatureFrameLayout64.slots) .saveScan
    (V2ItemFrameCore.control V2FeatureFrameLayout64.slots) (V2ItemFrameCore.control V2FeatureFrameLayout64.slots)
    ((), none) v S F U a b hra hrb
  have hbudget : t ≤ time V2FeatureFrameLayout64.slots S raw +
      (4*body.length + 2*(EncodedCommunication.natField raw.length ++ raw).length+7)+1 := by
    dsimp only [field] at hbnd
    omega
  refine ⟨t, hbudget, v, U,
    ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [program] using hrun
  · exact hout
  · exact hpay
  · have hF7 : F 7 = [] := by
      change (Function.update (cleared V2FeatureFrameLayout64.slots S) 5 field) 7 = []
      rw [Function.update_of_ne (by decide)]
      exact V2ItemFrameCore.cleared_scratch V2FeatureFrameLayout64.slots S
    exact (hforeign 7 (by decide) (by decide) (by decide) (by decide)).trans hF7
  · intro j hj5 hj9 hj11 hj14 hj7 hjm
    exact (hforeign j hj5 hj9 hj11 hj14).trans
      (untouched S raw j hj5 hj7 hjm)

#print axioms run

end CurrentAdditive.V2FeatureFrameAppend64
