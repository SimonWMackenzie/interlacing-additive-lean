import CurrentAdditive.SourceContextScheduler96

/-! The higher banks of the actual Fin96 selected tuple frame.  Bank 33
holds the immutable unary q cap; every other high scratch bank starts empty. -/

namespace CurrentAdditive.CylinderGeneralSelectedFrame96

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.GaussListContext
open CurrentAdditive.Wide96ContextListScheduler

def evaluationExtra (q : Nat) : Fin 96 → List Bool :=
  fun k => if k = 33 then List.replicate q true else []

noncomputable def selected (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (output context : List Bool)
    (q : Nat) : Wide96ContextPreservingScan.Config :=
  Wide96ContextPreservingScan.frame
    (foreignBank output context suffix.length (evaluationExtra q))
    (⟨none,
      CylinderContextScanStep.getterControl
        (PreservingV2Program.v2Control
          (IndexedV2Program.indexControl
            (SourceListMachineFields.coreControl (some true, false), none))),
      CylinderContextScanStep.selectedBank
        (SourceListEncoding.encode (pre ++ word :: suffix))
        (SourceListEncoding.fields suffix) word pre.length⟩ :
          CylinderContextScanStep.Config)

theorem selected_extra (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (output context : List Bool)
    (q : Nat) (k : Fin 96) (hk : 15 ≤ k.val) :
    (selected pre word suffix output context q).stk k =
      evaluationExtra q k := by
  unfold selected
  rw [Wide96ContextPreservingScan.frame_foreign]
  · exact foreignBank_extra output context suffix.length
      (evaluationExtra q) k hk
  · rintro ⟨j, hj⟩
    have hsmall : (Wide96ContextPreservingScan.locate j).val < 15 := by
      fin_cases j <;> decide
    have heq := congrArg Fin.val hj
    omega

theorem selected_cap (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (output context : List Bool)
    (q : Nat) :
    (selected pre word suffix output context q).stk 33 =
      List.replicate q true := by
  rw [selected_extra pre word suffix output context q 33 (by decide)]
  simp [evaluationExtra]

theorem selected_scratch (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (output context : List Bool)
    (q : Nat) (k : Fin 96) (hk : 15 ≤ k.val) (hne : k ≠ 33) :
    (selected pre word suffix output context q).stk k = [] := by
  rw [selected_extra pre word suffix output context q k hk]
  simp [evaluationExtra, hne]

theorem selected_word (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (output context : List Bool)
    (q : Nat) :
    (selected pre word suffix output context q).stk 6 = word := by
  simpa [selected] using Wide96ContextPreservingScan.selected_word
    (SourceListEncoding.encode (pre ++ word :: suffix))
    (SourceListEncoding.fields suffix) word pre.length
    (foreignBank output context suffix.length (evaluationExtra q))

theorem selected_suffix (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (output context : List Bool)
    (q : Nat) :
    (selected pre word suffix output context q).stk 0 =
      SourceListEncoding.fields suffix := by
  simpa [selected, CylinderContextScanStep.selectedBank,
    Wide96ContextPreservingScan.locate] using
    Wide96ContextPreservingScan.frame_bank
      (foreignBank output context suffix.length (evaluationExtra q))
      (⟨none,
        CylinderContextScanStep.getterControl
          (PreservingV2Program.v2Control
            (IndexedV2Program.indexControl
              (SourceListMachineFields.coreControl
                (some true, false), none))),
        CylinderContextScanStep.selectedBank
          (SourceListEncoding.encode (pre ++ word :: suffix))
          (SourceListEncoding.fields suffix) word pre.length⟩ :
            CylinderContextScanStep.Config) 0

theorem selected_source (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (output context : List Bool)
    (q : Nat) :
    (selected pre word suffix output context q).stk 8 =
      SourceListEncoding.encode (pre ++ word :: suffix) := by
  simpa [selected] using Wide96ContextPreservingScan.selected_source
    (SourceListEncoding.encode (pre ++ word :: suffix))
    (SourceListEncoding.fields suffix) word pre.length
    (foreignBank output context suffix.length (evaluationExtra q))

theorem selected_output (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (output context : List Bool)
    (q : Nat) :
    (selected pre word suffix output context q).stk 9 = output := by
  rw [selected, Wide96ContextPreservingScan.output_preserved]
  simp [foreignBank]

theorem selected_index (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (output context : List Bool)
    (q : Nat) :
    (selected pre word suffix output context q).stk 10 =
      List.replicate pre.length true := by
  simpa [selected, CylinderContextScanStep.selectedBank,
    Wide96ContextPreservingScan.locate] using
    Wide96ContextPreservingScan.frame_bank
      (foreignBank output context suffix.length (evaluationExtra q))
      (⟨none,
        CylinderContextScanStep.getterControl
          (PreservingV2Program.v2Control
            (IndexedV2Program.indexControl
              (SourceListMachineFields.coreControl
                (some true, false), none))),
        CylinderContextScanStep.selectedBank
          (SourceListEncoding.encode (pre ++ word :: suffix))
          (SourceListEncoding.fields suffix) word pre.length⟩ :
            CylinderContextScanStep.Config) 10

theorem selected_context_fuel (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (output context : List Bool)
    (q : Nat) :
    (selected pre word suffix output context q).stk 12 = context ∧
    (selected pre word suffix output context q).stk 13 =
      List.replicate suffix.length true := by
  have h := Wide96ContextPreservingScan.context_preserved
    (foreignBank output context suffix.length (evaluationExtra q))
    (⟨none,
      CylinderContextScanStep.getterControl
        (PreservingV2Program.v2Control
          (IndexedV2Program.indexControl
            (SourceListMachineFields.coreControl
              (some true, false), none))),
      CylinderContextScanStep.selectedBank
        (SourceListEncoding.encode (pre ++ word :: suffix))
        (SourceListEncoding.fields suffix) word pre.length⟩ :
          CylinderContextScanStep.Config)
  simpa [selected, foreignBank] using h

#print axioms selected_extra
#print axioms selected_cap
#print axioms selected_scratch
#print axioms selected_word
#print axioms selected_suffix
#print axioms selected_source
#print axioms selected_output
#print axioms selected_index
#print axioms selected_context_fuel

end CurrentAdditive.CylinderGeneralSelectedFrame96
