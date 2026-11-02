import CurrentAdditive.CylinderCoordinateEqualityCallback

/-!
The real Fin32 counted-list frame for one fixed cylinder pair.  The selected
tuple word on bank 6 is routed into the physical coordinate callback; the
coordinate address and expected symbol are fixed extra registers on 15/16.
This is the one-pair row layer.  Multi-pair conjunction and feature
enumeration remain separate.
-/

namespace CurrentAdditive.CylinderCoordinateRowRun

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.GaussListContext
open CurrentAdditive.CylinderCoordinateEqualityCallback
open CurrentAdditive.LargeContextListScheduler

def pairExtra (index : Nat) (symbol : List Bool) :
    Fin 32 → List Bool :=
  fun k => if k = 15 then List.replicate index true
    else if k = 16 then symbol else []

noncomputable def selected (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (output context : List Bool)
    (index : Nat) (symbol : List Bool) :
    LargeContextPreservingScan.Config :=
  let source := SourceListEncoding.encode (pre ++ word :: suffix)
  LargeContextPreservingScan.frame
    (foreignBank output context suffix.length (pairExtra index symbol))
    ⟨none,
     CylinderContextScanStep.getterControl
       (PreservingV2Program.v2Control
         (IndexedV2Program.indexControl
           (SourceListMachineFields.coreControl (some true, false), none))),
     CylinderContextScanStep.selectedBank source
       (SourceListEncoding.fields suffix) word pre.length⟩

theorem selected_word (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (output context : List Bool)
    (index : Nat) (symbol : List Bool) :
    (selected pre word suffix output context index symbol).stk 6 = word := by
  simpa [selected, CylinderContextScanStep.selectedBank] using
    LargeContextPreservingScan.frame_bank
      (foreignBank output context suffix.length (pairExtra index symbol))
      (⟨none,
       CylinderContextScanStep.getterControl
         (PreservingV2Program.v2Control
           (IndexedV2Program.indexControl
             (SourceListMachineFields.coreControl (some true, false), none))),
       CylinderContextScanStep.selectedBank
         (SourceListEncoding.encode (pre ++ word :: suffix))
         (SourceListEncoding.fields suffix) word pre.length⟩ :
        CylinderContextScanStep.Config) 6

theorem selected_foreign (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (output context : List Bool)
    (index : Nat) (symbol : List Bool) (k : Fin 32)
    (hk : ¬ ∃ i : Fin 12, LargeContextPreservingScan.locate i = k) :
    (selected pre word suffix output context index symbol).stk k =
      (foreignBank output context suffix.length
        (pairExtra index symbol)) k := by
  simpa [selected] using LargeContextPreservingScan.frame_foreign
    (foreignBank output context suffix.length (pairExtra index symbol))
    (⟨none,
     CylinderContextScanStep.getterControl
       (PreservingV2Program.v2Control
         (IndexedV2Program.indexControl
           (SourceListMachineFields.coreControl (some true, false), none))),
     CylinderContextScanStep.selectedBank
       (SourceListEncoding.encode (pre ++ word :: suffix))
       (SourceListEncoding.fields suffix) word pre.length⟩ :
      CylinderContextScanStep.Config) k hk

theorem selected_extra (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (output context : List Bool)
    (index : Nat) (symbol : List Bool) (k : Fin 32)
    (hk : 15 ≤ k.val) :
    (selected pre word suffix output context index symbol).stk k =
      pairExtra index symbol k := by
  rw [selected_foreign pre word suffix output context index symbol k]
  · have h9 : k ≠ (9 : Fin 32) := by
      intro h
      have hv := congrArg Fin.val h
      omega
    have h12 : k ≠ (12 : Fin 32) := by
      intro h
      have hv := congrArg Fin.val h
      omega
    have h13 : k ≠ (13 : Fin 32) := by
      intro h
      have hv := congrArg Fin.val h
      omega
    simp [foreignBank, h9, h12, h13]
  · intro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    fin_cases i <;> simp [LargeContextPreservingScan.locate] at hv <;>
      omega

theorem selected_output (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (output context : List Bool)
    (index : Nat) (symbol : List Bool) :
    (selected pre word suffix output context index symbol).stk 9 = output := by
  rw [selected_foreign pre word suffix output context index symbol 9
    (by decide)]
  simp [foreignBank]

theorem getter_match (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (output context : List Bool)
    (index : Nat) (symbol : List Bool) :
    let S := (selected pre word suffix output context index symbol).stk
    getterFrame S (CylinderContextScanStep.initial word index) =
      ⟨some (.inl (.inl .scan)),
       getterControl (CylinderContextScanStep.copyControl ((), none)),
       S⟩ := by
  dsimp only
  let S := (selected pre word suffix output context index symbol).stk
  have h6 : S 6 = word :=
    selected_word pre word suffix output context index symbol
  have h15 : S 15 = List.replicate index true := by
    simpa [S, pairExtra] using selected_extra pre word suffix
      output context index symbol 15 (by decide)
  have hs (k : Fin 32) (hk : 17 ≤ k.val) : S k = [] := by
    simpa [S, pairExtra, show k ≠ (15 : Fin 32) by omega,
      show k ≠ (16 : Fin 32) by omega]
      using selected_extra pre word suffix output context index symbol
        k (by omega)
  change (selected pre word suffix output context index symbol).stk 6 =
    word at h6
  change (selected pre word suffix output context index symbol).stk 15 =
    List.replicate index true at h15
  change ∀ k : Fin 32, 17 ≤ k.val →
    (selected pre word suffix output context index symbol).stk k = []
    at hs
  unfold getterFrame BitMachineStackEmbedding.cfg
    BitMachineStackEmbedding.stackCfg BitMachineInline.cfg
  congr 1
  apply BitMachineStackEmbedding.bank_eq_self
  intro k
  fin_cases k <;>
    simp [getterStack, CylinderContextScanStep.initial,
      CylinderContextScanStep.initialBank, h6, h15, hs]

theorem canonical_selected_run (outerPre : List (List Bool))
    (outerWord : List Bool) (outerSuffix : List (List Bool))
    (coordPre : List (List Bool)) (coordWord : List Bool)
    (coordSuffix : List (List Bool))
    (output context symbol : List Bool)
    (hword : outerWord = SourceListEncoding.encode
      (coordPre ++ coordWord :: coordSuffix))
    (index : Nat) (hindex : index = coordPre.length) :
    let S := (selected outerPre outerWord outerSuffix output
      context index symbol).stk
    ∃ (t : Nat) (vFinal : CylinderCoordinateEqualityCallback.Control)
      (SFinal SBefore : Fin 32 → List Bool),
      t ≤ getterBound coordPre coordWord coordSuffix + 1 +
        CylinderEqualityAppendCallback.callbackBound
          coordWord symbol output +
        (∑ i : Fin 15, (SBefore (cleanBank i)).length) + 17 ∧
      CylinderCoordinateEqualityCallback.run t
        ⟨some (.inl (.inl .scan)),
         getterControl (CylinderContextScanStep.copyControl ((), none)),
         S⟩ = ⟨none, vFinal, SFinal⟩ ∧
      SFinal 9 = output ++ [decide (coordWord = symbol)] ∧
      (∀ i : Fin 15, SFinal (cleanBank i) = []) ∧
      (∀ k : Fin 32,
        k = 8 ∨ k = 10 ∨ k = 12 ∨ k = 13 ∨ k = 15 ∨ k = 16 →
          SFinal k = S k) := by
  dsimp only
  let S := (selected outerPre outerWord outerSuffix output
    context index symbol).stk
  have h16 : S 16 = symbol := by
    simpa [S, pairExtra] using selected_extra outerPre outerWord
      outerSuffix output context index symbol 16 (by decide)
  have h9 : S 9 = output :=
    selected_output outerPre outerWord outerSuffix output context
      index symbol
  have h27 : S 27 = [] := by
    simpa [S, pairExtra] using selected_extra outerPre outerWord
      outerSuffix output context index symbol 27 (by decide)
  have h28 : S 28 = [] := by
    simpa [S, pairExtra] using selected_extra outerPre outerWord
      outerSuffix output context index symbol 28 (by decide)
  have h29 : S 29 = [] := by
    simpa [S, pairExtra] using selected_extra outerPre outerWord
      outerSuffix output context index symbol 29 (by decide)
  obtain ⟨t,v,T,B,ht,hr,ho,_,hclean,hpres⟩ :=
    physical_coordinate_pair coordPre coordWord coordSuffix symbol
      output S h16 h9 h27 h28 h29
  have hstart := getter_match outerPre outerWord outerSuffix
    output context index symbol
  change getterFrame S
    (CylinderContextScanStep.initial outerWord index) =
    ⟨some (.inl (.inl .scan)),
     getterControl (CylinderContextScanStep.copyControl ((), none)),
     S⟩ at hstart
  rw [hword, hindex] at hstart
  rw [hstart] at hr
  refine ⟨t,v,T,B,ht,hr,ho,hclean,?_⟩
  intro k hk
  rw [hpres k hk]
  exact congrArg (fun c => c.stk k) hstart

#print axioms selected_word
#print axioms getter_match
#print axioms canonical_selected_run

end CurrentAdditive.CylinderCoordinateRowRun
