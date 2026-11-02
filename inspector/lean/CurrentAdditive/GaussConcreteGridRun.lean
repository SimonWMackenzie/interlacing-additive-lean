import CurrentAdditive.GaussConcreteGrid

namespace CurrentAdditive.GaussConcreteGridRun

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open GaussCellFieldFrame GaussConcreteCellEntry GaussConcreteGrid

theorem value_length_bound {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) :
    ∃ L : Nat, ∀ x y,(GaussConcreteGrid.value B r pivot c x y).length ≤ L := by
  let L := ∑ i : Fin m,(GaussConcreteGrid.value B r pivot c i.val 0).length
  refine ⟨L,?_⟩
  intro x y
  by_cases h : x < m ∧ y < 1
  · have hy : y=0 := by omega
    subst y
    let i : Fin m := ⟨x,h.1⟩
    exact Finset.single_le_sum
      (f := fun i : Fin m => (GaussConcreteGrid.value B r pivot c i.val 0).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  · rw [GaussConcreteGrid.value,if_neg h]
    exact Nat.zero_le _

theorem matrixBits_exact {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) :
    EncodedCommunication.natField m ++
      GaussWordGridTraversal.tableWord (GaussConcreteGrid.value B r pivot c) 1 0 m =
      GaussPhysical.encodeTypedMatrix
        (SequentialTotality.clearTyped (SequentialTotality.swapTyped B r pivot) r c) := by
  have h := GaussWordGridTraversal.tableWord_finite
    (GaussConcreteGrid.value B r pivot c) 1 0 m 1 rfl
    (fun i _ => V2FieldContext.field (GaussConcreteRow.rowBits B r pivot c i.val))
    (by intro i j; simp [GaussConcreteGrid.value,i.isLt,j.isLt])
  rw [h,GaussTypedGetterBridge.encodeTypedMatrix_eq]
  simp [SourceListEncoding.encode,GaussTypedGetterBridge.rowWords,
    GaussNestedFraming64.fields_eq_flatMap,GaussNestedFraming64.frameWord,
    SourceListMachineWriter.result,V2FieldContext.field,List.flatMap_map,
    GaussConcreteRowEncoding.rowBits_exact,List.finRange_succ]

/-- One actual program generates the outer count header, invokes the complete
physical row routine for each row, and returns the literal typed matrix
encoding. The starting configuration is a prepared physical bank; serialized
input preparation and fixed finite-machine packaging remain separate. -/
theorem physical_grid {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) (hn : B pivot c≠0) :
    ∃ t : Nat, ∃ v : GaussConcreteGrid.Control,
      ((advance GaussConcreteGrid.program)^[t])
        (⟨some GaussConcreteGrid.start,GaussConcreteGrid.control,
          (GaussConcreteGrid.initialData B r pivot c).contents⟩ :
            TM2.Cfg (fun _ : GaussConcreteGrid.Stack => Bool)
              GaussConcreteGrid.Label GaussConcreteGrid.Control) =
        ⟨none,v,Function.update (GaussConcreteGrid.initialData B r pivot c).contents
          (.inr .output) (GaussPhysical.encodeTypedMatrix
            (SequentialTotality.clearTyped (SequentialTotality.swapTyped B r pivot) r c))⟩ := by
  let D := GaussConcreteGrid.initialData B r pivot c
  let S := D.contents
  let H := fun z => S (GaussConcreteGrid.headerSlots z)
  have h28 : H (loc 28)=List.replicate m true := by
    simp [H,S,D,GaussConcreteGrid.initialData,GaussConcreteGrid.headerSlots,
      GaussConcreteGrid.headerMap,loc,old,GaussFetchedArithmetic.lower,
      GaussWordGridTraversal.ready,GaussWordGridTraversal.Data.contents,
      GaussWordGridTraversal.Data.foreign]
  have h29 : H (loc 29)=[] := by
    have hN : 29 < N := by dsimp [N]; omega
    simp [H,S,D,GaussConcreteGrid.initialData,GaussConcreteGrid.headerSlots,
      GaussConcreteGrid.headerMap,GaussConcreteGrid.persistent,GaussConcreteCellEntry.persistent,
      loc,old,GaussFetchedArithmetic.lower,hN,
      GaussWordGridTraversal.ready,GaussWordGridTraversal.Data.contents,GaussWordGridTraversal.Data.cell]
  have h30 : H (loc 30)=[] := by
    simp [H,S,D,GaussConcreteGrid.initialData,GaussConcreteGrid.headerSlots,
      GaussConcreteGrid.headerMap,loc,old,GaussFetchedArithmetic.lower,
      GaussWordGridTraversal.ready,GaussWordGridTraversal.Data.contents,GaussWordGridTraversal.Data.foreign]
  have hblank (z : Fin 10) : H (fresh z)=[] := by
    have hz (n : Nat) (hn : n < 64) : 64+GaussFetchedArithmetic.M.stackCount+z.val≠n := by omega
    have hN : 64+GaussFetchedArithmetic.M.stackCount+z.val < N := by have h:=z.isLt; dsimp [N]; omega
    simp [H,S,D,GaussConcreteGrid.initialData,GaussConcreteGrid.headerSlots,
      GaussConcreteGrid.headerMap,GaussConcreteGrid.persistent,GaussConcreteCellEntry.persistent,
      fresh,hN,hz 28 (by decide),hz 30 (by decide),hz 8 (by decide),hz 9 (by decide),
      hz 10 (by decide),hz 20 (by decide),
      GaussWordGridTraversal.ready,GaussWordGridTraversal.Data.contents,GaussWordGridTraversal.Data.cell]
  obtain ⟨a,ha,hheader⟩ := GaussCountHeader.physical_header H m h28 h29 h30 hblank
  obtain ⟨a',ha',hheader'⟩ := GaussCellCursorEmbedding.outputs_update GaussConcreteGrid.headerSlots
    GaussCountHeader.program GaussCountHeader.start GaussCountHeader.control GaussCountHeader.control
    S (loc 30) (EncodedCommunication.natField m).reverse a hheader
  let D1 := GaussWordGridTraversal.ready (GaussConcreteGrid.persistent B r pivot c)
    m 1 0 0 0 0 (EncodedCommunication.natField m).reverse []
  have hD1 : Function.update S (GaussConcreteGrid.headerSlots (loc 30))
      (EncodedCommunication.natField m).reverse = D1.contents := by
    funext z
    cases z with
    | inl z => simp [S,D,D1,GaussConcreteGrid.initialData,GaussConcreteGrid.headerSlots,
        GaussConcreteGrid.headerMap,loc,old,GaussFetchedArithmetic.lower,
        GaussWordGridTraversal.ready,GaussWordGridTraversal.Data.contents,GaussWordGridTraversal.Data.cell]
    | inr z => cases z <;> simp [S,D,D1,GaussConcreteGrid.initialData,GaussConcreteGrid.headerSlots,
        GaussConcreteGrid.headerMap,loc,old,GaussFetchedArithmetic.lower,
        GaussWordGridTraversal.ready,GaussWordGridTraversal.Data.contents,GaussWordGridTraversal.Data.foreign]
  rw [hD1] at hheader'
  obtain ⟨T,hcells⟩ := GaussConcreteGrid.entry_runs B r pivot c hn
  obtain ⟨L,hlen⟩ := value_length_bound B r pivot c
  obtain ⟨b,hb,vb,hbody⟩ := GaussWordGridTraversal.write_table_with_prefix
    GaussConcreteGrid.rowProgram GaussConcreteRow.start GaussConcreteRow.control
    (GaussConcreteGrid.persistent B r pivot c) m 1 T L
    (GaussConcreteGrid.value B r pivot c) hcells hlen (EncodedCommunication.natField m) []
  let result := GaussPhysical.encodeTypedMatrix
    (SequentialTotality.clearTyped (SequentialTotality.swapTyped B r pivot) r c)
  have hbody' : ((advance GaussConcreteGrid.matrixProgram)^[b])
      (⟨some GaussConcreteGrid.matrixStart,GaussConcreteGrid.matrixControl,D1.contents⟩ :
        TM2.Cfg (fun _ : GaussConcreteGrid.Stack => Bool) _ _) =
      ⟨none,vb,Function.update S (.inr .output) result⟩ := by
    have hbits := matrixBits_exact B r pivot c
    simp only [List.append_nil,hbits] at hbody
    convert hbody using 1
    apply congrArg (fun bank => (⟨none,vb,bank⟩ :
      TM2.Cfg (fun _ : GaussConcreteGrid.Stack => Bool)
        (GaussWordGridTraversal.Label GaussConcreteRow.Label)
        (GaussWordGridTraversal.Control GaussConcreteRow.Control)))
    funext z
    cases z with
    | inl z => rfl
    | inr z => cases z <;> rfl
  obtain ⟨t,ht,hfull⟩ := BitMachineRawSequence.runs
    GaussConcreteGrid.headerProgram GaussConcreteGrid.matrixProgram
    GaussCountHeader.start GaussConcreteGrid.matrixStart
    GaussCountHeader.control GaussCountHeader.control GaussConcreteGrid.matrixControl vb
    S D1.contents (Function.update S (.inr .output) result) a' b hheader' hbody'
  exact ⟨t,(GaussCountHeader.control,vb),hfull⟩

#print axioms matrixBits_exact
#print axioms physical_grid
end
end CurrentAdditive.GaussConcreteGridRun
