import CurrentAdditive.GaussConcreteGridRun
import CurrentAdditive.GaussConcreteRowClock

namespace CurrentAdditive.GaussConcreteGridClock
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open GaussCellFieldFrame (Bank loc fresh old)
open GaussConcreteCellEntry (N)
open GaussConcreteGrid

theorem actual_row_clock {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot i : Fin m) (c : Fin k) (hn : B pivot c≠0) :
    ∃ t ≤ GaussConcreteRowClock.clock B r pivot c, ((advance rowProgram)^[t])
      (GaussWordGridTraversal.cellCfg (some GaussConcreteRow.start) GaussConcreteRow.control
        (persistent B r pivot c) i.val 0 []) =
      GaussWordGridTraversal.cellCfg none GaussConcreteRow.control
        (persistent B r pivot c) i.val 0 (value B r pivot c i.val 0) := by
  let S := (GaussWordGridTraversal.cellCfg (L := GaussConcreteRow.Label)
    (some GaussConcreteRow.start) GaussConcreteRow.control
      (persistent B r pivot c) i.val 0 []).stk
  have hrestriction : (fun z => S (rowSlots z))=(GaussConcreteRow.initialData B r pivot i c).contents := by
    funext z
    rcases z with ((z|z)|z)
    · simp [S,rowSlots,rowMap,persistent,GaussConcreteRow.initialData,
        GaussWordGridTraversal.cellCfg,GaussWordRowTraversal.ready,
        GaussWordRowTraversal.Data.contents,GaussWordRowTraversal.Data.cell,z.isLt]
    · fin_cases z <;> simp [S,rowSlots,rowMap,persistent,GaussConcreteRow.initialData,
        GaussWordGridTraversal.cellCfg,GaussWordRowTraversal.ready,
        GaussWordRowTraversal.Data.contents,GaussWordRowTraversal.Data.cell]
    · cases z <;> simp [S,rowSlots,rowMap,persistent,GaussConcreteRow.initialData,
        GaussWordGridTraversal.cellCfg,GaussWordRowTraversal.ready,
        GaussWordRowTraversal.Data.contents,GaussWordRowTraversal.Data.foreign]
  obtain ⟨t,ht,hrun⟩ := GaussConcreteRowClock.physical_row_clock B r pivot i c hn
  rw [←hrestriction] at hrun
  obtain ⟨u,hu,he⟩ := GaussCellCursorEmbedding.outputs_update rowSlots
    GaussConcreteRow.program GaussConcreteRow.start GaussConcreteRow.control
    GaussConcreteRow.control S (.inr .output)
    (V2FieldContext.field (GaussConcreteRow.rowBits B r pivot c i.val)) t hrun
  refine ⟨u,hu.trans ht,he.trans ?_⟩
  apply congrArg (fun bank => (⟨none,GaussConcreteRow.control,bank⟩ :
    TM2.Cfg (fun _ : Cell => Bool) GaussConcreteRow.Label GaussConcreteRow.Control))
  funext z
  cases z with
  | inl z => simp [S,rowSlots,rowMap,GaussWordGridTraversal.cellCfg]
  | inr z => fin_cases z <;>
      simp [S,rowSlots,rowMap,GaussWordGridTraversal.cellCfg,value,i.isLt]

theorem bounded_entry {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) (hn : B pivot c≠0) :
    GaussWordGridTraversal.EntryRuns rowProgram GaussConcreteRow.start
      GaussConcreteRow.control (persistent B r pivot c) m 1
      (GaussConcreteRowClock.clock B r pivot c) (value B r pivot c) := by
  intro x hx y hy
  have hy0 : y=0 := by omega
  subst y
  obtain ⟨t,ht,he⟩ := actual_row_clock B r pivot ⟨x,hx⟩ c hn
  exact ⟨t,ht,GaussConcreteRow.control,he⟩

def valueCap {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) : Nat :=
  ∑ i : Fin m,(GaussConcreteGrid.value B r pivot c i.val 0).length

theorem value_length_le {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) :
    ∀ x y,(GaussConcreteGrid.value B r pivot c x y).length ≤ valueCap B r pivot c := by
  intro x y
  by_cases h : x < m ∧ y < 1
  · have hy : y=0 := by omega
    subst y
    exact Finset.single_le_sum (f := fun i : Fin m =>
      (GaussConcreteGrid.value B r pivot c i.val 0).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ ⟨x,h.1⟩)
  · rw [GaussConcreteGrid.value,if_neg h]
    exact Nat.zero_le _

def clock {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) : Nat :=
  GaussCountHeader.clock m+
  GaussWordGridTraversal.writerBound m 1 (GaussConcreteRowClock.clock B r pivot c)
    (valueCap B r pivot c)+(EncodedCommunication.natField m).length+1

theorem physical_grid_clock {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) (hn : B pivot c≠0) :
    ∃ t ≤ clock B r pivot c, ∃ v : GaussConcreteGrid.Control,
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
  let T := GaussConcreteRowClock.clock B r pivot c
  have hcells := bounded_entry B r pivot c hn
  let L := valueCap B r pivot c
  have hlen := value_length_le B r pivot c
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
    have hbits := GaussConcreteGridRun.matrixBits_exact B r pivot c
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
  refine ⟨t,?_,(GaussCountHeader.control,vb),hfull⟩
  unfold clock
  change b ≤ GaussWordGridTraversal.writerBound m 1 (GaussConcreteRowClock.clock B r pivot c) (valueCap B r pivot c)+(EncodedCommunication.natField m).length at hb
  omega

#print axioms actual_row_clock
#print axioms physical_grid_clock
end
end CurrentAdditive.GaussConcreteGridClock
