import CurrentAdditive.GaussConcreteRow

/-! Explicit phase clock for the same frozen physical row program. The proof
replays its actual header, column traversal and full-row framing phases. -/

namespace CurrentAdditive.GaussConcreteRowClock

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open GaussConcreteRow
open GaussCellFieldFrame (Bank loc fresh old)
open GaussConcreteCellEntry (N dataCap value persistent cursor)
open CurrentAdditive.MinimumRatioContext

def cellClock {m k : Nat} (B : Fin m → Fin k → ℚ) : Nat :=
  GaussCellInitialClock.framedCap (dataCap B) (dataCap B)

def valueCap {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) : Nat :=
  ∑ i : Fin m,∑ j : Fin k,(value B r pivot c i.val j.val).length

theorem bounded_entry {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) (hn : B pivot c≠0) :
    GaussWordRowTraversal.EntryRuns GaussConcreteCellEntry.program GaussFramedCell.start
      GaussFramedCell.control (persistent B r pivot c) m k (cellClock B) (value B r pivot c) := by
  intro x hx y hy
  exact GaussConcreteCellEntry.actual_cell B r pivot ⟨x,hx⟩ c ⟨y,hy⟩ hn

theorem value_length_le {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) : ∀ x y,(value B r pivot c x y).length ≤ valueCap B r pivot c := by
  intro x y
  by_cases hx : x < m
  · by_cases hy : y < k
    · let i : Fin m := ⟨x,hx⟩
      let j : Fin k := ⟨y,hy⟩
      have h1 := Finset.single_le_sum (f := fun j : Fin k =>
        (value B r pivot c i.val j.val).length)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      have h2 := Finset.single_le_sum (f := fun i : Fin m => ∑ j : Fin k,
        (value B r pivot c i.val j.val).length)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      exact h1.trans h2
    · simp [value,hy]
  · simp [value,hx]

def rowCap {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) : Nat :=
  (EncodedCommunication.natField k).length+k*valueCap B r pivot c

theorem rowBits_length_le {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) (x : Nat) :
    (rowBits B r pivot c x).length ≤ rowCap B r pivot c := by
  have h := GaussWordRowTraversal.rowWord_length_le (value B r pivot c)
    (valueCap B r pivot c) x 0 k (value_length_le B r pivot c)
  simpa only [rowBits,List.length_append,rowCap] using
    Nat.add_le_add_left h (EncodedCommunication.natField k).length

theorem frame_clock_le (word : List Bool) (n : Nat) (hn : word.length ≤ n) :
    V2FieldContext.clock word ≤ V2FieldContext.clock (List.replicate n true) := by
  unfold V2FieldContext.clock MachineInvokeFull.uniformBound
  simp only [List.length_replicate]
  gcongr

def clock {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) : Nat :=
  GaussCountHeader.clock k+
    GaussWordRowTraversal.writerBound k (cellClock B) (valueCap B r pivot c)+
    (EncodedCommunication.natField k).length+4*rowCap B r pivot c+
    V2FieldContext.clock (List.replicate (rowCap B r pivot c) true)+11

theorem physical_row_clock {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot i : Fin m) (c : Fin k) (hn : B pivot c≠0) :
    ∃ t ≤ clock B r pivot c, ((advance program)^[t])
      (⟨some start,control,(initialData B r pivot i c).contents⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Label Control) =
      ⟨none,control,Function.update (initialData B r pivot i c).contents
        (.inr .output) (V2FieldContext.field (rowBits B r pivot c i.val))⟩ := by
  let D := initialData B r pivot i c
  let S := D.contents
  let H := fun z => S (headerSlots z)
  have h28 : H (loc 28)=List.replicate k true := by
    simp [H,S,D,initialData,headerSlots,headerMap,loc,old,GaussFetchedArithmetic.lower,
      GaussWordRowTraversal.ready,GaussWordRowTraversal.Data.contents,GaussWordRowTraversal.Data.foreign]
  have h29 : H (loc 29)=[] := by
    simp [H,S,D,initialData,headerSlots,headerMap,cursor,GaussCellCursorEmbedding.slots,
      GaussCellCursorEmbedding.cursor,loc,old,GaussFetchedArithmetic.lower,
      GaussWordRowTraversal.ready,GaussWordRowTraversal.Data.contents,GaussWordRowTraversal.Data.cell]
  have h30 : H (loc 30)=[] := by
    simp [H,S,D,initialData,headerSlots,headerMap,loc,old,GaussFetchedArithmetic.lower,
      GaussWordRowTraversal.ready,GaussWordRowTraversal.Data.contents,GaussWordRowTraversal.Data.foreign]
  have hblank (z : Fin 10) : H (fresh z)=[] := by
    have hz (n : Nat) (hn : n < 64) : 64+GaussFetchedArithmetic.M.stackCount+z.val≠n := by omega
    simp [H,S,D,initialData,headerSlots,headerMap,cursor,GaussCellCursorEmbedding.slots,
      GaussCellCursorEmbedding.cursor,fresh,persistent,
      hz 28 (by decide),hz 30 (by decide),hz 7 (by decide),hz 19 (by decide),hz 29 (by decide),
      hz 8 (by decide),hz 9 (by decide),hz 10 (by decide),hz 20 (by decide),
      GaussWordRowTraversal.ready,GaussWordRowTraversal.Data.contents,GaussWordRowTraversal.Data.cell]
  obtain ⟨a,ha,hheader⟩ := GaussCountHeader.physical_header H k h28 h29 h30 hblank
  obtain ⟨a',ha',hheader'⟩ := GaussCellCursorEmbedding.outputs_update headerSlots
    GaussCountHeader.program GaussCountHeader.start GaussCountHeader.control GaussCountHeader.control
    S (loc 30) (EncodedCommunication.natField k).reverse a hheader
  let D1 := GaussWordRowTraversal.ready (persistent B r pivot c) m k i.val 0 0 0
    (EncodedCommunication.natField k).reverse []
  have hD1 : Function.update S (headerSlots (loc 30)) (EncodedCommunication.natField k).reverse =
      D1.contents := by
    funext z
    cases z with
    | inl z => simp [S,D,D1,initialData,headerSlots,headerMap,loc,old,GaussFetchedArithmetic.lower,
        GaussWordRowTraversal.ready,GaussWordRowTraversal.Data.contents,GaussWordRowTraversal.Data.cell]
    | inr z => cases z <;> simp [S,D,D1,initialData,headerSlots,headerMap,loc,old,
        GaussFetchedArithmetic.lower,GaussWordRowTraversal.ready,
        GaussWordRowTraversal.Data.contents,GaussWordRowTraversal.Data.foreign]
  rw [hD1] at hheader'
  let T := cellClock B
  have hcells := bounded_entry B r pivot c hn
  let L := valueCap B r pivot c
  have hlen := value_length_le B r pivot c
  obtain ⟨b,hb,vb,hrow⟩ := GaussWordRowTraversal.write_row_with_prefix
    GaussConcreteCellEntry.program GaussFramedCell.start GaussFramedCell.control
    (persistent B r pivot c) m k T L (value B r pivot c) hcells hlen i.val i.isLt
    (EncodedCommunication.natField k) []
  let D2 := GaussWordRowTraversal.ready (persistent B r pivot c) m k i.val 0 0 0 []
    (rowBits B r pivot c i.val)
  have hrow' : ((advance rowProgram)^[b])
      (⟨some rowStart,rowControl,D1.contents⟩ : TM2.Cfg (fun _ : Stack => Bool) RowLabel RowControl) =
      ⟨none,vb,D2.contents⟩ := by
    simpa only [GaussWordRowTraversal.run,GaussWordRowTraversal.cfg,
      rowProgram,rowStart,rowControl,D1,D2,rowBits,List.append_nil] using hrow
  let F := fun z => D2.contents (frameSlots z)
  have hf29 : F (loc 29)=rowBits B r pivot c i.val := by
    simp [F,D2,frameSlots,frameMap,loc,old,GaussFetchedArithmetic.lower,
      GaussWordRowTraversal.ready,GaussWordRowTraversal.Data.contents,GaussWordRowTraversal.Data.foreign]
  have hf28 : F (loc 28)=[] := by
    simp [F,D2,frameSlots,frameMap,cursor,GaussCellCursorEmbedding.slots,
      GaussCellCursorEmbedding.cursor,loc,old,GaussFetchedArithmetic.lower,persistent,
      GaussWordRowTraversal.ready,GaussWordRowTraversal.Data.contents,GaussWordRowTraversal.Data.cell]
  have hffresh (z : Fin 10) : F (fresh z)=[] := by
    have hz (n : Nat) (hn : n < 64) : 64+GaussFetchedArithmetic.M.stackCount+z.val≠n := by omega
    simp [F,D2,frameSlots,frameMap,cursor,GaussCellCursorEmbedding.slots,
      GaussCellCursorEmbedding.cursor,fresh,persistent,
      hz 28 (by decide),hz 30 (by decide),hz 7 (by decide),hz 19 (by decide),hz 29 (by decide),
      hz 8 (by decide),hz 9 (by decide),hz 10 (by decide),hz 20 (by decide),
      GaussWordRowTraversal.ready,GaussWordRowTraversal.Data.contents,GaussWordRowTraversal.Data.cell]
  obtain ⟨d,hd,hframe⟩ := GaussCellFieldFrame.physical_frame F (rowBits B r pivot c i.val)
    hf29 hf28 hffresh
  obtain ⟨d',hd',hframe'⟩ := GaussCellCursorEmbedding.outputs_update frameSlots
    GaussCellFieldFrame.program GaussCellFieldFrame.start GaussCellFieldFrame.control
    GaussCellFieldFrame.control D2.contents (loc 29)
    (V2FieldContext.field (rowBits B r pivot c i.val)) d hframe
  have hfinal : Function.update D2.contents (frameSlots (loc 29))
      (V2FieldContext.field (rowBits B r pivot c i.val)) =
      Function.update S (.inr .output) (V2FieldContext.field (rowBits B r pivot c i.val)) := by
    funext z
    cases z with
    | inl z => rfl
    | inr z => cases z <;> simp [S,D,D2,initialData,frameSlots,frameMap,loc,old,
        GaussFetchedArithmetic.lower,GaussWordRowTraversal.ready,
        GaussWordRowTraversal.Data.contents,GaussWordRowTraversal.Data.foreign]
  rw [hfinal] at hframe'
  obtain ⟨u,hu,h01⟩ := BitMachineRawSequence.runs headerProgram rowProgram
    GaussCountHeader.start rowStart GaussCountHeader.control GaussCountHeader.control
    rowControl vb S D1.contents D2.contents a' b hheader' hrow'
  obtain ⟨t,ht,hfull⟩ := BitMachineRawSequence.runs p01 frameProgram
    (BitMachineRawSequence.leftLabel GaussCountHeader.start) GaussCellFieldFrame.start
    (GaussCountHeader.control,rowControl) (GaussCountHeader.control,vb)
    GaussCellFieldFrame.control GaussCellFieldFrame.control S D2.contents
    (Function.update S (.inr .output) (V2FieldContext.field (rowBits B r pivot c i.val)))
    u d' h01 hframe'
  have hrowlen := rowBits_length_le B r pivot c i.val
  have hframeclock := frame_clock_le (rowBits B r pivot c i.val)
    (rowCap B r pivot c) hrowlen
  refine ⟨t,?_,hfull⟩
  unfold clock
  change b ≤ GaussWordRowTraversal.writerBound k (cellClock B) (valueCap B r pivot c)+
    (EncodedCommunication.natField k).length at hb
  omega


#print axioms bounded_entry
#print axioms rowBits_length_le
#print axioms physical_row_clock
end
end CurrentAdditive.GaussConcreteRowClock
