import CurrentAdditive.GaussConcreteCellEntry
import CurrentAdditive.GaussCountHeader

/-! One concrete Gauss row: produce the real count header from the physical
column counter, execute the actual cell program for each column, and frame
the complete row. No local evaluator or preinstalled header is assumed. -/

namespace CurrentAdditive.GaussConcreteRow

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open GaussCellFieldFrame
open GaussConcreteCellEntry

abbrev Stack := GaussWordRowTraversal.Stack N
abbrev RowLabel := GaussWordRowTraversal.Label GaussFramedCell.Label
abbrev RowControl := GaussWordRowTraversal.Control GaussFramedCell.Control

def headerMap (z : Bank) : Stack :=
  if z.val=28 then .inr .cols else if z.val=30 then .inr .buffer else .inl (cursor z)

theorem headerMap_injective : Function.Injective headerMap := by
  intro a b h
  by_cases ha28 : a.val=28 <;> by_cases hb28 : b.val=28 <;>
    by_cases ha30 : a.val=30 <;> by_cases hb30 : b.val=30
  all_goals simp only [headerMap,ha28,hb28,ha30,hb30,↓reduceIte] at h
  all_goals first
    | exact Fin.ext (by omega)
    | exact cursor.injective (Sum.inl.inj h)
    | cases h

def headerSlots : Bank ↪ Stack := ⟨headerMap,headerMap_injective⟩
def headerProgram := GaussCellCursorEmbedding.relocate headerSlots GaussCountHeader.program

def frameMap (z : Bank) : Stack :=
  if z.val=29 then .inr .output else .inl (cursor z)

theorem frameMap_injective : Function.Injective frameMap := by
  intro a b h
  by_cases ha : a.val=29 <;> by_cases hb : b.val=29
  all_goals simp only [frameMap,ha,hb,↓reduceIte] at h
  all_goals first
    | exact Fin.ext (by omega)
    | exact cursor.injective (Sum.inl.inj h)
    | cases h

def frameSlots : Bank ↪ Stack := ⟨frameMap,frameMap_injective⟩
def frameProgram := GaussCellCursorEmbedding.relocate frameSlots GaussCellFieldFrame.program

def rowProgram := GaussWordRowTraversal.program GaussConcreteCellEntry.program
  GaussFramedCell.start GaussFramedCell.control
def rowStart : RowLabel := .inr (.copy .cols)
def rowControl : RowControl := (GaussFramedCell.control,none)

def p01 := BitMachineRawSequence.program headerProgram rowProgram rowStart
  GaussCountHeader.control rowControl
def program := BitMachineRawSequence.program p01 frameProgram GaussCellFieldFrame.start
  (GaussCountHeader.control,rowControl) GaussCellFieldFrame.control
abbrev Label := BitMachineRawSequence.Label
  (BitMachineRawSequence.Label GaussCountHeader.Label RowLabel) GaussCellFieldFrame.Label
abbrev Control := BitMachineRawSequence.Control
  (BitMachineRawSequence.Control GaussCountHeader.Control RowControl) GaussCellFieldFrame.Control
def start : Label := BitMachineRawSequence.leftLabel
  (BitMachineRawSequence.leftLabel GaussCountHeader.start)
def control : Control := ((GaussCountHeader.control,rowControl),GaussCellFieldFrame.control)

def rowBits {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) (x : Nat) : List Bool :=
  EncodedCommunication.natField k ++
    GaussWordRowTraversal.rowWord (value B r pivot c) x 0 k

def initialData {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot i : Fin m) (c : Fin k) : GaussWordRowTraversal.Data N :=
  GaussWordRowTraversal.ready (persistent B r pivot c) m k i.val 0 0 0 [] []

theorem value_length_bound {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) :
    ∃ L : Nat, ∀ x y,(value B r pivot c x y).length ≤ L := by
  let L := ∑ i : Fin m,∑ j : Fin k,(value B r pivot c i.val j.val).length
  refine ⟨L,?_⟩
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

theorem physical_row {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot i : Fin m) (c : Fin k) (hn : B pivot c≠0) :
    ∃ t : Nat, ((advance program)^[t])
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
  obtain ⟨T,hcells⟩ := GaussConcreteCellEntry.entry_runs B r pivot c hn
  obtain ⟨L,hlen⟩ := value_length_bound B r pivot c
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
  exact ⟨t,hfull⟩

#print axioms physical_row
end
end CurrentAdditive.GaussConcreteRow
