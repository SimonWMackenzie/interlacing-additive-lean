import CurrentAdditive.GaussCellInitialClock
import CurrentAdditive.GaussCellCursorEmbedding
import CurrentAdditive.GaussWordRowTraversal

/-! Instantiation of the row traversal's local contract with the actual
swap/get/arithmetic/reset/framing program. The existence of a uniform finite
time follows from the finitely many actual executions. This file does not
assert a polynomial clock from that finite maximum. -/

namespace CurrentAdditive.GaussConcreteCellEntry

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open GaussCellFieldFrame

abbrev N := 32+(32+GaussFetchedArithmetic.M.stackCount+10)
abbrev Ambient := GaussWordGridTraversal.CellStack N

def cursor : Bank ↪ Ambient := GaussCellCursorEmbedding.slots N
def program := GaussCellCursorEmbedding.relocate cursor GaussFramedCell.program

def persistent {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) (z : Fin N) : List Bool :=
  if z.val=8 then GaussPhysical.encodeTypedMatrix B else
  if z.val=9 then List.replicate r.val true else
  if z.val=10 then List.replicate pivot.val true else
  if z.val=20 then List.replicate c.val true else []

def source {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot i : Fin m) (c j : Fin k) (z : Bank) : List Bool :=
  if z.val=7 then List.replicate i.val true else
  if z.val=19 then List.replicate j.val true else persistent B r pivot c z

def value {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) (x y : Nat) : List Bool :=
  if hx : x < m then
    if hy : y < k then
      V2FieldContext.field (GaussFramedCell.answer B r pivot ⟨x,hx⟩ c ⟨y,hy⟩)
    else []
  else []

def dataCap {m k : Nat} (B : Fin m → Fin k → ℚ) : Nat :=
  m+k+(GaussPhysical.encodeTypedMatrix B).length+
    (∑ u : Fin m,∑ v : Fin k,
      (CodeDCodec.encodeRawRat (GaussPhysical.rawOfRat (B u v))).length)+1

private theorem restriction {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot i : Fin m) (c j : Fin k) :
    (fun z => (GaussWordRowTraversal.cellCfg (L := GaussFramedCell.Label)
      (some GaussFramedCell.start) GaussFramedCell.control
      (persistent B r pivot c) i.val j.val []).stk (cursor z)) =
      source B r pivot i c j := by
  funext z
  by_cases h7 : z.val=7 <;> by_cases h19 : z.val=19 <;> by_cases h29 : z.val=29
  all_goals simp_all [cursor,GaussCellCursorEmbedding.slots,
    GaussCellCursorEmbedding.cursor,GaussWordRowTraversal.cellCfg,source,persistent]

theorem actual_cell {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot i : Fin m) (c j : Fin k) (hn : B pivot c≠0) :
    ∃ t ≤ GaussCellInitialClock.framedCap (dataCap B) (dataCap B),
      ∃ v : GaussFramedCell.Control,
      ((advance program)^[t])
        (GaussWordRowTraversal.cellCfg (some GaussFramedCell.start) GaussFramedCell.control
          (persistent B r pivot c) i.val j.val []) =
      GaussWordRowTraversal.cellCfg none v (persistent B r pivot c) i.val j.val
        (value B r pivot c i.val j.val) := by
  let S := source B r pivot i c j
  let cellMass := ∑ u : Fin m,∑ v : Fin k,
    (CodeDCodec.encodeRawRat (GaussPhysical.rawOfRat (B u v))).length
  let indexCap := dataCap B
  let sizeCap := indexCap
  have hSize (z : Fin 64) : (S (loc z)).length ≤ sizeCap := by
    dsimp [S,source,persistent,loc,old,GaussFetchedArithmetic.lower]
    split_ifs <;> (try simp only [List.length_replicate,List.length_nil])
    all_goals have hi:=i.isLt; have hr:=r.isLt; have hp:=pivot.isLt; have hj:=j.isLt; have hc:=c.isLt
    all_goals dsimp [sizeCap,indexCap,dataCap]; omega
  have hCell (u : Fin m) (v : Fin k) :
      (CodeDCodec.encodeRawRat (GaussPhysical.rawOfRat (B u v))).length ≤ indexCap := by
    have h1 := Finset.single_le_sum (f := fun v : Fin k =>
      (CodeDCodec.encodeRawRat (GaussPhysical.rawOfRat (B u v))).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
    have h2 := Finset.single_le_sum (f := fun u : Fin m => ∑ v : Fin k,
      (CodeDCodec.encodeRawRat (GaussPhysical.rawOfRat (B u v))).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ u)
    dsimp only at h1 h2
    dsimp [indexCap,dataCap,cellMass]
    omega
  have hclean (z : Fin 64) (hz : ¬GaussCellScratchReset.retained z) : S (loc z)=[] := by
    have h7 : z.val≠7 := by simp only [GaussCellScratchReset.retained] at hz; omega
    have h8 : z.val≠8 := by simp only [GaussCellScratchReset.retained] at hz; omega
    have h9 : z.val≠9 := by simp only [GaussCellScratchReset.retained] at hz; omega
    have h10 : z.val≠10 := by simp only [GaussCellScratchReset.retained] at hz; omega
    have h19 : z.val≠19 := by simp only [GaussCellScratchReset.retained] at hz; omega
    have h20 : z.val≠20 := by simp only [GaussCellScratchReset.retained] at hz; omega
    simp [S,source,persistent,loc,old,GaussFetchedArithmetic.lower,h7,h8,h9,h10,h19,h20]
  have harith (z : Fin GaussFetchedArithmetic.M.stackCount) :
      S (old (GaussFetchedArithmetic.slots.machine z))=[] := by
    dsimp [S,source,persistent,old,GaussFetchedArithmetic.slots]
    split_ifs <;> (first | rfl | omega)
  have hframe (z : Fin 10) : S (fresh z)=[] := by
    dsimp [S,source,persistent,fresh]
    split_ifs <;> (first | rfl | omega)
  obtain ⟨t,ht,hrun⟩ := GaussCellInitialClock.physical_cell B r pivot i c j hn S
    sizeCap indexCap hSize (by dsimp [indexCap,dataCap]; omega) (by dsimp [indexCap,dataCap]; omega)
    (by dsimp [indexCap,dataCap]; omega) hCell
    (by simp [S,source,loc,old,GaussFetchedArithmetic.lower])
    (by simp [S,source,persistent,loc,old,GaussFetchedArithmetic.lower])
    (by simp [S,source,persistent,loc,old,GaussFetchedArithmetic.lower])
    (by simp [S,source,persistent,loc,old,GaussFetchedArithmetic.lower])
    (by simp [S,source,loc,old,GaussFetchedArithmetic.lower])
    (by simp [S,source,persistent,loc,old,GaussFetchedArithmetic.lower])
    (by simp [S,source,persistent,loc,old,GaussFetchedArithmetic.lower])
    (by simp [S,source,persistent,loc,old,GaussFetchedArithmetic.lower]) hclean harith hframe
  let A := (GaussWordRowTraversal.cellCfg (L := GaussFramedCell.Label)
    (some GaussFramedCell.start) GaussFramedCell.control
      (persistent B r pivot c) i.val j.val []).stk
  have hrestrict : (fun z => A (cursor z))=S := restriction B r pivot i c j
  rw [←hrestrict] at hrun
  obtain ⟨u,hu,he⟩ := GaussCellCursorEmbedding.outputs_update cursor GaussFramedCell.program
    GaussFramedCell.start GaussFramedCell.control GaussFramedCell.control A (loc 29)
    (V2FieldContext.field (GaussFramedCell.answer B r pivot i c j)) t hrun
  refine ⟨u,hu.trans ht,GaussFramedCell.control,?_⟩
  have hanswer : cursor (loc 29)=(.inr 2 : Ambient) := by
    simp [cursor,GaussCellCursorEmbedding.slots,GaussCellCursorEmbedding.cursor,
      loc,old,GaussFetchedArithmetic.lower]
  rw [hanswer] at he
  refine he.trans ?_
  apply congrArg (fun bank => (⟨none,GaussFramedCell.control,bank⟩ :
    TM2.Cfg (fun _ : Ambient => Bool) GaussFramedCell.Label GaussFramedCell.Control))
  funext z
  cases z with
  | inl z => simp [A,GaussWordRowTraversal.cellCfg]
  | inr z => fin_cases z <;>
      simp [A,GaussWordRowTraversal.cellCfg,value,i.isLt,j.isLt]

/-- The actual fixed cell program supplies the traversal contract; no cell
correctness callback is a hypothesis of this theorem. -/
theorem entry_runs {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) (hn : B pivot c≠0) :
    ∃ T : Nat, GaussWordRowTraversal.EntryRuns program GaussFramedCell.start
      GaussFramedCell.control (persistent B r pivot c) m k T (value B r pivot c) := by
  refine ⟨GaussCellInitialClock.framedCap (dataCap B) (dataCap B),?_⟩
  intro x hx y hy
  let i : Fin m := ⟨x,hx⟩
  let j : Fin k := ⟨y,hy⟩
  exact actual_cell B r pivot i c j hn

#print axioms actual_cell
#print axioms entry_runs
end
end CurrentAdditive.GaussConcreteCellEntry
