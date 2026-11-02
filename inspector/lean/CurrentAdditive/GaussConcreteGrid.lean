import CurrentAdditive.GaussConcreteRowEncoding

/-! Actual outer traversal of the concrete framed row routine. The input
configuration contains the physical matrix, immutable pivot data and unary
dimensions. Parsing a serialized four-field input and producing those
dimension banks are separate physical preparator segments. -/

namespace CurrentAdditive.GaussConcreteGrid

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open GaussCellFieldFrame GaussConcreteCellEntry

abbrev K := N+8
abbrev Cell := GaussWordGridTraversal.CellStack K
abbrev Stack := GaussWordGridTraversal.Stack K

def rowMap : GaussConcreteRow.Stack → Cell
  | .inl (.inl z) => .inl ⟨z.val,by dsimp only [K]; omega⟩
  | .inl (.inr z) => if z=0 then .inr 0 else if z=1 then .inl ⟨N,by dsimp only [K]; omega⟩
      else .inl ⟨N+1,by dsimp only [K]; omega⟩
  | .inr .rows => .inl ⟨N+2,by dsimp only [K]; omega⟩
  | .inr .cols => .inl ⟨N+3,by dsimp only [K]; omega⟩
  | .inr .rowsLeft => .inl ⟨N+4,by dsimp only [K]; omega⟩
  | .inr .colsLeft => .inl ⟨N+5,by dsimp only [K]; omega⟩
  | .inr .temp => .inl ⟨N+6,by dsimp only [K]; omega⟩
  | .inr .buffer => .inl ⟨N+7,by dsimp only [K]; omega⟩
  | .inr .output => .inr 2

theorem rowMap_injective : Function.Injective rowMap := by
  intro a b h
  let code : Cell → Nat := fun z => match z with | .inl q => q.val | .inr q => K+q.val
  have hv := congrArg code h
  cases a with
  | inl a =>
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        cases b with
        | inl b =>
          simp only [rowMap] at h
          have hv' : a.val=b.val := congrArg (fun z : Fin K => z.val) (Sum.inl.inj h)
          exact congrArg (fun z => Sum.inl (Sum.inl z))
            (Fin.ext hv')
        | inr b => fin_cases b <;> simp [code,rowMap,K] at hv <;> have ha:=a.isLt <;> omega
      | inr b => cases b <;> simp [code,rowMap,K] at hv <;> have ha:=a.isLt <;> omega
    | inr a =>
      cases b with
      | inl b =>
        cases b with
        | inl b => fin_cases a <;> simp [code,rowMap,K] at hv <;> have hb:=b.isLt <;> omega
        | inr b => fin_cases a <;> fin_cases b <;> simp_all [rowMap,Fin.ext_iff]
      | inr b => fin_cases a <;> cases b <;> simp_all [rowMap,Fin.ext_iff]
  | inr a =>
    cases b with
    | inl b =>
      cases b with
      | inl b => cases a <;> simp [code,rowMap,K] at hv <;> have hb:=b.isLt <;> omega
      | inr b => cases a <;> fin_cases b <;> simp_all [rowMap,Fin.ext_iff]
    | inr b => cases a <;> cases b <;> simp_all [rowMap,Fin.ext_iff]

def rowSlots : GaussConcreteRow.Stack ↪ Cell := ⟨rowMap,rowMap_injective⟩
def rowProgram := GaussCellCursorEmbedding.relocate rowSlots GaussConcreteRow.program

def persistent {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) (z : Fin K) : List Bool :=
  if hz : z.val<N then GaussConcreteCellEntry.persistent B r pivot c ⟨z.val,hz⟩
  else if z.val=N+2 then List.replicate m true
  else if z.val=N+3 then List.replicate k true else []

def value {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) (x y : Nat) : List Bool :=
  if x < m ∧ y < 1 then V2FieldContext.field (GaussConcreteRow.rowBits B r pivot c x) else []

theorem actual_row {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot i : Fin m) (c : Fin k) (hn : B pivot c≠0) :
    ∃ t : Nat, ((advance rowProgram)^[t])
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
  obtain ⟨t,hrun⟩ := GaussConcreteRow.physical_row B r pivot i c hn
  rw [←hrestriction] at hrun
  obtain ⟨u,hu,he⟩ := GaussCellCursorEmbedding.outputs_update rowSlots
    GaussConcreteRow.program GaussConcreteRow.start GaussConcreteRow.control
    GaussConcreteRow.control S (.inr .output)
    (V2FieldContext.field (GaussConcreteRow.rowBits B r pivot c i.val)) t hrun
  refine ⟨u,he.trans ?_⟩
  apply congrArg (fun bank => (⟨none,GaussConcreteRow.control,bank⟩ :
    TM2.Cfg (fun _ : Cell => Bool) GaussConcreteRow.Label GaussConcreteRow.Control))
  funext z
  cases z with
  | inl z => simp [S,rowSlots,rowMap,GaussWordGridTraversal.cellCfg]
  | inr z => fin_cases z <;>
      simp [S,rowSlots,rowMap,GaussWordGridTraversal.cellCfg,value,i.isLt]

theorem entry_runs {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) (hn : B pivot c≠0) :
    ∃ T : Nat, GaussWordGridTraversal.EntryRuns rowProgram GaussConcreteRow.start
      GaussConcreteRow.control (persistent B r pivot c) m 1 T (value B r pivot c) := by
  choose times runs using (fun i : Fin m => actual_row B r pivot i c hn)
  let T := ∑ i : Fin m,times i
  refine ⟨T,?_⟩
  intro x hx y hy
  have hy0 : y=0 := by dsimp only [K]; omega
  subst y
  let i : Fin m := ⟨x,hx⟩
  exact ⟨times i,Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i),
    GaussConcreteRow.control,runs i⟩

def headerMap (z : Bank) : Stack :=
  if z.val=28 then .inr .rows else if z.val=30 then .inr .buffer
  else .inl (.inl ⟨z.val,by have hz:=z.isLt; dsimp only [K,N] at *; omega⟩)

theorem headerMap_injective : Function.Injective headerMap := by
  intro a b h
  apply Fin.ext
  by_cases ha28 : a.val=28 <;> by_cases hb28 : b.val=28 <;>
    by_cases ha30 : a.val=30 <;> by_cases hb30 : b.val=30
  all_goals simp only [headerMap,ha28,hb28,ha30,hb30,↓reduceIte] at h
  all_goals first
    | omega
    | exact congrArg (fun z : Fin K => z.val) (Sum.inl.inj (Sum.inl.inj h))
    | cases h

def headerSlots : Bank ↪ Stack := ⟨headerMap,headerMap_injective⟩
def headerProgram := GaussCellCursorEmbedding.relocate headerSlots GaussCountHeader.program
def matrixProgram := GaussWordGridTraversal.program rowProgram GaussConcreteRow.start GaussConcreteRow.control
def matrixStart : GaussWordGridTraversal.Label GaussConcreteRow.Label := .inr (.copy .rows)
def matrixControl : GaussWordGridTraversal.Control GaussConcreteRow.Control := (GaussConcreteRow.control,none)
def program := BitMachineRawSequence.program headerProgram matrixProgram matrixStart
  GaussCountHeader.control matrixControl
abbrev Label := BitMachineRawSequence.Label GaussCountHeader.Label
  (GaussWordGridTraversal.Label GaussConcreteRow.Label)
abbrev Control := BitMachineRawSequence.Control GaussCountHeader.Control
  (GaussWordGridTraversal.Control GaussConcreteRow.Control)
def start : Label := BitMachineRawSequence.leftLabel GaussCountHeader.start
def control : Control := (GaussCountHeader.control,matrixControl)

def initialData {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) : GaussWordGridTraversal.Data K :=
  GaussWordGridTraversal.ready (persistent B r pivot c) m 1 0 0 0 0 [] []

end
end CurrentAdditive.GaussConcreteGrid
