import Mathlib
import Paper2.YaoCapacity

/-!
# Serialized Boolean tables and their materialization loop

Frozen v12 Appendix B, `yao:dimensions` and `yao:materialization`.
This generic helper represents the actual row-major output bits, proves
that each getter returns the input matrix entry, and counts the calls and
list cells in an explicit output loop. Those counters do not claim a
complete encoded-machine running-time bound: entry evaluation, arithmetic,
and memory-access costs remain separate obligations.
-/

namespace Paper2.YaoMaterialization

open Paper2.Yao

/-- An explicit row-major Boolean table, not an unevaluated entry function. -/
structure SerializedTable (rows cols : ℕ) where
  bits : List Bool
  length : bits.length = rows * cols

/-- Flat index of an entry, with the column changing fastest. -/
def rowMajorIndex {rows cols : ℕ} (i : Fin rows) (j : Fin cols) : Fin (rows * cols) :=
  finProdFinEquiv (i, j)

@[simp] theorem rowMajorIndex_value {rows cols : ℕ} (i : Fin rows) (j : Fin cols) :
    (rowMajorIndex i j).val = i.val * cols + j.val := by
  simp [rowMajorIndex, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

/-- Matrix entry recovered by reading one serialized output position. -/
def SerializedTable.matrix {rows cols : ℕ} (T : SerializedTable rows cols)
    (i : Fin rows) (j : Fin cols) : Bool :=
  T.bits.get (Fin.cast T.length.symm (rowMajorIndex i j))

/-- The actual row-major entry function indexed by the output position. -/
def linearEntries {rows cols : ℕ} (F : Fin rows → Fin cols → Bool)
    (k : Fin (rows * cols)) : Bool :=
  F (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

@[simp] theorem linearEntries_rowMajorIndex {rows cols : ℕ}
    (F : Fin rows → Fin cols → Bool) (i : Fin rows) (j : Fin cols) :
    linearEntries F (rowMajorIndex i j) = F i j := by
  simp [linearEntries, rowMajorIndex]

/-- Evaluate every indexed entry once in row-major order, retaining exactly
`rows * cols` Boolean output bits. Empty dimensions produce the empty list. -/
def tabulate {rows cols : ℕ} (F : Fin rows → Fin cols → Bool) :
    SerializedTable rows cols where
  bits := List.ofFn (linearEntries F)
  length := List.length_ofFn

@[simp] theorem tabulate_length {rows cols : ℕ} (F : Fin rows → Fin cols → Bool) :
    (tabulate F).bits.length = rows * cols := (tabulate F).length

@[simp] theorem tabulate_matrix {rows cols : ℕ} (F : Fin rows → Fin cols → Bool)
    (i : Fin rows) (j : Fin cols) : (tabulate F).matrix i j = F i j := by
  change (List.ofFn (linearEntries F)).get _ = F i j
  rw [List.get_ofFn]
  change linearEntries F (rowMajorIndex i j) = F i j
  exact linearEntries_rowMajorIndex F i j

/-- A loop trace with separate counts for entry evaluation and output cells.
These are generated counters, not assumptions about the resulting table. -/
structure CountedOutput where
  bits : List Bool
  entryCalls : ℕ
  consCells : ℕ

/-- Concrete recursion: the zero case does nothing; every nonzero iteration
evaluates its next input entry and prepends exactly one output bit. -/
def countedOfFn : {n : ℕ} → (Fin n → Bool) → CountedOutput
  | 0, _ => ⟨[], 0, 0⟩
  | n + 1, f =>
      let bit := f 0
      let rest := countedOfFn (fun i : Fin n => f i.succ)
      ⟨bit :: rest.bits, rest.entryCalls + 1, rest.consCells + 1⟩

theorem countedOfFn_bits {n : ℕ} (f : Fin n → Bool) :
    (countedOfFn f).bits = List.ofFn f := by
  induction n with
  | zero => simp [countedOfFn]
  | succ n ih => simp [countedOfFn, List.ofFn_succ, ih]

theorem countedOfFn_entryCalls {n : ℕ} (f : Fin n → Bool) :
    (countedOfFn f).entryCalls = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [countedOfFn, ih]

theorem countedOfFn_consCells {n : ℕ} (f : Fin n → Bool) :
    (countedOfFn f).consCells = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [countedOfFn, ih]

/-- The row-major output loop with its explicitly generated trace counters. -/
def countedTabulate {rows cols : ℕ} (F : Fin rows → Fin cols → Bool) : CountedOutput :=
  countedOfFn (linearEntries F)

theorem countedTabulate_bits {rows cols : ℕ} (F : Fin rows → Fin cols → Bool) :
    (countedTabulate F).bits = (tabulate F).bits := countedOfFn_bits _

theorem countedTabulate_entryCalls {rows cols : ℕ} (F : Fin rows → Fin cols → Bool) :
    (countedTabulate F).entryCalls = rows * cols := countedOfFn_entryCalls _

theorem countedTabulate_consCells {rows cols : ℕ} (F : Fin rows → Fin cols → Bool) :
    (countedTabulate F).consCells = rows * cols := countedOfFn_consCells _

section Reindexing

variable {X Y X' Y' : Type*} {s : Turn}

/-- Pull an actual strictly alternating protocol back along local input
maps, retaining its complete transcript tree and every charged bit. -/
def reindexProtocol (P : StrictProtocol X Y s) (f : X' → X) (g : Y' → Y) :
    StrictProtocol X' Y' s :=
  ⟨Workspace.UpperBound.Protocol.comap f g P.toProtocol,
    alternates_comap P.toProtocol f g s P.alternates⟩

@[simp] theorem reindexProtocol_cost (P : StrictProtocol X Y s)
    (f : X' → X) (g : Y' → Y) : (reindexProtocol P f g).cost = P.cost :=
  Workspace.UpperBound.Protocol.comap_cost f g P.toProtocol

@[simp] theorem reindexProtocol_eval (P : StrictProtocol X Y s)
    (f : X' → X) (g : Y' → Y) (x : X') (y : Y') :
    (reindexProtocol P f g).eval x y = P.eval (f x) (g y) :=
  Workspace.UpperBound.Protocol.comap_eval f g P.toProtocol x y

theorem Dalt_comap_le [Fintype X] [Fintype Y] [Fintype X'] [Fintype Y']
    (s : Turn) (F : X → Y → Bool) (f : X' → X) (g : Y' → Y) :
    Dalt s (fun x y => F (f x) (g y)) ≤ Dalt s F := by
  obtain ⟨P, hcost, hP⟩ := exists_optimal s F
  calc
    _ ≤ (reindexProtocol P f g).cost := Dalt_le_cost _ (by
      intro x y
      simpa using hP (f x) (g y))
    _ = Dalt s F := by rw [reindexProtocol_cost, hcost]

/-- Row and column bijections preserve exact strictly alternating complexity,
with no starter change, dummy bit, or additive loss. -/
theorem Dalt_comap_equiv [Fintype X] [Fintype Y] [Fintype X'] [Fintype Y']
    (s : Turn) (F : X → Y → Bool) (e : X' ≃ X) (d : Y' ≃ Y) :
    Dalt s (fun x y => F (e x) (d y)) = Dalt s F := by
  apply Nat.le_antisymm (Dalt_comap_le s F e d)
  simpa using Dalt_comap_le s (fun x y => F (e x) (d y)) e.symm d.symm

end Reindexing

end Paper2.YaoMaterialization
