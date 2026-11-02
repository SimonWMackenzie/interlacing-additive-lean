import EthInapproximability.CurrentPaper.CNFValidatorMachine

/-! # Exact transition equations of the CNF validator (unit 4, B4-S1)

Field, budget, storage, clause and sign runs of the literal finite controller
`CNFValidator.program`. The field and budget lemmas are the admitted
`EncodedGraphMachineFields` equations restated for this controller.
-/

namespace EthInapproximability.CurrentPaper.CNFValidator.Steps

open Turing TM2.Stmt BitMachineEncoding EthInapproximability.CurrentPaper.CNFValidator

theorem afterHeader_good (v : Control) (d : Data) (bs : List Bool) :
    advance program (cfg (some (outer .afterHeader)) v {d with value := true :: bs}) =
      if field v = .count then
        cfg (some (.inr (.inl .zeroScan))) (v.1, (none, false), (setPop v (some true)).2.2)
          {d with value := bs}
      else cfg (some (outer .copyVertices)) (setPop v (some true)) {d with value := bs} := by
  by_cases hf : v.2.2.1 = .count <;>
    simp [advance, TM2.step, program, outerProgram, outer, TM2.stepAux,
      cfg, Data.stacks, popped, setPop, field, go, readBounded, hf] <;>
    (funext k; fin_cases k <;> rfl)

theorem afterHeader_bad (v : Control) (d : Data) (bs : List Bool) :
    advance program (cfg (some (outer .afterHeader)) v {d with value := false :: bs}) =
      cfg (some (outer .reject)) (setPop v (some false)) {d with value := bs} := by
  simp [advance, TM2.step, program, outerProgram, outer, TM2.stepAux,
    cfg, Data.stacks, popped, setPop, go, fail]
  funext k
  fin_cases k <;> rfl

theorem afterBound_good (v : Control) (d : Data) (bs : List Bool) :
    advance program (cfg (some (outer .afterBound)) v {d with unary := true :: bs}) =
      cfg (some (outer .clearValue)) (setPop v (some true)) {d with unary := bs} := by
  simp [advance, TM2.step, program, outerProgram, outer, TM2.stepAux,
    cfg, Data.stacks, popped, setPop, go]
  funext k
  fin_cases k <;> rfl

theorem afterBound_bad (v : Control) (d : Data) (bs : List Bool) :
    advance program (cfg (some (outer .afterBound)) v {d with unary := false :: bs}) =
      cfg (some (outer .reject)) (setPop v (some false)) {d with unary := bs} := by
  simp [advance, TM2.step, program, outerProgram, outer, TM2.stepAux,
    cfg, Data.stacks, popped, setPop, go, fail]
  funext k
  fin_cases k <;> rfl

theorem copyVertices_cons (b : Bool) (xs : List Bool) (v : Control) (d : Data) :
    advance program (cfg (some (outer .copyVertices)) v {d with vertices := b :: xs}) =
      cfg (some (outer .copyVertices)) (setPop v (some b))
        {d with vertices := xs, scratch := true :: d.scratch, cap := true :: d.cap} := by
  simp [advance, TM2.step, program, outerProgram, outer, TM2.stepAux,
    cfg, Data.stacks, popped, setPop, go]
  funext k
  fin_cases k <;> rfl

theorem copyVertices_nil (v : Control) (d : Data) :
    advance program (cfg (some (outer .copyVertices)) v {d with vertices := []}) =
      cfg (some (outer .restoreVertices)) (setPop v none) {d with vertices := []} := by
  simp [advance, TM2.step, program, outerProgram, outer, TM2.stepAux,
    cfg, Data.stacks, popped, setPop, go]

theorem copyVertices_run (xs : List Bool) (v : Control) (d : Data) :
    run (xs.length + 1) (cfg (some (outer .copyVertices)) v {d with vertices := xs}) =
      cfg (some (outer .restoreVertices)) (setPop v none)
        {d with vertices := [], scratch := List.replicate xs.length true ++ d.scratch,
                cap := List.replicate xs.length true ++ d.cap} := by
  induction xs generalizing v d with
  | nil => simpa using run_succ (copyVertices_nil v d) 0
  | cons b xs ih =>
      rw [List.length_cons, run_succ (copyVertices_cons b xs v d)]
      rw [ih (setPop v (some b)) {d with scratch := true :: d.scratch, cap := true :: d.cap}]
      have hu (ys : List Bool) : List.replicate xs.length true ++ true :: ys =
          List.replicate (xs.length + 1) true ++ ys := by
        rw [List.replicate_add, List.append_assoc]
        rfl
      simp [setPop, hu, List.replicate_succ]

theorem restoreVertices_cons (b : Bool) (xs : List Bool) (v : Control) (d : Data) :
    advance program (cfg (some (outer .restoreVertices)) v {d with scratch := b :: xs}) =
      cfg (some (outer .restoreVertices)) (setPop v (some b))
        {d with scratch := xs, vertices := b :: d.vertices} := by
  simp [advance, TM2.step, program, outerProgram, outer, TM2.stepAux,
    cfg, Data.stacks, move, popped, setPop, go]
  funext k
  fin_cases k <;> rfl

theorem restoreVertices_nil (v : Control) (d : Data) :
    advance program (cfg (some (outer .restoreVertices)) v {d with scratch := []}) =
      cfg (some (outer .endpointCap)) (setPop v none) {d with scratch := []} := by
  simp [advance, TM2.step, program, outerProgram, outer, TM2.stepAux,
    cfg, Data.stacks, move, popped, setPop, go]

theorem restoreVertices_run (xs : List Bool) (v : Control) (d : Data) :
    run (xs.length + 1) (cfg (some (outer .restoreVertices)) v {d with scratch := xs}) =
      cfg (some (outer .endpointCap)) (setPop v none)
        {d with scratch := [], vertices := xs.reverse ++ d.vertices} := by
  induction xs generalizing v d with
  | nil => simpa using run_succ (restoreVertices_nil v d) 0
  | cons b xs ih =>
      rw [List.length_cons, run_succ (restoreVertices_cons b xs v d)]
      rw [ih (setPop v (some b)) {d with vertices := b :: d.vertices}]
      simp [List.reverse_cons, List.append_assoc, setPop]

theorem copy_budget_run (n : Nat) (v : Control) (d : Data) :
    run (2 * n + 2) (cfg (some (outer .copyVertices)) v
      {d with vertices := List.replicate n true, scratch := [], cap := []}) =
        cfg (some (outer .endpointCap)) (setPop v none)
          {d with vertices := List.replicate n true, scratch := [], cap := List.replicate n true} := by
  have hc := copyVertices_run (List.replicate n true) v {d with scratch := [], cap := []}
  simp only [List.length_replicate, List.append_nil] at hc
  rw [show 2 * n + 2 = (n + 1) + (n + 1) by omega, run_add hc]
  simpa [setPop] using restoreVertices_run (List.replicate n true) (setPop v none)
    {d with vertices := [], scratch := [], cap := List.replicate n true}

theorem endpointCap_nil (v : Control) (d : Data) :
    advance program (cfg (some (outer .endpointCap)) v {d with cap := []}) =
      cfg (some (outer .reject)) (setPop v none) {d with cap := []} := by
  simp [advance, TM2.step, program, outerProgram, outer, TM2.stepAux,
    cfg, Data.stacks, popped, setPop, go, fail]

theorem endpointCap_cons (b : Bool) (xs : List Bool) (v : Control) (d : Data) :
    advance program (cfg (some (outer .endpointCap)) v {d with cap := b :: xs}) =
      cfg (some (.inr (.inl .zeroScan))) (v.1, (none, false), (setPop v (some b)).2.2)
        {d with cap := xs} := by
  simp [advance, TM2.step, program, outerProgram, outer, TM2.stepAux,
    cfg, Data.stacks, popped, setPop, readBounded]
  funext k
  fin_cases k <;> rfl


/-- The actual continuation after storing one of the four unary fields. -/
def storeNext : Field → Label
  | .count => outer .clauses
  | .lit0 => outer .sign
  | .lit1 => outer .sign
  | .lit2 => outer .clauses

def storeControl : Field → Control → Control
  | .count, v => setPop v none
  | .lit0, v => setField (setPop v none) .lit1
  | .lit1, v => setField (setPop v none) .lit2
  | .lit2, v => setPop v none

/-- A literal's unary index is discarded after its bound check; the clause
count is stored on the clause counter. -/
def storeData (f : Field) (n : ℕ) (d : Data) : Data :=
  match f with
  | .count => {d with unary := [], clauses := List.replicate n true ++ d.clauses}
  | .lit0 => {d with unary := []}
  | .lit1 => {d with unary := []}
  | .lit2 => {d with unary := []}

def storeOne (f : Field) (d : Data) : Data :=
  match f with
  | .count => {d with clauses := true :: d.clauses}
  | .lit0 => d
  | .lit1 => d
  | .lit2 => d

theorem store_cons (f : Field) (b : Bool) (xs : List Bool) (v : Control)
    (hf : field v = f) (d : Data) :
    advance program (cfg (some (outer .store)) v {d with unary := b :: xs}) =
      cfg (some (outer .store)) (setPop v (some b))
        {storeOne f d with unary := xs} := by
  change v.2.2.1 = f at hf
  cases f <;>
    simp [advance, TM2.step, program, outerProgram, outer, TM2.stepAux,
      cfg, Data.stacks, popped, setPop, go, field, hf, storeOne]
  all_goals funext k; fin_cases k <;> rfl

theorem store_nil (f : Field) (v : Control) (hf : field v = f) (d : Data) :
    advance program (cfg (some (outer .store)) v {d with unary := []}) =
      cfg (some (storeNext f)) (storeControl f v) {d with unary := []} := by
  change v.2.2.1 = f at hf
  cases f <;>
    simp [advance, TM2.step, program, outerProgram, outer, TM2.stepAux,
      cfg, Data.stacks, popped, setPop, go, field, hf, storeNext, storeControl,
      setField]

theorem store_run (f : Field) (xs : List Bool) (v : Control)
    (hf : field v = f) (d : Data) :
    run (xs.length + 1) (cfg (some (outer .store)) v {d with unary := xs}) =
      cfg (some (storeNext f)) (storeControl f v) (storeData f xs.length d) := by
  induction xs generalizing v d with
  | nil => cases f <;> simpa [storeData] using run_succ (store_nil _ v hf d) 0
  | cons b xs ih =>
      rw [List.length_cons, run_succ (store_cons f b xs v hf d)]
      rw [ih (setPop v (some b)) (by simpa [field, setPop] using hf) (storeOne f d)]
      have hu (ys : List Bool) : List.replicate xs.length true ++ true :: ys =
          List.replicate (xs.length + 1) true ++ ys := by
        rw [List.replicate_add, List.append_assoc]
        rfl
      cases f <;> simp [storeControl, storeData, storeOne, setPop, setField, hu]

/-- One remaining clause is charged before its first literal. -/
theorem clauses_cons (b : Bool) (xs : List Bool) (v : Control) (d : Data) :
    advance program (cfg (some (outer .clauses)) v {d with clauses := b :: xs}) =
      cfg (some (outer .sign)) (setField (setPop v (some b)) .lit0)
        {d with clauses := xs} := by
  simp [advance, TM2.step, program, outerProgram, outer, TM2.stepAux,
    cfg, Data.stacks, popped, setPop, setField, go]
  funext k
  fin_cases k <;> rfl

theorem clauses_nil (v : Control) (d : Data) :
    advance program (cfg (some (outer .clauses)) v {d with clauses := []}) =
      cfg (some (outer .finalCheck)) (setPop v none) {d with clauses := []} := by
  simp [advance, TM2.step, program, outerProgram, outer, TM2.stepAux,
    cfg, Data.stacks, popped, setPop, go]

/-- A literal's sign bit is consumed (either value is legal) before its
index field is read; a missing sign bit rejects. -/
theorem sign_cons (b : Bool) (xs : List Bool) (v : Control) (d : Data) :
    advance program (cfg (some (outer .sign)) v {d with input := b :: xs}) =
      cfg (some (.inl .scan)) ((none, none), (setPop v (some b)).2)
        {d with input := xs} := by
  simp [advance, TM2.step, program, outerProgram, outer, TM2.stepAux,
    cfg, Data.stacks, popped, setPop, readHeader]
  funext k
  fin_cases k <;> rfl

theorem sign_nil (v : Control) (d : Data) :
    advance program (cfg (some (outer .sign)) v {d with input := []}) =
      cfg (some (outer .reject)) (setPop v none) {d with input := []} := by
  simp [advance, TM2.step, program, outerProgram, outer, TM2.stepAux,
    cfg, Data.stacks, popped, setPop, go, fail]

/-- Exhausting the declared clauses accepts only when no input remains. -/
theorem finalCheck_nil (v : Control) (d : Data) :
    advance program (cfg (some (outer .finalCheck)) v {d with input := []}) =
      cfg (some (outer .accept)) (setPop v none) {d with input := []} := by
  simp [advance, TM2.step, program, outerProgram, outer, TM2.stepAux,
    cfg, Data.stacks, popped, setPop, go]

theorem finalCheck_cons (b : Bool) (xs : List Bool) (v : Control) (d : Data) :
    advance program (cfg (some (outer .finalCheck)) v {d with input := b :: xs}) =
      cfg (some (outer .reject)) (setPop v (some b)) {d with input := xs} := by
  simp [advance, TM2.step, program, outerProgram, outer, TM2.stepAux,
    cfg, Data.stacks, popped, setPop, go, fail]
  funext k
  fin_cases k <;> rfl

end EthInapproximability.CurrentPaper.CNFValidator.Steps
