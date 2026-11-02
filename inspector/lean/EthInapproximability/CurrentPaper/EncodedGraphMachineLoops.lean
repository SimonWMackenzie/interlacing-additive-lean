import EthInapproximability.CurrentPaper.EncodedGraphMachine

/-!
# Exact storage and endpoint-comparison runs of the graph validator

Source: frozen v8 `03-exact-hardness.tex`, explicit graph encoding, and
`06-eth.tex`, finite-stack bit-machine convention. These are run equations
for the literal fifteen-stack controller, not an assumed parser contract.
The auxiliary definitions name finite control and stack updates only.
-/

namespace EthInapproximability.CurrentPaper.EncodedGraphMachineLoops

open Turing TM2.Stmt BitMachineEncoding
open EncodedGraphMachine

/-- The actual continuation after storing one of the three unary fields. -/
def storeNext : Field → Label
  | .count => outer .edges
  | .left => .inl .scan
  | .right => outer .compare

def storeControl : Field → Control → Control
  | .count, v => setPop v none
  | .left, v => ((none, none), v.2.1, .right, none, v.2.2.2.2)
  | .right, v => setPop v none

def storeData (f : Field) (n : ℕ) (d : Data) : Data :=
  match f with
  | .count => {d with unary := [], edges := List.replicate n true ++ d.edges}
  | .left => {d with unary := [], left := List.replicate n true ++ d.left}
  | .right => {d with unary := [], right := List.replicate n true ++ d.right}

def storeOne (f : Field) (d : Data) : Data :=
  match f with
  | .count => {d with edges := true :: d.edges}
  | .left => {d with left := true :: d.left}
  | .right => {d with right := true :: d.right}

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
      setField, readHeader]

/-- Every field consumes exactly one transition per unary cell plus the
empty-stack test, and then follows the appropriate literal continuation. -/
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
      cases f <;> simp [storeControl, storeData, storeOne, setPop, hu]

theorem clearLeft_run (xs : List Bool) (v : Control) (d : Data) :
    run (xs.length + 1) (cfg (some (outer .clearLeft)) v {d with left := xs}) =
      cfg (some (outer .edges)) (setPop v none) {d with left := []} := by
  have hi : cfg (some (outer .clearLeft)) v {d with left := xs} =
      ⟨some (outer .clearLeft), v, Function.update d.stacks 9 xs⟩ := by
    unfold cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  rw [hi, clear_run 9 .clearLeft .edges rfl xs v d.stacks]
  unfold cfg
  congr 1
  funext k
  fin_cases k <;> rfl

theorem clearRight_run (xs : List Bool) (v : Control) (d : Data) :
    run (xs.length + 1) (cfg (some (outer .clearRight)) v {d with right := xs}) =
      cfg (some (outer .edges)) (setPop v none) {d with right := []} := by
  have hi : cfg (some (outer .clearRight)) v {d with right := xs} =
      ⟨some (outer .clearRight), v, Function.update d.stacks 10 xs⟩ := by
    unfold cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  rw [hi, clear_run 10 .clearRight .edges rfl xs v d.stacks]
  unfold cfg
  congr 1
  funext k
  fin_cases k <;> rfl

theorem compare_cons (a b : Bool) (xs ys : List Bool) (v : Control) (d : Data) :
    advance program (cfg (some (outer .compare)) v {d with left := a :: xs, right := b :: ys}) =
      cfg (some (outer .compare)) (setPop₂ (setPop v (some a)) (some b))
        {d with left := xs, right := ys} := by
  simp [advance, TM2.step, program, outerProgram, outer, TM2.stepAux,
    cfg, Data.stacks, popped, popped₂, setPop, setPop₂, go]
  funext k
  fin_cases k <;> rfl

theorem compare_nil (v : Control) (d : Data) :
    advance program (cfg (some (outer .compare)) v {d with left := [], right := []}) =
      cfg (some (outer .reject)) (setPop₂ (setPop v none) none)
        {d with left := [], right := []} := by
  simp [advance, TM2.step, program, outerProgram, outer, TM2.stepAux,
    cfg, Data.stacks, popped, popped₂, setPop, setPop₂, go, fail]
  funext k
  fin_cases k <;> rfl

theorem compare_left (b : Bool) (xs : List Bool) (v : Control) (d : Data) :
    advance program (cfg (some (outer .compare)) v {d with left := b :: xs, right := []}) =
      cfg (some (outer .clearLeft)) (setPop₂ (setPop v (some b)) none)
        {d with left := xs, right := []} := by
  simp [advance, TM2.step, program, outerProgram, outer, TM2.stepAux,
    cfg, Data.stacks, popped, popped₂, setPop, setPop₂, go]
  funext k
  fin_cases k <;> rfl

theorem compare_right (b : Bool) (xs : List Bool) (v : Control) (d : Data) :
    advance program (cfg (some (outer .compare)) v {d with left := [], right := b :: xs}) =
      cfg (some (outer .clearRight)) (setPop₂ (setPop v none) (some b))
        {d with left := [], right := xs} := by
  simp [advance, TM2.step, program, outerProgram, outer, TM2.stepAux,
    cfg, Data.stacks, popped, popped₂, setPop, setPop₂, go]
  funext k
  fin_cases k <;> rfl

/-- Equal endpoints are rejected, including the two empty unary values. -/
theorem compare_eq (n : ℕ) (v : Control) (d : Data) :
    run (n + 1) (cfg (some (outer .compare)) v
      {d with left := List.replicate n true, right := List.replicate n true}) =
      cfg (some (outer .reject)) (setPop₂ (setPop v none) none)
        {d with left := [], right := []} := by
  induction n generalizing v d with
  | zero => simpa using run_succ (compare_nil v d) 0
  | succ n ih =>
      rw [List.replicate_succ, run_succ (compare_cons true true _ _ v d)]
      simpa [setPop, setPop₂] using ih (setPop₂ (setPop v (some true)) (some true)) d

/-- A smaller left endpoint clears the residual right counter and returns
to the edge loop in exactly the larger endpoint plus one transitions. -/
theorem compare_lt (n m : ℕ) (hnm : n < m) (v : Control) (d : Data) :
    run (m + 1) (cfg (some (outer .compare)) v
      {d with left := List.replicate n true, right := List.replicate m true}) =
      cfg (some (outer .edges)) (setPop₂ (setPop v none) (some true))
        {d with left := [], right := []} := by
  induction n generalizing m v d with
  | zero =>
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
      rw [List.replicate_succ, List.replicate_zero,
        run_succ (compare_right true _ v d)]
      simpa [setPop, setPop₂] using clearRight_run (List.replicate m true)
        (setPop₂ (setPop v none) (some true)) {d with left := []}
  | succ n ih =>
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
      rw [List.replicate_succ, List.replicate_succ,
        run_succ (compare_cons true true _ _ v d)]
      simpa [setPop, setPop₂] using ih m (by omega)
        (setPop₂ (setPop v (some true)) (some true)) d

/-- A larger left endpoint clears the residual left counter before
returning to the edge loop, preserving all other stack contents. -/
theorem compare_gt (n m : ℕ) (hnm : m < n) (v : Control) (d : Data) :
    run (n + 1) (cfg (some (outer .compare)) v
      {d with left := List.replicate n true, right := List.replicate m true}) =
      cfg (some (outer .edges)) (setPop₂ (setPop v none) none)
        {d with left := [], right := []} := by
  induction m generalizing n v d with
  | zero =>
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      rw [List.replicate_succ, List.replicate_zero,
        run_succ (compare_left true _ v d)]
      simpa [setPop, setPop₂] using clearLeft_run (List.replicate n true)
        (setPop₂ (setPop v (some true)) none) {d with right := []}
  | succ m ih =>
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      rw [List.replicate_succ, List.replicate_succ,
        run_succ (compare_cons true true _ _ v d)]
      simpa [setPop, setPop₂] using ih n (by omega)
        (setPop₂ (setPop v (some true)) (some true)) d

/-- One remaining edge is charged before reading its left endpoint. -/
theorem edges_cons (b : Bool) (xs : List Bool) (v : Control) (d : Data) :
    advance program (cfg (some (outer .edges)) v {d with edges := b :: xs}) =
      cfg (some (.inl .scan)) ((none, none), v.2.1, .left, some b, v.2.2.2.2)
        {d with edges := xs} := by
  simp [advance, TM2.step, program, outerProgram, outer, TM2.stepAux,
    cfg, Data.stacks, popped, setPop, setField, readHeader]
  funext k
  fin_cases k <;> rfl

theorem edges_nil (v : Control) (d : Data) :
    advance program (cfg (some (outer .edges)) v {d with edges := []}) =
      cfg (some (outer .finalCheck)) (setPop v none) {d with edges := []} := by
  simp [advance, TM2.step, program, outerProgram, outer, TM2.stepAux,
    cfg, Data.stacks, popped, setPop, go]

/-- Exhausting the declared edges accepts only when no input remains. -/
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

end EthInapproximability.CurrentPaper.EncodedGraphMachineLoops
