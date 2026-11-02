import EthInapproximability.CurrentPaper.SourceClausePairUnitLift
import EthInapproximability.CurrentPaper.SourceClausePrefixGateOperands

/-! Physical unary pair ordinal on the frozen pair-unit bank. -/

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix.PairOrdinalLoader

open Turing Turing.TM2.Stmt BitMachineEncoding
open scoped Classical

abbrev Stack := PairUnitLift.Stack

def nCell : Stack := .inl (.inl 0)
def vCell : Stack := PairUnitLift.vertexCell
def ordinalCell : Stack := PairUnitLift.pairOrdinalCell
noncomputable def scratchCell : Stack := .inl PrefixGateOperands.temp

private theorem scratch_shape : scratchCell =
    .inl (.inr (.inl ⟨PrefixGateOperands.tempLocal,
      PrefixGateOperands.temp_not_core⟩)) := by
  change Sum.inl (PrefixSharedCore.gateEmbedding PrefixGateOperands.tempLocal) = _
  rw [PrefixSharedCore.gateEmbedding,
    SourceClauseSharedCore.left_outside PrefixSharedCore.gateCore
      PrefixSharedCore.unitCore _ PrefixGateOperands.temp_not_core]

private theorem cells_distinct :
    nCell ≠ vCell ∧ nCell ≠ ordinalCell ∧ nCell ≠ scratchCell ∧
    vCell ≠ ordinalCell ∧ vCell ≠ scratchCell ∧
    ordinalCell ≠ scratchCell := by
  rw [scratch_shape]
  simp [nCell, vCell, ordinalCell, PairUnitLift.vertexCell,
    PairUnitLift.pairOrdinalCell, PairUnitLift.ordinalCell]

noncomputable def frame (nword vword ordword scratchword : List Bool)
    (saved output count : List Bool) : Stack → List Bool :=
  fun x => if x = nCell then nword else if x = vCell then vword else
    if x = ordinalCell then ordword else if x = scratchCell then scratchword else
      PairUnitLift.pairBank 0 0 0 saved output count x

private theorem n_ne_v : nCell ≠ vCell := cells_distinct.1
private theorem n_ne_ord : nCell ≠ ordinalCell := cells_distinct.2.1
private theorem n_ne_scratch : nCell ≠ scratchCell := cells_distinct.2.2.1
private theorem v_ne_ord : vCell ≠ ordinalCell := cells_distinct.2.2.2.1
private theorem v_ne_scratch : vCell ≠ scratchCell := cells_distinct.2.2.2.2.1
private theorem ord_ne_scratch : ordinalCell ≠ scratchCell := cells_distinct.2.2.2.2.2

private theorem frame_n (nw vw ow sw new : List Bool) (a b c : List Bool) :
    Function.update (frame nw vw ow sw a b c) nCell new =
      frame new vw ow sw a b c := by
  funext x
  by_cases hx : x = nCell <;> simp [frame, Function.update, hx]

private theorem frame_v (nw vw ow sw new : List Bool) (a b c : List Bool) :
    Function.update (frame nw vw ow sw a b c) vCell new =
      frame nw new ow sw a b c := by
  funext x
  by_cases hx : x = vCell <;> simp [frame, Function.update, hx, n_ne_v.symm]

private theorem frame_ord (nw vw ow sw new : List Bool) (a b c : List Bool) :
    Function.update (frame nw vw ow sw a b c) ordinalCell new =
      frame nw vw new sw a b c := by
  funext x
  by_cases hx : x = ordinalCell <;>
    simp [frame, Function.update, hx, n_ne_ord.symm, v_ne_ord.symm]

private theorem frame_scratch (nw vw ow sw new : List Bool) (a b c : List Bool) :
    Function.update (frame nw vw ow sw a b c) scratchCell new =
      frame nw vw ow new a b c := by
  funext x
  by_cases hx : x = scratchCell <;>
    simp [frame, Function.update, hx, n_ne_scratch.symm, v_ne_scratch.symm,
      ord_ne_scratch.symm]

inductive Label where
  | vertexCopy | vertexRestore | nCopy | nRestore | offset | accept
  deriving DecidableEq, Fintype

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label (Option Bool)

def offsetStmt (s t : Fin 2) : TM2.Stmt (fun _ : Stack => Bool) Label (Option Bool) :=
  match s.val, t.val with
  | 0, 0 => goto (fun _ => .accept)
  | 0, 1 => push ordinalCell (fun _ => true) (goto (fun _ => .accept))
  | 1, 0 => push ordinalCell (fun _ => true)
      (push ordinalCell (fun _ => true) (goto (fun _ => .accept)))
  | _, _ => push ordinalCell (fun _ => true)
      (push ordinalCell (fun _ => true)
        (push ordinalCell (fun _ => true) (goto (fun _ => .accept))))

noncomputable def program (s t : Fin 2) :
    Label → TM2.Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .vertexCopy => pop vCell (fun _ b => b)
      (branch Option.isSome
        (push scratchCell (fun b => b.getD false)
          (push ordinalCell (fun _ => true)
            (push ordinalCell (fun _ => true)
              (push ordinalCell (fun _ => true)
                (push ordinalCell (fun _ => true) (goto (fun _ => .vertexCopy)))))))
        (goto (fun _ => .vertexRestore)))
  | .vertexRestore => pop scratchCell (fun _ b => b)
      (branch Option.isSome
        (push vCell (fun b => b.getD false) (goto (fun _ => .vertexRestore)))
        (goto (fun _ => .nCopy)))
  | .nCopy => pop nCell (fun _ b => b)
      (branch Option.isSome
        (push scratchCell (fun b => b.getD false)
          (push ordinalCell (fun _ => true) (goto (fun _ => .nCopy))))
        (goto (fun _ => .nRestore)))
  | .nRestore => pop scratchCell (fun _ b => b)
      (branch Option.isSome
        (push nCell (fun b => b.getD false) (goto (fun _ => .nRestore)))
        (goto (fun _ => .offset)))
  | .offset => offsetStmt s t
  | .accept => load (fun _ => none) halt

noncomputable def run (s t : Fin 2) (steps : Nat) (c : Config) : Config :=
  ((advance (program s t))^[steps]) c

private theorem frame_v_get (nw vw ow sw a b c : List Bool) :
    frame nw vw ow sw a b c vCell = vw := by
  simp [frame, n_ne_v.symm]

private theorem frame_n_get (nw vw ow sw a b c : List Bool) :
    frame nw vw ow sw a b c nCell = nw := by simp [frame]

private theorem frame_scratch_get (nw vw ow sw a b c : List Bool) :
    frame nw vw ow sw a b c scratchCell = sw := by
  simp [frame, n_ne_scratch.symm, v_ne_scratch.symm,
    ord_ne_scratch.symm]

private theorem frame_ord_get (nw vw ow sw a b c : List Bool) :
    frame nw vw ow sw a b c ordinalCell = ow := by
  simp [frame, n_ne_ord.symm, v_ne_ord.symm]

private theorem pairBank_inl (n v ordinal : Nat) (saved output count : List Bool)
    (x : PrefixSharedCore.Stack) (hx : x ≠ PairUnitLift.ordinalCell) :
    PairUnitLift.pairBank n v ordinal saved output count (.inl x) =
      PrefixGateReady.blank n ordinal saved output count x := by
  have he : PairUnitLift.unitEmbedding x = (.inl x : Stack) := by
    simp [PairUnitLift.unitEmbedding, hx]
  rw [← he, PairUnitLift.pairBank, BitMachineStackEmbedding.bank_at]

theorem frame_pairBank (n v ordinal : Nat) (saved output count : List Bool) :
    frame (List.replicate n true) (List.replicate v true)
      (List.replicate ordinal true) [] saved output count =
      PairUnitLift.pairBank n v ordinal saved output count := by
  funext x
  classical
  by_cases hn : x = nCell
  · subst x
    rw [frame_n_get]
    change List.replicate n true =
      PairUnitLift.pairBank n v ordinal saved output count (.inl (.inl 0))
    rw [pairBank_inl n v ordinal saved output count (.inl 0) (by simp [PairUnitLift.ordinalCell])]
    rfl
  by_cases hv : x = vCell
  · subst x
    rw [frame_v_get]
    exact (PairUnitLift.vertex_word n v ordinal saved output count).symm
  by_cases ho : x = ordinalCell
  · subst x
    rw [frame_ord_get]
    exact (PairUnitLift.ordinal_word n v ordinal saved output count).symm
  by_cases hs : x = scratchCell
  · subst x
    have ht : PrefixGateOperands.temp ≠ PairUnitLift.ordinalCell := by
      intro he
      have : scratchCell = vCell := congrArg Sum.inl he
      exact v_ne_scratch this.symm
    simp only [frame_scratch_get]
    change [] = PairUnitLift.pairBank n v ordinal saved output count
      (.inl PrefixGateOperands.temp)
    rw [pairBank_inl n v ordinal saved output count PrefixGateOperands.temp ht]
    exact (PrefixGateReady.blank_temp n ordinal saved output count).symm
  have hf : frame (List.replicate n true) (List.replicate v true)
      (List.replicate ordinal true) [] saved output count x =
      PairUnitLift.pairBank 0 0 0 saved output count x := by
    simp [frame, hn, hv, ho, hs]
  rw [hf]
  cases x with
  | inr u => cases u; exact False.elim (ho rfl)
  | inl y =>
      have hy : y ≠ PairUnitLift.ordinalCell := by
        intro he
        apply hv
        change Sum.inl y = Sum.inl PairUnitLift.ordinalCell
        rw [he]
      rw [pairBank_inl 0 0 0 saved output count y hy,
        pairBank_inl n v ordinal saved output count y hy]
      cases y with
      | inr z => rfl
      | inl i =>
          fin_cases i
          · exact False.elim (hn rfl)
          · exact False.elim (hv rfl)
          all_goals rfl

private theorem vertex_cons (s t : Fin 2) (ctl : Option Bool)
    (nw vw ow sw a b c : List Bool) :
    advance (program s t)
      (⟨some .vertexCopy, ctl, frame nw (true :: vw) ow sw a b c⟩ : Config) =
      ⟨some .vertexCopy, some true,
        frame nw vw (List.replicate 4 true ++ ow) (true :: sw) a b c⟩ := by
  simp [advance, TM2.step, program, TM2.stepAux,
    frame_v_get, frame_scratch_get, frame_ord_get,
    frame_v, frame_scratch, frame_ord,
    Function.update_self, List.replicate]

private theorem vertex_nil (s t : Fin 2) (ctl : Option Bool)
    (nw ow sw a b c : List Bool) :
    advance (program s t)
      (⟨some .vertexCopy, ctl, frame nw [] ow sw a b c⟩ : Config) =
      ⟨some .vertexRestore, none, frame nw [] ow sw a b c⟩ := by
  simp [advance, TM2.step, program, TM2.stepAux, frame_v_get]

private theorem vertex_restore_cons (s t : Fin 2) (ctl : Option Bool)
    (nw vw ow sw a b c : List Bool) :
    advance (program s t)
      (⟨some .vertexRestore, ctl, frame nw vw ow (true :: sw) a b c⟩ : Config) =
      ⟨some .vertexRestore, some true, frame nw (true :: vw) ow sw a b c⟩ := by
  simp [advance, TM2.step, program, TM2.stepAux,
    frame_scratch_get, frame_v_get, frame_scratch, frame_v]

private theorem vertex_restore_nil (s t : Fin 2) (ctl : Option Bool)
    (nw vw ow a b c : List Bool) :
    advance (program s t)
      (⟨some .vertexRestore, ctl, frame nw vw ow [] a b c⟩ : Config) =
      ⟨some .nCopy, none, frame nw vw ow [] a b c⟩ := by
  simp [advance, TM2.step, program, TM2.stepAux, frame_scratch_get]

private theorem n_cons (s t : Fin 2) (ctl : Option Bool)
    (nw vw ow sw a b c : List Bool) :
    advance (program s t)
      (⟨some .nCopy, ctl, frame (true :: nw) vw ow sw a b c⟩ : Config) =
      ⟨some .nCopy, some true, frame nw vw (true :: ow) (true :: sw) a b c⟩ := by
  simp [advance, TM2.step, program, TM2.stepAux,
    frame_n_get, frame_scratch_get, frame_ord_get,
    frame_n, frame_scratch, frame_ord]

private theorem n_nil (s t : Fin 2) (ctl : Option Bool)
    (vw ow sw a b c : List Bool) :
    advance (program s t)
      (⟨some .nCopy, ctl, frame [] vw ow sw a b c⟩ : Config) =
      ⟨some .nRestore, none, frame [] vw ow sw a b c⟩ := by
  simp [advance, TM2.step, program, TM2.stepAux, frame_n_get]

private theorem n_restore_cons (s t : Fin 2) (ctl : Option Bool)
    (nw vw ow sw a b c : List Bool) :
    advance (program s t)
      (⟨some .nRestore, ctl, frame nw vw ow (true :: sw) a b c⟩ : Config) =
      ⟨some .nRestore, some true, frame (true :: nw) vw ow sw a b c⟩ := by
  simp [advance, TM2.step, program, TM2.stepAux,
    frame_scratch_get, frame_n_get, frame_scratch, frame_n]

private theorem n_restore_nil (s t : Fin 2) (ctl : Option Bool)
    (nw vw ow a b c : List Bool) :
    advance (program s t)
      (⟨some .nRestore, ctl, frame nw vw ow [] a b c⟩ : Config) =
      ⟨some .offset, none, frame nw vw ow [] a b c⟩ := by
  simp [advance, TM2.step, program, TM2.stepAux, frame_scratch_get]

private theorem offset_step (s t : Fin 2) (ow : List Bool)
    (nw vw a b c : List Bool) :
    advance (program s t)
      (⟨some .offset, none, frame nw vw ow [] a b c⟩ : Config) =
      ⟨some .accept, none,
        frame nw vw (List.replicate (2*s.val+t.val) true ++ ow) [] a b c⟩ := by
  fin_cases s <;> fin_cases t <;>
    simp [advance, TM2.step, program, offsetStmt, TM2.stepAux,
      frame_ord_get, frame_ord, List.replicate]

private theorem accept_step (s t : Fin 2) (nw vw ow a b c : List Bool) :
    advance (program s t)
      (⟨some .accept, none, frame nw vw ow [] a b c⟩ : Config) =
      ⟨none, none, frame nw vw ow [] a b c⟩ := by
  simp [advance, TM2.step, program, TM2.stepAux]

private theorem run_succ (s t : Fin 2) (k : Nat) (c : Config) :
    run s t (k+1) c = run s t k (advance (program s t) c) := by
  simp only [run, Function.iterate_succ_apply]

private theorem run_add (s t : Fin 2) (i j : Nat) (c : Config) :
    run s t (i+j) c = run s t j (run s t i c) := by
  rw [Nat.add_comm]
  simp only [run, Function.iterate_add_apply]

private theorem replicate_append_true (k : Nat) (tail : List Bool) :
    List.replicate k true ++ true :: tail =
      true :: (List.replicate k true ++ tail) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih]

private theorem vertex_copy_run (s t : Fin 2) (k : Nat) (ctl : Option Bool)
    (nw ow sw a b c : List Bool) :
    run s t (k+1)
      ⟨some .vertexCopy, ctl, frame nw (List.replicate k true) ow sw a b c⟩ =
      ⟨some .vertexRestore, none,
        frame nw [] (List.replicate (4*k) true ++ ow)
          (List.replicate k true ++ sw) a b c⟩ := by
  induction k generalizing ctl ow sw with
  | zero => simpa [run_succ, run] using vertex_nil s t ctl nw ow sw a b c
  | succ k ih =>
      rw [show k+1+1 = (k+1)+1 by omega, run_succ]
      simp only [List.replicate_succ]
      rw [vertex_cons]
      have h := ih (some true) (List.replicate 4 true ++ ow) (true :: sw)
      simpa [List.replicate_add, List.append_assoc, Nat.mul_add,
        replicate_append_true] using h

private theorem vertex_restore_run (s t : Fin 2) (k : Nat)
    (ctl : Option Bool) (nw vw ow a b c : List Bool) :
    run s t (k+1)
      ⟨some .vertexRestore, ctl,
        frame nw vw ow (List.replicate k true) a b c⟩ =
      ⟨some .nCopy, none,
        frame nw (List.replicate k true ++ vw) ow [] a b c⟩ := by
  induction k generalizing ctl vw with
  | zero => simpa [run_succ, run] using vertex_restore_nil s t ctl nw vw ow a b c
  | succ k ih =>
      rw [run_succ]
      simp only [List.replicate_succ]
      rw [vertex_restore_cons]
      simpa [List.replicate_succ, List.append_assoc,
        replicate_append_true] using
        ih (some true) (true :: vw)

private theorem n_copy_run (s t : Fin 2) (k : Nat) (ctl : Option Bool)
    (vw ow sw a b c : List Bool) :
    run s t (k+1)
      ⟨some .nCopy, ctl, frame (List.replicate k true) vw ow sw a b c⟩ =
      ⟨some .nRestore, none,
        frame [] vw (List.replicate k true ++ ow)
          (List.replicate k true ++ sw) a b c⟩ := by
  induction k generalizing ctl ow sw with
  | zero => simpa [run_succ, run] using n_nil s t ctl vw ow sw a b c
  | succ k ih =>
      rw [run_succ]
      simp only [List.replicate_succ]
      rw [n_cons]
      simpa [List.replicate_succ, List.append_assoc,
        replicate_append_true] using
        ih (some true) (true :: ow) (true :: sw)

private theorem n_restore_run (s t : Fin 2) (k : Nat)
    (ctl : Option Bool) (nw vw ow a b c : List Bool) :
    run s t (k+1)
      ⟨some .nRestore, ctl,
        frame nw vw ow (List.replicate k true) a b c⟩ =
      ⟨some .offset, none,
        frame (List.replicate k true ++ nw) vw ow [] a b c⟩ := by
  induction k generalizing ctl nw with
  | zero => simpa [run_succ, run] using n_restore_nil s t ctl nw vw ow a b c
  | succ k ih =>
      rw [run_succ]
      simp only [List.replicate_succ]
      rw [n_restore_cons]
      simpa [List.replicate_succ, List.append_assoc,
        replicate_append_true] using
        ih (some true) (true :: nw)

def clock (n v : Nat) : Nat := 2*(n+v)+6

theorem framed_run (n v : Nat) (s t : Fin 2)
    (saved output count : List Bool) :
    run s t (clock n v)
      ⟨some .vertexCopy, none,
        frame (List.replicate n true) (List.replicate v true) [] []
          saved output count⟩ =
      ⟨none, none,
        frame (List.replicate n true) (List.replicate v true)
          (List.replicate (n+4*v+2*s.val+t.val) true) []
          saved output count⟩ := by
  rw [clock, show 2*(n+v)+6 =
    (v+1)+((v+1)+((n+1)+((n+1)+(1+1)))) by omega]
  rw [run_add s t (v+1), vertex_copy_run]
  simp only [List.append_nil]
  rw [run_add s t (v+1), vertex_restore_run]
  simp only [List.append_nil]
  rw [run_add s t (n+1), n_copy_run]
  simp only [List.append_nil]
  rw [run_add s t (n+1), n_restore_run]
  simp only [List.append_nil]
  rw [run_add s t 1 1]
  simp only [run, Function.iterate_one]
  rw [offset_step, accept_step]
  simp only [List.replicate_append_replicate]
  congr 1
  congr 1
  congr 1
  omega

/-- Exact same-bank installation, with the vertex cell and all three
accumulator cells unchanged and every scratch cell blank at the endpoint. -/
theorem pairBank_run (n v : Nat) (s t : Fin 2)
    (saved output count : List Bool) :
    run s t (clock n v)
      (⟨some .vertexCopy, none,
        PairUnitLift.pairBank n v 0 saved output count⟩ : Config) =
      ⟨none, none,
        PairUnitLift.pairBank n v (n+4*v+2*s.val+t.val)
          saved output count⟩ := by
  rw [← frame_pairBank n v 0 saved output count,
    ← frame_pairBank n v (n+4*v+2*s.val+t.val) saved output count]
  exact framed_run n v s t saved output count

theorem pairBank_run_source {n : Nat} (v : Fin n) (s t : Fin 2)
    (saved output count : List Bool) :
    run s t (clock n v.val)
      (⟨some .vertexCopy, none,
        PairUnitLift.pairBank n v.val 0 saved output count⟩ : Config) =
      ⟨none, none,
        PairUnitLift.pairBank n v.val (pairOrdinal v s t)
          saved output count⟩ := by
  simpa only [pairOrdinal] using
    pairBank_run n v.val s t saved output count

theorem clock_bound {n : Nat} (v : Fin n) :
    clock n v.val ≤ 4*n+6 := by
  unfold clock
  omega

#print axioms pairBank_run
#print axioms pairBank_run_source
#print axioms clock_bound

end EthInapproximability.CurrentPaper.SourceBooleanPrefix.PairOrdinalLoader
