import EthInapproximability.CurrentPaper.EncodedGraphMachine

/-! # Binary fields inside the concrete graph controller

Source: v8 graph encoding and bit-machine implementation. These are exact
transition equations for the actual finite controller, not a RAM abstraction.
-/

namespace EthInapproximability.CurrentPaper.EncodedGraphMachineFields

open Turing BitMachineEncoding EncodedGraphMachine

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

end EthInapproximability.CurrentPaper.EncodedGraphMachineFields
