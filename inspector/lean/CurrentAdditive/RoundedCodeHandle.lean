import CurrentAdditive.RoundedCodeAdmin
import Paper2.CodeDrawOutput
import Paper2.CodeBranchAdapter

/-! Literal consumption of a successful rounded ticket. Tickets and bits are
written to the accumulated output; a branch uses the existing physical unary
comparisons and child-code selector. No failure or fallback status is read. -/

namespace EthInapproximability.CurrentPaper.RoundedCodeHandle

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineStackEmbedding
open Paper2.GeneratorCode Paper2.GeneratorSerialization
noncomputable section

abbrev Stack := RoundedCodeDraw.Stack
abbrev BranchControl := Paper2.CodeBranchAdapter.Control
abbrev Control := BranchControl × Option Bool

def successBase : Paper2.CodeBranchAdapter.BaseControl :=
  let d := Paper2.CodeHeaderDraw.drawInitialControl
  ((d.1, (d.2.1, some true)), (none, some .branch3))

def branchInitial : BranchControl :=
  (((.first, none), Paper2.ChildSelect.idle .first), (successBase, none))

def initial : Control := (branchInitial, none)

def outputSlot (i : Fin 2) : Stack :=
  if i = 0 then .inl RoundedCodeDraw.oldResult else .inl Paper2.CodeHeaderDraw.output

def outputEmbed : Fin 2 ↪ Stack := ⟨outputSlot, by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp [outputSlot, RoundedCodeDraw.oldResult, Paper2.CodeHeaderDraw.d,
      Paper2.CodeHeaderDraw.output] at h ⊢⟩

def branchEmbed : Paper2.CodeBranchAdapter.Stack ↪ Stack :=
  ⟨Sum.inl, by intro i j h; exact Sum.inl_injective h⟩

inductive Label where
  | route (kind : Paper2.CodeHeaderMachine.Kind)
  | output (l : Paper2.CodeDrawOutput.Label)
  | branch (l : Paper2.CodeBranchAdapter.Label)
  deriving DecidableEq, Fintype

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .route kind =>
      if kind = .ticket then goto (fun _ => .output .ticket) else
      if kind = .bit then goto (fun _ => .output .bitStart) else
      if kind = .branch3 then goto (fun _ => .branch (.inr .route)) else halt
  | .output l => stmt outputEmbed Label.output (fun v => (branchInitial, v))
      Prod.snd none (Paper2.CodeDrawOutput.program l)
  | .branch l => stmt branchEmbed Label.branch (fun v => (v, none))
      Prod.fst none (Paper2.CodeBranchAdapter.program l)

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

def start (kind : Paper2.CodeHeaderMachine.Kind) (S : Stack → List Bool) : Config :=
  ⟨some (.route kind), initial, S⟩

def framedOutput (S : Stack → List Bool) (c : Paper2.CodeDrawOutput.Config) : Config :=
  cfg outputEmbed S Label.output (fun v => (branchInitial, v)) none c

def framedBranch (S : Stack → List Bool) (c : Paper2.CodeBranchAdapter.Config) : Config :=
  cfg branchEmbed S Label.branch (fun v => (v, none)) none c

theorem output_run (S : Stack → List Bool) (l : Paper2.CodeDrawOutput.Label)
    (input out : List Bool)
    (hi : S (.inl RoundedCodeDraw.oldResult) = input)
    (ho : S (.inl Paper2.CodeHeaderDraw.output) = out)
    (t : ℕ) (c : Paper2.CodeDrawOutput.Config)
    (hr : ((BitMachineEncoding.advance Paper2.CodeDrawOutput.program)^[t])
      (Paper2.CodeDrawOutput.cfg (some l) none input out) = c) (hh : c.l = none) :
    ∃ u ≤ t, run u ⟨some (.output l), initial, S⟩ = framedOutput S c := by
  have hbank : bank outputEmbed S
      (Paper2.CodeDrawOutput.cfg (some l) none input out).stk = S := by
    apply bank_eq_self
    intro i
    fin_cases i <;> simp [Paper2.CodeDrawOutput.cfg, Paper2.CodeDrawOutput.bank,
      outputEmbed, outputSlot, hi, ho]
  have hhalt : (((BitMachineEncoding.advance Paper2.CodeDrawOutput.program)^[t])
      (Paper2.CodeDrawOutput.cfg (some l) none input out)).l = none := by rw [hr]; exact hh
  obtain ⟨u, hu, hur⟩ := outputs outputEmbed S Label.output
    (fun v => (branchInitial, v)) Prod.snd (by intro v; rfl) none
    Paper2.CodeDrawOutput.program program (by intro k; rfl)
    (Paper2.CodeDrawOutput.cfg (some l) none input out) t hhalt
  rw [hr] at hur
  change run u ⟨some (.output l), initial,
      bank outputEmbed S (Paper2.CodeDrawOutput.cfg (some l) none input out).stk⟩ = _ at hur
  rw [hbank] at hur
  exact ⟨u, hu, hur⟩

theorem ticket_run (S : Stack → List Bool) (input out : List Bool)
    (hi : S (.inl RoundedCodeDraw.oldResult) = input)
    (ho : S (.inl Paper2.CodeHeaderDraw.output) = out) :
    ∃ t ≤ input.length + 2, run t (start .ticket S) =
      framedOutput S (Paper2.CodeDrawOutput.cfg none none [] (input.reverse ++ out)) := by
  have hr := Paper2.CodeDrawOutput.ticket_word input out none
  obtain ⟨u, hu, hur⟩ := output_run S .ticket input out hi ho _ _ hr rfl
  have hroute : run 1 (start .ticket S) = ⟨some (.output .ticket), initial, S⟩ := by
    simp [run, start, program, BitMachineEncoding.advance, TM2.step, TM2.stepAux]
  refine ⟨1 + u, by omega, ?_⟩
  have hjoin : run (1 + u) (start .ticket S) = run u (run 1 (start .ticket S)) := by
    rw [run, Nat.add_comm 1 u, Function.iterate_add_apply]
    rfl
  rw [hjoin, hroute]
  exact hur

theorem bit_run (S : Stack → List Bool) (i : Fin 2) (out : List Bool)
    (hi : S (.inl RoundedCodeDraw.oldResult) =
      (Paper2.RecursiveLabelCodecScratch.finCodec 2).encode i)
    (ho : S (.inl Paper2.CodeHeaderDraw.output) = out) :
    ∃ t ≤ i.val + 3, run t (start .bit S) =
      framedOutput S (Paper2.CodeDrawOutput.cfg none none [] (decide (i.val = 1) :: out)) := by
  have hr := Paper2.CodeDrawOutput.bit_codec i out
  obtain ⟨u, hu, hur⟩ := output_run S .bitStart _ out hi ho _ _ hr rfl
  have hroute : run 1 (start .bit S) = ⟨some (.output .bitStart), initial, S⟩ := by
    simp [run, start, program, BitMachineEncoding.advance, TM2.step, TM2.stepAux]
  refine ⟨1 + u, by omega, ?_⟩
  have hjoin : run (1 + u) (start .bit S) = run u (run 1 (start .bit S)) := by
    rw [run, Nat.add_comm 1 u, Function.iterate_add_apply]
    rfl
  rw [hjoin, hroute]
  exact hur

theorem branch_run (foreign : Paper2.CodeBranchAdapter.Stack → List Bool)
    (newPrivate : RoundedLoadedDraw.Stack → List Bool)
    (n out : List Bool) (i a b : ℕ) (first second third : Code) (rest : List Bool) :
    ∃ t ≤ 70 *
      (i + a + b + (Paper2.BranchSelection.inputWord first second third rest).length + 1),
      run t (framedBranch (Sum.elim foreign newPrivate)
        (Paper2.CodeBranchAdapter.initial successBase foreign n out i a b first second third rest)) =
      framedBranch (Sum.elim foreign newPrivate)
        (Paper2.CodeBranchAdapter.final successBase foreign n out i a b first second third rest) := by
  obtain ⟨t, ht, hr⟩ := Paper2.CodeBranchAdapter.branch_adapter successBase (by rfl)
    foreign n out i a b first second third rest
  have hh : (((BitMachineEncoding.advance Paper2.CodeBranchAdapter.program)^[t])
      (Paper2.CodeBranchAdapter.initial successBase foreign n out i a b first second third rest)).l = none := by
    change (Paper2.CodeBranchAdapter.run t _).l = none
    rw [hr]
    rfl
  obtain ⟨u, hu, hur⟩ := outputs branchEmbed (Sum.elim foreign newPrivate) Label.branch
    (fun v => (v, none)) Prod.fst (by intro v; rfl) none
    Paper2.CodeBranchAdapter.program program (by intro l; rfl)
    (Paper2.CodeBranchAdapter.initial successBase foreign n out i a b first second third rest) t hh
  change ((BitMachineEncoding.advance Paper2.CodeBranchAdapter.program)^[t]) _ = _ at hr
  rw [hr] at hur
  exact ⟨u, hu.trans ht, hur⟩

#print axioms ticket_run
#print axioms bit_run
#print axioms branch_run

end
end EthInapproximability.CurrentPaper.RoundedCodeHandle
