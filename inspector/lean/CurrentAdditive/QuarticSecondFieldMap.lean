import Paper2.A4Loops
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding
import EthInapproximability.CurrentPaper.EncodedComplexity

/-! A fixed physical combinator applying a bit machine to the second field of
`pair header word`, while preserving the arbitrary first field `header`. -/

namespace Paper2.CurrentAdditive.QuarticSecondFieldMap

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.Unit4Shell.Loops

noncomputable section

inductive Phase
  | parse | load0 | load1 | move0 | move1 | emit0 | emit | done
  deriving DecidableEq, Fintype

variable (M : BitMachine.Machine)

abbrev Stack := Fin 3 ⊕ Fin M.stackCount
abbrev Label := Phase ⊕ Fin M.labelCount
abbrev Control := Option Bool × Fin M.controlCount

def mainS : Stack M := .inl 0
def headS : Stack M := .inl 1
def revS : Stack M := .inl 2
def mStack : Fin M.stackCount ↪ Stack M := ⟨Sum.inr, Sum.inr_injective⟩
def embedC (v : Fin M.controlCount) : Control M := (none, v)

def program : Label M → TM2.Stmt (fun _ : Stack M => Bool) (Label M) (Control M)
  | .inl .parse => parseStmt (mainS M) (headS M) (.inl .parse) (.inl .load0)
  | .inl .load0 => moveStmt (mainS M) (revS M) (.inl .load0) (.inl .load1)
  | .inl .load1 => moveStmt (revS M) (.inr M.input) (.inl .load1) (.inr M.start)
  | .inl .move0 => moveStmt (.inr M.output) (revS M) (.inl .move0) (.inl .move1)
  | .inl .move1 => moveStmt (revS M) (mainS M) (.inl .move1) (.inl .emit0)
  | .inl .emit0 => pushFalseStmt (mainS M) (.inl .emit)
  | .inl .emit => emitStmt (headS M) (mainS M) (.inl .emit) (.inl .done)
  | .inl .done => .halt
  | .inr l => BitMachineStackEmbedding.stmt (mStack M) Sum.inr (embedC M) Prod.snd
      (some (.inl .move0)) (M.program l)

noncomputable def machine : BitMachine.Machine :=
  ofFinite (mainS M) (mainS M) (.inl .parse)
    ((none, M.initial) : Control M) (program M)

theorem machine_program_eq (l : Fin M.labelCount) :
    program M (.inr l) = BitMachineStackEmbedding.stmt (mStack M) Sum.inr (embedC M)
      Prod.snd (some (.inl .move0)) (M.program l) := rfl

theorem main_ne_head : mainS M ≠ headS M := by simp [mainS, headS]
theorem main_ne_rev : mainS M ≠ revS M := by simp [mainS, revS]
theorem head_ne_rev : headS M ≠ revS M := by simp [headS, revS]

theorem machine_outputs (header word result : List Bool) (T : ℕ)
    (h : M.OutputsWithin word result T) :
    (machine M).OutputsWithin
      (EncodedComplexity.pair header word)
      (EncodedComplexity.pair header result)
      (2 * header.length + 2 * word.length + T +
        2 * result.length + 2 * header.length + 11) := by
  obtain ⟨tM, htM, hhalt, hout⟩ := h
  let S0 : Stack M → List Bool := fun k =>
    if k = mainS M then EncodedComplexity.pair header word else []
  have hS0main : S0 (mainS M) = EncodedCommunication.field header ++ word := by
    simp [S0, EncodedComplexity.pair]
  have e1 := parse_loop (program M) (mainS M) (headS M) (.inl .parse) (.inl .load0)
    (main_ne_head M) rfl header word S0 none M.initial hS0main
  set S1 := Function.update (Function.update S0 (headS M)
    (header.reverse ++ S0 (headS M))) (mainS M) word with hS1
  have hS1main : S1 (mainS M) = word := by simp [S1]
  have e2 := move_loop (program M) (mainS M) (revS M) (.inl .load0) (.inl .load1)
    (main_ne_rev M) rfl word S1 (some false) M.initial hS1main
  set S2 := Function.update (Function.update S1 (revS M)
    (word.reverse ++ S1 (revS M))) (mainS M) [] with hS2
  have hS2rev : S2 (revS M) = word.reverse := by
    simp [S2, S1, S0, revS, headS, mainS]
  have e3 := move_loop (program M) (revS M) (.inr M.input) (.inl .load1) (.inr M.start)
    (by simp [revS]) rfl word.reverse S2 none M.initial hS2rev
  rw [List.length_reverse] at e3
  set S3 := Function.update (Function.update S2 (.inr M.input)
    (word.reverse.reverse ++ S2 (.inr M.input))) (revS M) [] with hS3
  have hbank : BitMachineStackEmbedding.bank (mStack M) S3 (M.init word).stk = S3 := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro j
    by_cases hj : j = M.input
    · subst j
      simp [BitMachine.Machine.init, hS3, hS2, hS1, S0,
        mStack, mainS, headS, revS]
    · simp [BitMachine.Machine.init, hj, hS3, hS2, hS1, S0,
        mStack, mainS, headS, revS]
  have hentry : (⟨some (.inr M.start), (none, M.initial), S3⟩ :
      TM2.Cfg (fun _ : Stack M => Bool) (Label M) (Control M)) =
      BitMachineStackEmbedding.cfg (mStack M) S3 Sum.inr (embedC M)
        (some (.inl .move0)) (M.init word) := by
    unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    rw [show (BitMachineInline.cfg Sum.inr (embedC M) (some (Sum.inl Phase.move0))
      (M.init word)).stk = (M.init word).stk from rfl, hbank]
    rfl
  have hh : (((advance M.program)^[tM]) (M.init word)).l = none := hhalt
  obtain ⟨n4, hn4, e4⟩ := BitMachineStackEmbedding.outputs (mStack M) S3 Sum.inr
    (embedC M) Prod.snd (by intro v; rfl) (some (.inl .move0))
    M.program (program M) (machine_program_eq M) (M.init word) tM hh
  set c := ((advance M.program)^[tM]) (M.init word) with hc
  have hcout : c.stk M.output = result := hout
  set S4 := BitMachineStackEmbedding.bank (mStack M) S3 c.stk with hS4
  have hexit : BitMachineStackEmbedding.cfg (mStack M) S3 Sum.inr (embedC M)
      (some (.inl .move0)) c =
      (⟨some (.inl .move0), (none, c.var), S4⟩ :
        TM2.Cfg (fun _ : Stack M => Bool) (Label M) (Control M)) := by
    simp only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg, hh, embedC, hS4]
  have hS4out : S4 (.inr M.output) = result := by
    rw [hS4, show (Sum.inr M.output : Stack M) = mStack M M.output from rfl,
      BitMachineStackEmbedding.bank_at, hcout]
  have hS4rev : S4 (revS M) = [] := by
    rw [hS4, BitMachineStackEmbedding.bank_outside]
    · simp [hS3, revS]
    · rintro ⟨j, hj⟩
      simp [mStack, revS] at hj
  have hS4head : S4 (headS M) = header.reverse := by
    rw [hS4, BitMachineStackEmbedding.bank_outside]
    · simp [hS3, hS2, hS1, S0, mainS, headS, revS]
    · rintro ⟨j, hj⟩
      simp [mStack, headS] at hj
  have hS4main : S4 (mainS M) = [] := by
    rw [hS4, BitMachineStackEmbedding.bank_outside]
    · simp [hS3, hS2, mainS, revS]
    · rintro ⟨j, hj⟩
      simp [mStack, mainS] at hj
  have e5 := move_loop (program M) (.inr M.output) (revS M) (.inl .move0) (.inl .move1)
    (by simp [revS]) rfl result S4 none c.var hS4out
  set S5 := Function.update (Function.update S4 (revS M)
    (result.reverse ++ S4 (revS M))) (.inr M.output) [] with hS5
  have hS5rev : S5 (revS M) = result.reverse := by
    rw [hS5, Function.update_of_ne (by simp [revS]), Function.update_self,
      hS4rev, List.append_nil]
  have hS5main : S5 (mainS M) = [] := by
    rw [hS5, Function.update_of_ne (by simp [mainS]),
      Function.update_of_ne (main_ne_rev M), hS4main]
  have hS5head : S5 (headS M) = header.reverse := by
    rw [hS5, Function.update_of_ne (by simp [headS]),
      Function.update_of_ne (head_ne_rev M), hS4head]
  have e6 := move_loop (program M) (revS M) (mainS M) (.inl .move1) (.inl .emit0)
    (main_ne_rev M).symm rfl result.reverse S5 none c.var hS5rev
  rw [List.length_reverse] at e6
  set S6 := Function.update (Function.update S5 (mainS M)
    (result.reverse.reverse ++ S5 (mainS M))) (revS M) [] with hS6
  have hS6main : S6 (mainS M) = result := by
    rw [hS6, Function.update_of_ne (main_ne_rev M),
      Function.update_self, List.reverse_reverse, hS5main, List.append_nil]
  have hS6head : S6 (headS M) = header.reverse := by
    rw [hS6, Function.update_of_ne (head_ne_rev M),
      Function.update_of_ne (main_ne_head M).symm]
    exact hS5head
  have e7 := pushFalse_step (program M) (mainS M) (.inl .emit0) (.inl .emit) rfl
    (none, c.var) S6
  set S7 := Function.update S6 (mainS M) (false :: S6 (mainS M)) with hS7
  have hS7head : S7 (headS M) = header.reverse := by
    rw [hS7, Function.update_of_ne (main_ne_head M).symm]
    exact hS6head
  have e8 := emit_loop (program M) (headS M) (mainS M) (.inl .emit) (.inl .done)
    (main_ne_head M).symm rfl header.reverse S7 none c.var hS7head
  rw [List.length_reverse] at e8
  set S8 := Function.update (Function.update S7 (mainS M)
    (header.reverse.foldl emitFold (S7 (mainS M)))) (headS M) [] with hS8
  have e9 := halt_step (program M) (.inl .done) rfl (none, c.var) S8
  have hS8main : S8 (mainS M) = EncodedCommunication.field header ++ result := by
    have h7 : S7 (mainS M) = false :: result := by simp [S7, hS6main]
    simp only [hS8, Function.update_of_ne (main_ne_head M), Function.update_self, h7]
    exact emit_reverse_field header result
  have r12 := iter_chain e1 e2
  have r123 := iter_chain r12 e3
  have r1234 := iter_chain r123 (hentry ▸ e4)
  rw [hexit] at r1234
  have r5 := iter_chain r1234 e5
  have r6 := iter_chain r5 e6
  have r7 := iter_chain r6 (show (advance (program M))^[1] _ = _ from e7)
  have r8 := iter_chain r7 e8
  have r9 := iter_chain r8 (show (advance (program M))^[1] _ = _ from e9)
  have hraw : rawInit (mainS M) (Sum.inl Phase.parse : Label M)
      ((none, M.initial) : Control M) (EncodedComplexity.pair header word) =
      ⟨some (Sum.inl Phase.parse), (none, M.initial), S0⟩ := rfl
  refine outputsWithin_of_raw_run (mainS M) (mainS M)
    (Sum.inl Phase.parse : Label M) ((none, M.initial) : Control M) (program M)
    (EncodedComplexity.pair header word) (EncodedComplexity.pair header result)
    (header.length + 1 + (word.length + 1) + (word.length + 1) + n4 +
      (result.length + 1) + (result.length + 1) + 1 + (header.length + 1) + 1) _
    (by omega) ?_ ?_
  · rw [hraw, r9]
  · rw [hraw, r9]
    exact hS8main

#print axioms machine_outputs

end
end Paper2.CurrentAdditive.QuarticSecondFieldMap
