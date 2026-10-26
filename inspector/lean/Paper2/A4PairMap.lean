import Paper2.A4Loops
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding
import EthInapproximability.CurrentPaper.EncodedComplexity

/-!
# Unit 4 (Paper A) glue: the physical first-field map combinator `H_PairMap`

Owner lane `owner:a-unit4-shell-3` (private, 26 September 2026).

For every `BitMachine.Machine` `M` there is ONE fixed finite machine `machine M` which, on the
literal word `EncodedComplexity.pair x t = field x ++ t`, prints `pair y t` whenever
`M.OutputsWithin x y T`. Stacks: `main` (input AND output), `temp`, and a disjoint copy of
all stacks of `M` (`BitMachineStackEmbedding`, admitted). Phases, each a fixed statement:

1. `parse`: consume the self-delimiting field `x` from `main` (payload reversed onto `temp`);
   `main` now holds exactly the raw suffix `t`, which is never touched again until phase 5.
2. `load`: move `temp` onto `M`'s input stack (so it holds exactly `x`; every other stack of
   `M` is empty and `M`'s control is `M.initial`): this is literally `M.init x`.
3. `M` runs in place (inline embedding; `M`'s halt continues to phase 4).
4. `move`: move `M`'s output stack (`y`) onto `temp` (reversed).
5. `emit0`/`emit`: push `false`, then for each bit of `reverse y` push the bit and `true`:
   `main` becomes `field y ++ t`. `done` halts.

Clock: `2|x| + T + 2|y| + 6`, with `|y| ≤ |x| + T·pushBound M` (admitted
`output_length_bound`). No input is inserted: the machine starts from `Machine.init`.
**No ledger row is closed.**
-/

namespace Paper2.Unit4Shell.PairMap

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.Unit4Shell.Loops

inductive PL
  | parse | load | move | emit0 | emit | done
  deriving DecidableEq, Fintype

variable (M : BitMachine.Machine)

abbrev Stack := Fin 2 ⊕ Fin M.stackCount
abbrev Label := PL ⊕ Fin M.labelCount
abbrev Control := Option Bool × Fin M.controlCount

def mainS : Stack M := .inl 0
def tempS : Stack M := .inl 1

def mStack : Fin M.stackCount ↪ Stack M := ⟨Sum.inr, Sum.inr_injective⟩

def embedC (v : Fin M.controlCount) : Control M := (none, v)

def program : Label M → TM2.Stmt (fun _ : Stack M => Bool) (Label M) (Control M)
  | .inl .parse => parseStmt (mainS M) (tempS M) (.inl .parse) (.inl .load)
  | .inl .load => moveStmt (tempS M) (.inr M.input) (.inl .load) (.inr M.start)
  | .inl .move => moveStmt (.inr M.output) (tempS M) (.inl .move) (.inl .emit0)
  | .inl .emit0 => pushFalseStmt (mainS M) (.inl .emit)
  | .inl .emit => emitStmt (tempS M) (mainS M) (.inl .emit) (.inl .done)
  | .inl .done => .halt
  | .inr l => BitMachineStackEmbedding.stmt (mStack M) Sum.inr (embedC M) Prod.snd
      (some (.inl .move)) (M.program l)

/-- THE fixed pair-map machine for `M`. -/
noncomputable def machine : BitMachine.Machine :=
  ofFinite (mainS M) (mainS M) (.inl .parse) ((none, M.initial) : Control M) (program M)

theorem machine_program_eq (l : Fin M.labelCount) :
    program M (.inr l) = BitMachineStackEmbedding.stmt (mStack M) Sum.inr (embedC M)
      Prod.snd (some (.inl .move)) (M.program l) := rfl

theorem main_ne_temp : mainS M ≠ tempS M := by simp [mainS, tempS]

/-- The exact charged run on `pair x t`. -/
theorem machine_outputs (x y t : List Bool) (T : ℕ) (h : M.OutputsWithin x y T) :
    (machine M).OutputsWithin (EncodedComplexity.pair x t) (EncodedComplexity.pair y t)
      (2 * x.length + T + 2 * y.length + 6) := by
  obtain ⟨tM, htM, hhalt, hout⟩ := h
  let S0 : Stack M → List Bool := fun k => if k = mainS M then EncodedComplexity.pair x t else []
  -- phase 1: parse
  have hS0main : S0 (mainS M) = EncodedCommunication.field x ++ t := by
    simp [S0, EncodedComplexity.pair]
  have e1 := parse_loop (program M) (mainS M) (tempS M) (.inl .parse) (.inl .load)
    (main_ne_temp M) rfl x t S0 none M.initial hS0main
  set S1 := Function.update (Function.update S0 (tempS M) (x.reverse ++ S0 (tempS M)))
    (mainS M) t with hS1
  -- phase 2: load
  have hS1temp : S1 (tempS M) = x.reverse := by
    simp [hS1, S0, mainS, tempS]
  have e2 := move_loop (program M) (tempS M) (.inr M.input) (.inl .load) (.inr M.start)
    (by simp [tempS]) rfl x.reverse S1 (some false) M.initial hS1temp
  rw [List.length_reverse] at e2
  set S2 := Function.update (Function.update S1 (.inr M.input)
    (x.reverse.reverse ++ S1 (.inr M.input))) (tempS M) [] with hS2
  -- phase 3: the embedded machine
  have hbank : BitMachineStackEmbedding.bank (mStack M) S2 (M.init x).stk = S2 := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro j
    by_cases hj : j = M.input
    · subst hj
      simp [BitMachine.Machine.init, hS2, hS1, S0, mStack, mainS, tempS]
    · simp [BitMachine.Machine.init, hj, hS2, hS1, S0, mStack, mainS, tempS]
  have hentry : (⟨some (.inr M.start), (none, M.initial), S2⟩ :
      TM2.Cfg (fun _ : Stack M => Bool) (Label M) (Control M)) =
      BitMachineStackEmbedding.cfg (mStack M) S2 Sum.inr (embedC M) (some (.inl .move))
        (M.init x) := by
    unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    rw [show (BitMachineInline.cfg Sum.inr (embedC M) (some (Sum.inl PL.move))
      (M.init x)).stk = (M.init x).stk from rfl, hbank]
    rfl
  have hh : (((advance M.program)^[tM]) (M.init x)).l = none := hhalt
  obtain ⟨n3, hn3, e3⟩ := BitMachineStackEmbedding.outputs (mStack M) S2 Sum.inr (embedC M)
    Prod.snd (by intro v; rfl) (some (.inl .move)) M.program (program M)
    (machine_program_eq M) (M.init x) tM hh
  set c := ((advance M.program)^[tM]) (M.init x) with hc
  have hcout : c.stk M.output = y := hout
  set S3 := BitMachineStackEmbedding.bank (mStack M) S2 c.stk with hS3
  have hexit : BitMachineStackEmbedding.cfg (mStack M) S2 Sum.inr (embedC M)
      (some (.inl .move)) c =
      (⟨some (.inl .move), (none, c.var), S3⟩ :
        TM2.Cfg (fun _ : Stack M => Bool) (Label M) (Control M)) := by
    simp only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg, hh, embedC, hS3]
  -- phase 4: move the output of `M` to `temp`
  have hS3out : S3 (.inr M.output) = y := by
    rw [hS3, show (Sum.inr M.output : Stack M) = mStack M M.output from rfl,
      BitMachineStackEmbedding.bank_at, hcout]
  have hout_temp : S3 (tempS M) = [] := by
    rw [hS3, BitMachineStackEmbedding.bank_outside]
    · simp [hS2, tempS]
    · rintro ⟨j, hj⟩
      simp [mStack, tempS] at hj
  have hout_main : S3 (mainS M) = t := by
    rw [hS3, BitMachineStackEmbedding.bank_outside]
    · simp [hS2, hS1, mainS, tempS]
    · rintro ⟨j, hj⟩
      simp [mStack, mainS] at hj
  have e4 := move_loop (program M) (.inr M.output) (tempS M) (.inl .move) (.inl .emit0)
    (by simp [tempS]) rfl y S3 none c.var hS3out
  set S4 := Function.update (Function.update S3 (tempS M) (y.reverse ++ S3 (tempS M)))
    (.inr M.output) [] with hS4
  -- phase 5: emit
  have e5 := pushFalse_step (program M) (mainS M) (.inl .emit0) (.inl .emit) rfl
    (none, c.var) S4
  set S5 := Function.update S4 (mainS M) (false :: S4 (mainS M)) with hS5
  have htm : tempS M ≠ Sum.inr M.output := by simp [tempS]
  have hmm : mainS M ≠ Sum.inr M.output := by simp [mainS]
  have hS5temp : S5 (tempS M) = y.reverse := by
    rw [hS5, Function.update_of_ne (main_ne_temp M).symm, hS4, Function.update_of_ne htm,
      Function.update_self, hout_temp, List.append_nil]
  have e6 := emit_loop (program M) (tempS M) (mainS M) (.inl .emit) (.inl .done)
    (main_ne_temp M).symm rfl y.reverse S5 none c.var hS5temp
  rw [List.length_reverse] at e6
  set S6 := Function.update (Function.update S5 (mainS M)
    (y.reverse.foldl emitFold (S5 (mainS M)))) (tempS M) [] with hS6
  have e7 := halt_step (program M) (.inl .done) rfl (none, c.var) S6
  have hS6main : S6 (mainS M) = EncodedCommunication.field y ++ t := by
    have h5 : S5 (mainS M) = false :: t := by
      rw [hS5, Function.update_self, hS4, Function.update_of_ne hmm,
        Function.update_of_ne (main_ne_temp M), hout_main]
    simp only [hS6, Function.update_of_ne (main_ne_temp M), Function.update_self, h5]
    exact emit_reverse_field y t
  -- chain the phases
  have r12 := iter_chain e1 e2
  have r123 := iter_chain r12 (hentry ▸ e3)
  rw [hexit] at r123
  have r4 := iter_chain r123 e4
  have r5 := iter_chain r4 (show (advance (program M))^[1] _ = _ from e5)
  have r6 := iter_chain r5 e6
  have r7 := iter_chain r6 (show (advance (program M))^[1] _ = _ from e7)
  have hraw : rawInit (mainS M) (Sum.inl PL.parse : Label M) ((none, M.initial) : Control M)
      (EncodedComplexity.pair x t) = ⟨some (Sum.inl PL.parse), (none, M.initial), S0⟩ := rfl
  refine outputsWithin_of_raw_run (mainS M) (mainS M) (Sum.inl PL.parse : Label M)
    ((none, M.initial) : Control M) (program M) (EncodedComplexity.pair x t)
    (EncodedComplexity.pair y t)
    (x.length + 1 + (x.length + 1) + n3 + (y.length + 1) + 1 + (y.length + 1) + 1) _
    (by omega) ?_ ?_
  · rw [hraw, r7]
  · rw [hraw, r7]
    exact hS6main

/-- **The pair-map combinator (generic glue contract `H_PairMap`, literal body).** For every
machine `M` there is one fixed machine `M'` and constants `C, E` such that every charged run
`M.OutputsWithin x y T` lifts to `M'.OutputsWithin (pair x t) (pair y t)` within
`C·(T + |pair x t| + 1)^E`. Does not close a ledger row. -/
theorem pair_map : ∀ M : BitMachine.Machine, ∃ (M' : BitMachine.Machine) (C E : ℕ),
    ∀ (x y t : List Bool) (T : ℕ), M.OutputsWithin x y T →
      M'.OutputsWithin (EncodedComplexity.pair x t) (EncodedComplexity.pair y t)
        (C * (T + (EncodedComplexity.pair x t).length + 1) ^ E) := by
  intro M
  refine ⟨machine M, 4 + 2 * M.pushBound, 1, ?_⟩
  intro x y t T h
  have hy := BitMachine.output_length_bound M h
  have hr := machine_outputs M x y t T h
  apply BitMachine.outputsWithin_mono _ hr
  rw [EncodedComplexity.pair_length, pow_one]
  have hTp : T * M.pushBound ≤ T * M.pushBound := le_rfl
  nlinarith [Nat.zero_le (M.pushBound * x.length), Nat.zero_le (M.pushBound * t.length),
    Nat.zero_le M.pushBound, Nat.zero_le t.length]

end Paper2.Unit4Shell.PairMap
