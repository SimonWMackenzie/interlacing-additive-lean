import CurrentAdditive.QuarticHeaderStage
import Paper2.E3Loops

/-! A fixed physical projection from `pair a b` to its raw second field `b`. -/

namespace Paper2.CurrentAdditive.QuarticClassEndpoint.PairSecond

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.Unit4Shell.Loops

inductive Label
  | parse | done
  deriving DecidableEq, Fintype

abbrev Stack := Fin 2
abbrev Control := Option Bool × Unit

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .parse => parseStmt 0 1 .parse .done
  | .done => .halt

noncomputable def machine : BitMachine.Machine :=
  ofFinite (0 : Stack) (0 : Stack) Label.parse ((none, ()) : Control) program

theorem machine_outputs (a b : List Bool) :
    machine.OutputsWithin (EncodedComplexity.pair a b) b (a.length + 2) := by
  let S₀ : Stack → List Bool :=
    fun j => if j = 0 then EncodedComplexity.pair a b else []
  have e₁ := parse_loop program (0 : Stack) 1 Label.parse Label.done
    (by decide) rfl a b S₀ none ()
    (by simp [S₀, EncodedComplexity.pair])
  let S₁ := Function.update (Function.update S₀ 1 (a.reverse ++ S₀ 1)) 0 b
  have e₂ := halt_step program Label.done rfl (some false, ()) S₁
  have hrun := iter_chain e₁ (show (advance program)^[1] _ = _ from e₂)
  have hraw : rawInit (0 : Stack) Label.parse ((none, ()) : Control)
      (EncodedComplexity.pair a b) =
      ⟨some Label.parse, (none, ()), S₀⟩ := rfl
  refine outputsWithin_of_raw_run (0 : Stack) (0 : Stack)
    Label.parse ((none, ()) : Control) program
    (EncodedComplexity.pair a b) b (a.length + 1 + 1) (a.length + 2)
    (by omega) ?_ ?_
  · rw [hraw, hrun]
  · rw [hraw, hrun]
    simp [S₁]

#print axioms machine_outputs

end Paper2.CurrentAdditive.QuarticClassEndpoint.PairSecond
