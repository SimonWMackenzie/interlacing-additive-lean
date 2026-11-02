import EthInapproximability.CurrentPaper.BoundedBitMachine

/-!
# Source-preserving preparation of a bounded probe

Source: frozen v8 `05-iteration.tex`, the bounded prefix-clock caller.
Five physical Boolean stacks hold the source argument, a budget word,
scratch, the packed argument, and the comparison cap. Four finite labels
copy the argument, prepend the unary time budget, and write the cap.
The two source stacks are restored, even for arbitrary budget-bit values.
-/

namespace EthInapproximability.CurrentPaper.CutoffProbePreparation

open Turing TM2.Stmt BitMachineEncoding

inductive Label where
  | scanBits | restoreBits | scanBudget | restoreBudget
  deriving DecidableEq, Fintype

def program : Label → TM2.Stmt (fun _ : Fin 5 => Bool) Label (Option Bool)
  | .scanBits => pop 0 (fun _ b => b)
      (branch Option.isSome
        (push 2 (fun b => b.getD false) (goto (fun _ => .scanBits)))
        (goto (fun _ => .restoreBits)))
  | .restoreBits => pop 2 (fun _ b => b)
      (branch Option.isSome
        (push 0 (fun b => b.getD false)
          (push 3 (fun b => b.getD false) (goto (fun _ => .restoreBits))))
        (push 3 (fun _ => true) (goto (fun _ => .scanBudget))))
  | .scanBudget => pop 1 (fun _ b => b)
      (branch Option.isSome
        (push 2 (fun b => b.getD false)
          (push 3 (fun _ => false) (push 4 (fun _ => true) (goto (fun _ => .scanBudget)))))
        (goto (fun _ => .restoreBudget)))
  | .restoreBudget => pop 2 (fun _ b => b)
      (branch Option.isSome
        (push 1 (fun b => b.getD false) (goto (fun _ => .restoreBudget)))
        (load (fun _ => none) halt))

abbrev Config := TM2.Cfg (fun _ : Fin 5 => Bool) Label (Option Bool)

def cfg (l : Option Label) (v : Option Bool) (bits budget saved packed cap : List Bool) : Config :=
  ⟨l,v,![bits,budget,saved,packed,cap]⟩

def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

theorem run_add (t u : ℕ) (c : Config) : run (t+u) c = run u (run t c) := by
  simpa only [run,Nat.add_comm] using Function.iterate_add_apply (advance program) u t c

theorem scanBits_cons (v : Option Bool) (b : Bool) (bits budget saved packed cap : List Bool) :
    advance program (cfg (some .scanBits) v (b::bits) budget saved packed cap) =
      cfg (some .scanBits) (some b) bits budget (b::saved) packed cap := by
  simp [advance,program,cfg,TM2.step,TM2.stepAux]
  funext j
  fin_cases j <;> rfl

theorem scanBits_nil (v : Option Bool) (budget saved packed cap : List Bool) :
    advance program (cfg (some .scanBits) v [] budget saved packed cap) =
      cfg (some .restoreBits) none [] budget saved packed cap := by
  simp [advance,program,cfg,TM2.step,TM2.stepAux]

theorem scanBits_run (v : Option Bool) (bits budget saved packed cap : List Bool) :
    run (bits.length+1) (cfg (some .scanBits) v bits budget saved packed cap) =
      cfg (some .restoreBits) none [] budget (bits.reverse++saved) packed cap := by
  induction bits generalizing v saved with
  | nil => simpa only [run,Function.iterate_one,List.length_nil,zero_add,
      List.reverse_nil,List.nil_append] using scanBits_nil v budget saved packed cap
  | cons b bits ih =>
      simp only [List.length_cons,run,Function.iterate_succ_apply,scanBits_cons]
      simpa only [run,List.reverse_cons,List.append_assoc,List.singleton_append]
        using ih (some b) (b::saved)

theorem restoreBits_cons (v : Option Bool) (b : Bool) (bits budget saved packed cap : List Bool) :
    advance program (cfg (some .restoreBits) v bits budget (b::saved) packed cap) =
      cfg (some .restoreBits) (some b) (b::bits) budget saved (b::packed) cap := by
  simp [advance,program,cfg,TM2.step,TM2.stepAux]
  funext j
  fin_cases j <;> rfl

theorem restoreBits_nil (v : Option Bool) (bits budget packed cap : List Bool) :
    advance program (cfg (some .restoreBits) v bits budget [] packed cap) =
      cfg (some .scanBudget) none bits budget [] (true::packed) cap := by
  simp [advance,program,cfg,TM2.step,TM2.stepAux]
  funext j
  fin_cases j <;> rfl

theorem restoreBits_run (v : Option Bool) (bits budget saved packed cap : List Bool) :
    run (saved.length+1) (cfg (some .restoreBits) v bits budget saved packed cap) =
      cfg (some .scanBudget) none (saved.reverse++bits) budget []
        (true::(saved.reverse++packed)) cap := by
  induction saved generalizing v bits packed with
  | nil => simpa only [run,Function.iterate_one,List.length_nil,zero_add,
      List.reverse_nil,List.nil_append] using restoreBits_nil v bits budget packed cap
  | cons b saved ih =>
      simp only [List.length_cons,run,Function.iterate_succ_apply,restoreBits_cons]
      simpa only [run,List.reverse_cons,List.append_assoc,List.singleton_append]
        using ih (some b) (b::bits) (b::packed)

theorem copyBits_run (bits budget packed cap : List Bool) :
    run (2*bits.length+2) (cfg (some .scanBits) none bits budget [] packed cap) =
      cfg (some .scanBudget) none bits budget [] (true::(bits++packed)) cap := by
  have h := scanBits_run none bits budget [] packed cap
  rw [List.append_nil] at h
  rw [show 2*bits.length+2 = (bits.length+1)+(bits.length+1) by omega,run_add,h]
  have hr := restoreBits_run none [] budget bits.reverse packed cap
  simpa only [List.length_reverse,List.reverse_reverse,List.append_nil] using hr

theorem scanBudget_cons (v : Option Bool) (b : Bool) (bits budget saved packed cap : List Bool) :
    advance program (cfg (some .scanBudget) v bits (b::budget) saved packed cap) =
      cfg (some .scanBudget) (some b) bits budget (b::saved) (false::packed) (true::cap) := by
  simp [advance,program,cfg,TM2.step,TM2.stepAux]
  funext j
  fin_cases j <;> rfl

theorem scanBudget_nil (v : Option Bool) (bits saved packed cap : List Bool) :
    advance program (cfg (some .scanBudget) v bits [] saved packed cap) =
      cfg (some .restoreBudget) none bits [] saved packed cap := by
  simp [advance,program,cfg,TM2.step,TM2.stepAux]

theorem scanBudget_run (v : Option Bool) (bits budget saved packed cap : List Bool) :
    run (budget.length+1) (cfg (some .scanBudget) v bits budget saved packed cap) =
      cfg (some .restoreBudget) none bits [] (budget.reverse++saved)
        (List.replicate budget.length false++packed) (List.replicate budget.length true++cap) := by
  induction budget generalizing v saved packed cap with
  | nil => simpa only [run,Function.iterate_one,List.length_nil,zero_add,
      List.reverse_nil,List.nil_append,List.replicate_zero]
        using scanBudget_nil v bits saved packed cap
  | cons b budget ih =>
      simp only [List.length_cons,run,Function.iterate_succ_apply,scanBudget_cons]
      have h := ih (some b) (b::saved) (false::packed) (true::cap)
      simpa only [run,List.reverse_cons,List.append_assoc,List.singleton_append,
        List.replicate_succ',List.cons_append,List.append_assoc,List.singleton_append] using h

theorem restoreBudget_cons (v : Option Bool) (b : Bool) (bits budget saved packed cap : List Bool) :
    advance program (cfg (some .restoreBudget) v bits budget (b::saved) packed cap) =
      cfg (some .restoreBudget) (some b) bits (b::budget) saved packed cap := by
  simp [advance,program,cfg,TM2.step,TM2.stepAux]
  funext j
  fin_cases j <;> rfl

theorem restoreBudget_nil (v : Option Bool) (bits budget packed cap : List Bool) :
    advance program (cfg (some .restoreBudget) v bits budget [] packed cap) =
      cfg none none bits budget [] packed cap := by
  simp [advance,program,cfg,TM2.step,TM2.stepAux]

theorem restoreBudget_run (v : Option Bool) (bits budget saved packed cap : List Bool) :
    run (saved.length+1) (cfg (some .restoreBudget) v bits budget saved packed cap) =
      cfg none none bits (saved.reverse++budget) [] packed cap := by
  induction saved generalizing v budget with
  | nil => simpa only [run,Function.iterate_one,List.length_nil,zero_add,
      List.reverse_nil,List.nil_append] using restoreBudget_nil v bits budget packed cap
  | cons b saved ih =>
      simp only [List.length_cons,run,Function.iterate_succ_apply,restoreBudget_cons]
      simpa only [run,List.reverse_cons,List.append_assoc,List.singleton_append]
        using ih (some b) (b::budget)

theorem budget_run (bits budget packed cap : List Bool) :
    run (2*budget.length+2) (cfg (some .scanBudget) none bits budget [] packed cap) =
      cfg none none bits budget [] (List.replicate budget.length false++packed)
        (List.replicate budget.length true++cap) := by
  have h := scanBudget_run none bits budget [] packed cap
  rw [List.append_nil] at h
  rw [show 2*budget.length+2 = (budget.length+1)+(budget.length+1) by omega,run_add,h]
  have hr := restoreBudget_run none bits [] budget.reverse
    (List.replicate budget.length false++packed) (List.replicate budget.length true++cap)
  simpa only [List.length_reverse,List.reverse_reverse,List.append_nil] using hr

/-- Complete physical preparation. Both source stacks survive unchanged;
the cap and time prefix depend on the budget's length, not its bit values. -/
theorem run_correct (bits budget : List Bool) :
    run (2*bits.length+2*budget.length+4) (cfg (some .scanBits) none bits budget [] [] []) =
      cfg none none bits budget [] (BoundedBitMachine.packed budget.length bits)
        (List.replicate budget.length true) := by
  rw [show 2*bits.length+2*budget.length+4 = (2*bits.length+2)+(2*budget.length+2)
      by omega,run_add,copyBits_run,budget_run]
  simp only [List.append_nil,BoundedBitMachine.packed]

end EthInapproximability.CurrentPaper.CutoffProbePreparation
