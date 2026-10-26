import EthInapproximability.CurrentPaper.SourceListMachineItemPrefix
import EthInapproximability.CurrentPaper.SourceListMachineItemClear

namespace EthInapproximability.CurrentPaper.SourceListMachineItem

open Turing TM2.Stmt BitMachine BitMachineEncoding
open scoped BigOperators
open SourceListMachineFields hiding cfg run run_add program outer

variable (M : Machine)

def ready (source accumulator : List Bool) : Config M :=
  cfg M (some (fieldLabel M (.inl .scan))) (fieldControl M SourceListMachineFields.initialControl)
    (fun _ => []) (foreign source [] [] [] accumulator)

def success (source accumulator : List Bool) : Config M :=
  cfg M none ((SourceListMachineFields.initialControl,M.initial),some true)
    (fun _ => []) (foreign source [] [] [] accumulator)

/-- A complete actual one-item run. The large unread suffix and preceding
output accumulator do not occur in its runtime bound. -/
theorem item_encoded (input output source accumulator : List Bool) (bound : Nat)
    (hM : M.OutputsWithin input output bound) :
    ∃ t ≤ 20*(input.length+1)*(input.length.bits.length+1) +
        bound + 4*input.length + output.length +
        M.stackCount*(input.length+bound*M.pushBound+1)+9,
      run M t (ready M (EncodedCommunication.natField input.length ++ (input++source)) accumulator) =
        success M source (output.reverse++accumulator) := by
  obtain ⟨a,ha,he⟩ := field_encoded M input source accumulator
  have hs := afterField_good M source (List.replicate input.length true) input accumulator
  have hprepare := prepare_run M source (List.replicate input.length true) input accumulator
    (fieldControl M (SourceListMachineFields.coreControl (some true,false)))
  obtain ⟨b,hb,c,hhalt,hout,hcall,hsize⟩ := component_run M input output source
    (List.replicate input.length true) accumulator bound hM
  have hmove := moveOutput_run M source (List.replicate input.length true) output accumulator
    (localControl M c.var) c.stk hout
  have hclear := clear_run M (localControl M c.var).1 (Function.update c.stk M.output [])
    source (List.replicate input.length true) (output.reverse++accumulator)
  have hcount := clearCount_run M source (List.replicate input.length true)
    (output.reverse++accumulator) (SourceListMachineFields.initialControl,M.initial)
  have r1 := (run_add M he 1).trans (run_step M hs 0)
  have r2 := (run_add M r1 _).trans hprepare
  have r3 := (run_add M r2 _).trans hcall
  have r4 := (run_add M r3 _).trans hmove
  have r5 := (run_add M r4 _).trans hclear
  have r6 := (run_add M r5 _).trans hcount
  refine ⟨_,?_,r6⟩
  have hsum : (∑ k : Fin M.stackCount, ((Function.update c.stk M.output []) k).length) ≤
      M.stackCount*(input.length+bound*M.pushBound) := by
    calc
      _ ≤ ∑ _k : Fin M.stackCount, (input.length+bound*M.pushBound) := by
        apply Finset.sum_le_sum
        intro k _
        by_cases hk : k = M.output
        · subst k; simp
        · simpa only [Function.update_of_ne hk] using hsize k
      _ = _ := by simp
  simp only [List.length_replicate] at *
  nlinarith

end EthInapproximability.CurrentPaper.SourceListMachineItem
