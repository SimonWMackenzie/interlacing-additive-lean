import EthInapproximability.CurrentPaper.GenericPrefixAtLeastSource
import EthInapproximability.CurrentPaper.SourceClauseCircuitClock

namespace EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.AtLeastClock

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceBooleanEncoding SourceClauseEncoding EncodedCNF
open SourceBooleanPrefix SourceGenericPrefix AtLeastCircuit
open scoped Classical

abbrev BoundedRun := @SourceClauseCallback.Circuit.BoundedRun
  AtLeastCircuit.Stack

noncomputable def gateCost {n a q : Nat} (v : Fin n) (s : Fin a)
    (saved output count : List Bool) : Nat :=
  GateOperands.cost a s.val (width a q + 1)
      (List.replicate v.val true) +
    SourceClauseRowGate.cost v.val a s.val n s.val v.val
      (width a q + 1) true + 1 +
    PrefixSharedClear.cost
      (bank PrefixSharedCore.gateEmbedding
        (GateReady.prepared v s (width a q + 1) saved output count)
        (SourceClauseRowGate.finalBank (0 : Fin 1) (vertexFrame v)
          v.val a s.val n s.val v.val (width a q + 1) true
          saved output count)) + 1

theorem gate_bounded {n a q : Nat} (v : Fin n) (s : Fin a)
    (saved output count : List Bool) :
    BoundedRun (gateCircuit a s.val (width a q + 1))
      (gateCost (q := q) v s saved output count)
      (PrefixGateReady.blank n v.val saved output count)
      (PrefixGateReady.blank n v.val
        ((gatePayload (q := q) v s).reverse ++ saved)
        output (List.replicate 3 true ++ count)) := by
  obtain ⟨t,ht,h⟩ := GateCycle.run (q := q) v s
    saved output count
  refine ⟨t,ht,?_⟩
  simpa only [gateCircuit,SourceClauseCallback.Circuit.of,
    GateHandoff.nextSaved,gatePayload,List.replicate_succ,
    List.replicate_zero,List.nil_append,List.cons_append]
    using h

theorem unit_bounded (n a ordinal w ell : Nat) (sign : Bool)
    (saved output count : List Bool) :
    BoundedRun (unitCircuit a w ell sign)
      (UnitCycle.cost n a ordinal w ell sign saved output count)
      (PrefixGateReady.blank n ordinal saved output count)
      (PrefixGateReady.blank n ordinal
        (UnitHandoff.nextSaved n a ordinal w ell sign saved)
        output (true :: count)) := by
  obtain ⟨t,ht,h⟩ := UnitCycle.run n a ordinal w ell sign
    saved output count
  exact ⟨t,ht,by simpa only [unitCircuit,
    SourceClauseCallback.Circuit.of] using h⟩

noncomputable def gateListCost {n a q : Nat} (v : Fin n) :
    List (Fin a) → List Bool → List Bool → List Bool → Nat
  | [],_,_,_ => 1
  | s :: ss,saved,output,count =>
      gateCost (q := q) v s saved output count +
        gateListCost (q := q) v ss
          ((gatePayload (q := q) v s).reverse ++ saved)
          output (List.replicate 3 true ++ count) + 1

theorem gate_list_bounded {n a q : Nat} (v : Fin n)
    (ss : List (Fin a)) (saved output count : List Bool) :
    BoundedRun (gateListCircuit a q ss)
      (gateListCost (q := q) v ss saved output count)
      (PrefixGateReady.blank n v.val saved output count)
      (PrefixGateReady.blank n v.val
        (gateFold (q := q) v ss saved) output
        (List.replicate (3*ss.length) true ++ count)) := by
  induction ss generalizing saved count with
  | nil =>
      simpa [gateListCircuit,gateListCost,gateFold] using
        (SourceClauseCallback.Circuit.halt_bounded_run
          (PrefixGateReady.blank n v.val saved output count))
  | cons s ss ih =>
      have hhead := gate_bounded (q := q) v s saved output count
      have htail := ih ((gatePayload (q := q) v s).reverse ++ saved)
        (List.replicate 3 true ++ count)
      have hseq := SourceClauseCallback.Circuit.seq_bounded_run
        (gateCircuit a s.val (width a q + 1))
        (gateListCircuit a q ss)
        (PrefixGateReady.blank n v.val saved output count)
        (PrefixGateReady.blank n v.val
          ((gatePayload (q := q) v s).reverse ++ saved)
          output (List.replicate 3 true ++ count))
        (PrefixGateReady.blank n v.val
          (gateFold (q := q) v ss
            ((gatePayload (q := q) v s).reverse ++ saved)) output
          (List.replicate (3*ss.length) true ++
            (List.replicate 3 true ++ count)))
        (gateCost (q := q) v s saved output count)
        (gateListCost (q := q) v ss
          ((gatePayload (q := q) v s).reverse ++ saved)
          output (List.replicate 3 true ++ count)) hhead htail
      have hnum : List.replicate (3*(s::ss).length) true ++ count =
          List.replicate (3*ss.length) true ++
            (List.replicate 3 true ++ count) := by
        rw [List.length_cons,show 3*(ss.length+1)=3*ss.length+3 by omega,
          List.replicate_add]
        simp only [List.append_assoc]
      simpa only [gateListCircuit,gateListCost,gateFold,hnum] using hseq

noncomputable def cost {n a q : Nat} (v : Fin n)
    (saved output count : List Bool) : Nat :=
  let w := width a q + 1
  let opening := UnitHandoff.nextSaved n a v.val w 0 false saved
  let middle := gateFold (q := q) v
    (List.ofFn (fun s : Fin a => s)) opening
  UnitCycle.cost n a v.val w 0 false saved output count +
    (gateListCost (q := q) v
      (List.ofFn (fun s : Fin a => s)) opening output
      (true :: count) +
      UnitCycle.cost n a v.val w a true middle output
        (List.replicate (3*a) true ++ (true :: count)) + 1) + 1

theorem source_bounded {n a q : Nat} (v : Fin n)
    (saved output count : List Bool) :
    BoundedRun (atLeastCircuit a q)
      (cost (a := a) (q := q) v saved output count)
      (PrefixGateReady.blank n v.val saved output count)
      (PrefixGateReady.blank n v.val
        ((clauseFields (chain
          (SourceGenericPrefix.base n a q v.val)
          (SourceGenericPrefix.atLeastPayload (a := a) v))).reverse ++
          saved)
        output (List.replicate (3*a+2) true ++ count)) := by
  let w := width a q + 1
  let opening := UnitHandoff.nextSaved n a v.val w 0 false saved
  let middle := gateFold (q := q) v
    (List.ofFn (fun s : Fin a => s)) opening
  have h₀ := unit_bounded n a v.val w 0 false saved output count
  have h₁ := gate_list_bounded (q := q) v
    (List.ofFn (fun s : Fin a => s)) opening output (true :: count)
  have h₂ := unit_bounded n a v.val w a true middle output
    (List.replicate (3*a) true ++ (true :: count))
  have h₁₂ := SourceClauseCallback.Circuit.seq_bounded_run
    (gateListCircuit a q (List.ofFn (fun s : Fin a => s)))
    (unitCircuit a w a true)
    (PrefixGateReady.blank n v.val opening output (true :: count))
    (PrefixGateReady.blank n v.val middle output
      (List.replicate (3*a) true ++ (true :: count)))
    (PrefixGateReady.blank n v.val
      (UnitHandoff.nextSaved n a v.val w a true middle)
      output (true :: (List.replicate (3*a) true ++ (true :: count))))
    (gateListCost (q := q) v
      (List.ofFn (fun s : Fin a => s)) opening output (true :: count))
    (UnitCycle.cost n a v.val w a true middle output
      (List.replicate (3*a) true ++ (true :: count)))
    (by simpa only [List.length_ofFn] using h₁) h₂
  have h₀₁₂ := SourceClauseCallback.Circuit.seq_bounded_run
    (unitCircuit a w 0 false)
    (SourceClauseCallback.Circuit.seq
      (gateListCircuit a q (List.ofFn (fun s : Fin a => s)))
      (unitCircuit a w a true))
    (PrefixGateReady.blank n v.val saved output count)
    (PrefixGateReady.blank n v.val opening output (true :: count))
    (PrefixGateReady.blank n v.val
      (UnitHandoff.nextSaved n a v.val w a true middle)
      output (true :: (List.replicate (3*a) true ++ (true :: count))))
    (UnitCycle.cost n a v.val w 0 false saved output count)
    (gateListCost (q := q) v
      (List.ofFn (fun s : Fin a => s)) opening output (true :: count) +
      UnitCycle.cost n a v.val w a true middle output
        (List.replicate (3*a) true ++ (true :: count)) + 1)
    h₀ h₁₂
  have hnum : true :: (List.replicate (3*a) true ++ (true :: count)) =
      List.replicate (3*a+2) true ++ count := by
    rw [show 3*a+2=1+(3*a+1) by omega,List.replicate_add,
      List.replicate_add]
    simp [List.append_assoc]
  have hsource := AtLeastSource.saved_eq_source (a := a) (q := q) v saved
  dsimp at hsource
  simpa only [atLeastCircuit,cost,w,opening,middle,hnum,hsource]
    using h₀₁₂

#print axioms source_bounded

end EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.AtLeastClock
