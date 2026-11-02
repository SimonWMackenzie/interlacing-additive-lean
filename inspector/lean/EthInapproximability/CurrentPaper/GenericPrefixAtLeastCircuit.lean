import EthInapproximability.CurrentPaper.GenericPrefixGateCycle
import EthInapproximability.CurrentPaper.GenericPrefixUnitCycle
import EthInapproximability.CurrentPaper.SourceClauseCallback

namespace EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.AtLeastCircuit

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceBooleanEncoding SourceClauseEncoding EncodedCNF
open SourceBooleanPrefix SourceGenericPrefix
open scoped Classical

abbrev Stack := PrefixSharedCore.Stack
abbrev Circuit := SourceClauseCallback.Circuit

def gatePayload {n a q : Nat} (v : Fin n) (s : Fin a) : List Bool :=
  clauseFields (orGate
    (SourceGenericPrefix.base n a q v.val + s.val)
    (SourceBooleanEncoding.positive (bitIndex v s)))

def gateFold {n a q : Nat} (v : Fin n) :
    List (Fin a) → List Bool → List Bool
  | [],saved => saved
  | s :: ss,saved => gateFold (q := q) v ss
      ((gatePayload (q := q) v s).reverse ++ saved)

noncomputable def unitCircuit (a w ell : Nat) (sign : Bool) : Circuit Stack :=
  SourceClauseCallback.Circuit.of
    (UnitCycle.program a w ell sign)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (SourceClauseFixedBatch.labelAt
          (UnitStage.constantSize a w ell) 0)))
    (((),PrefixUnitRun.startControl),((),none))

noncomputable def gateCircuit (a s w : Nat) : Circuit Stack :=
  SourceClauseCallback.Circuit.of
    (GateCycle.program a s w)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (SourceClauseFixedBatch.labelAt
            (GateOperands.constantSize a s w) 0))))
    ((((),((),none)),GateCycle.gateControl),((),none))

theorem unit_run (n a ordinal w ell : Nat) (sign : Bool)
    (saved output count : List Bool) :
    SourceClauseCallback.Circuit.Run (unitCircuit a w ell sign)
      (PrefixGateReady.blank n ordinal saved output count)
      (PrefixGateReady.blank n ordinal
        (UnitHandoff.nextSaved n a ordinal w ell sign saved)
        output (true :: count)) := by
  obtain ⟨t,_,h⟩ := UnitCycle.run n a ordinal w ell sign
    saved output count
  exact ⟨t,by simpa only [unitCircuit,SourceClauseCallback.Circuit.of]
    using h⟩

theorem gate_run {n a q : Nat} (v : Fin n) (s : Fin a)
    (saved output count : List Bool) :
    SourceClauseCallback.Circuit.Run
      (gateCircuit a s.val (width a q + 1))
      (PrefixGateReady.blank n v.val saved output count)
      (PrefixGateReady.blank n v.val
        ((gatePayload (q := q) v s).reverse ++ saved)
        output (List.replicate 3 true ++ count)) := by
  obtain ⟨t,_,h⟩ := GateCycle.run (q := q) v s
    saved output count
  refine ⟨t,?_⟩
  simpa only [gateCircuit,SourceClauseCallback.Circuit.of,
    GateHandoff.nextSaved,gatePayload,List.replicate_succ,
    List.replicate_zero,List.nil_append,List.cons_append]
    using h

noncomputable def gateListCircuit (a q : Nat) :
    List (Fin a) → Circuit Stack
  | [] => SourceClauseCallback.Circuit.halt
  | s :: ss => SourceClauseCallback.Circuit.seq
      (gateCircuit a s.val (width a q + 1)) (gateListCircuit a q ss)

theorem gate_list_run {n a q : Nat} (v : Fin n)
    (ss : List (Fin a)) (saved output count : List Bool) :
    SourceClauseCallback.Circuit.Run (gateListCircuit a q ss)
      (PrefixGateReady.blank n v.val saved output count)
      (PrefixGateReady.blank n v.val
        (gateFold (q := q) v ss saved) output
        (List.replicate (3 * ss.length) true ++ count)) := by
  induction ss generalizing saved count with
  | nil =>
      simpa [gateListCircuit,gateFold] using
        (SourceClauseCallback.Circuit.halt_run
          (PrefixGateReady.blank n v.val saved output count))
  | cons s ss ih =>
      have hhead := gate_run (q := q) v s saved output count
      have htail := ih ((gatePayload (q := q) v s).reverse ++ saved)
        (List.replicate 3 true ++ count)
      have hseq := SourceClauseCallback.Circuit.seq_run
        (gateCircuit a s.val (width a q + 1))
        (gateListCircuit a q ss)
        (PrefixGateReady.blank n v.val saved output count)
        (PrefixGateReady.blank n v.val
          ((gatePayload (q := q) v s).reverse ++ saved)
          output (List.replicate 3 true ++ count))
        (PrefixGateReady.blank n v.val
          (gateFold (q := q) v ss
            ((gatePayload (q := q) v s).reverse ++ saved)) output
          (List.replicate (3 * ss.length) true ++
            (List.replicate 3 true ++ count))) hhead htail
      have hnum : List.replicate (3 * (s :: ss).length) true ++ count =
          List.replicate (3 * ss.length) true ++
            (List.replicate 3 true ++ count) := by
        rw [List.length_cons,show 3 * (ss.length + 1) =
          3 * ss.length + 3 by omega,List.replicate_add]
        simp only [List.append_assoc]
      simpa only [gateListCircuit,gateFold,hnum] using hseq

noncomputable def atLeastCircuit (a q : Nat) : Circuit Stack :=
  SourceClauseCallback.Circuit.seq
    (unitCircuit a (width a q + 1) 0 false)
    (SourceClauseCallback.Circuit.seq
      (gateListCircuit a q (List.ofFn (fun s : Fin a => s)))
      (unitCircuit a (width a q + 1) a true))

theorem callback_run {n a q : Nat} (v : Fin n)
    (saved output count : List Bool) :
    let w := width a q + 1
    let opening := UnitHandoff.nextSaved
      n a v.val w 0 false saved
    let middle := gateFold (q := q) v
      (List.ofFn (fun s : Fin a => s)) opening
    SourceClauseCallback.Circuit.Run (atLeastCircuit a q)
      (PrefixGateReady.blank n v.val saved output count)
      (PrefixGateReady.blank n v.val
        (UnitHandoff.nextSaved n a v.val w a true middle)
        output (List.replicate (3*a+2) true ++ count)) := by
  dsimp
  let w := width a q + 1
  let opening := UnitHandoff.nextSaved
    n a v.val w 0 false saved
  let middle := gateFold (q := q) v
    (List.ofFn (fun s : Fin a => s)) opening
  have h₀ := unit_run n a v.val w 0 false saved output count
  have h₁ := gate_list_run (q := q) v
    (List.ofFn (fun s : Fin a => s)) opening output (true :: count)
  have h₂ := unit_run n a v.val w a true middle output
    (List.replicate (3*a) true ++ (true :: count))
  have h₁₂ := SourceClauseCallback.Circuit.seq_run
    (gateListCircuit a q (List.ofFn (fun s : Fin a => s)))
    (unitCircuit a w a true)
    (PrefixGateReady.blank n v.val opening output (true :: count))
    (PrefixGateReady.blank n v.val middle output
      (List.replicate (3*a) true ++ (true :: count)))
    (PrefixGateReady.blank n v.val
      (UnitHandoff.nextSaved n a v.val w a true middle)
      output (true :: (List.replicate (3*a) true ++ (true :: count))))
    (by simpa only [List.length_ofFn] using h₁) h₂
  have h₀₁₂ := SourceClauseCallback.Circuit.seq_run
    (unitCircuit a w 0 false)
    (SourceClauseCallback.Circuit.seq
      (gateListCircuit a q (List.ofFn (fun s : Fin a => s)))
      (unitCircuit a w a true))
    (PrefixGateReady.blank n v.val saved output count)
    (PrefixGateReady.blank n v.val opening output (true :: count))
    (PrefixGateReady.blank n v.val
      (UnitHandoff.nextSaved n a v.val w a true middle)
      output (true :: (List.replicate (3*a) true ++ (true :: count))))
    h₀ h₁₂
  have hnum : true :: (List.replicate (3*a) true ++ (true :: count)) =
      List.replicate (3*a+2) true ++ count := by
    rw [show 3*a+2 = 1+(3*a+1) by omega,List.replicate_add,
      show 3*a+1 = 3*a+1 by rfl,List.replicate_add]
    simp [List.append_assoc]
  simpa only [atLeastCircuit,w,opening,middle,hnum]
    using h₀₁₂

#print axioms gate_list_run
#print axioms callback_run

end EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.AtLeastCircuit
