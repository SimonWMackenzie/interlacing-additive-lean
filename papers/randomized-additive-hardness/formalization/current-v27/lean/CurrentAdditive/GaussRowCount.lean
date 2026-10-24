import CurrentAdditive.GaussHeaderStrip
import EthInapproximability.CurrentPaper.SourceListMachineOuterRun
import EthInapproximability.CurrentPaper.BitMachineComposition
import EthInapproximability.CurrentPaper.SourceListMachineSemantics
import EthInapproximability.CurrentPaper.UnaryBinaryEncoding

/-! A physical row-count producer for a canonically encoded matrix list.  The
outer loop consumes each row word and emits one unary bit; the final stage
removes the list header.  No numerical row count is supplied to the machine. -/

namespace CurrentAdditive.GaussRowCount

open Turing TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.EncodedCommunication

def oneProgram : Unit → TM2.Stmt (fun _ : Fin 2 => Bool) Unit Unit
  | () => push 1 (fun _ => true) halt

noncomputable def oneMachine : BitMachine.Machine :=
  ofFinite (0 : Fin 2) 1 () () oneProgram

theorem one_outputs (input : List Bool) :
    oneMachine.OutputsWithin input [true] 1 := by
  apply outputsWithin_of_raw_run (0 : Fin 2) 1 () () oneProgram
    input [true] 1 1 (by omega)
  · rfl
  · rfl

def oneResult (_ : List Bool) : List Bool := [true]
def oneClock (_ : List Bool) : Nat := 1

theorem joined_ones (rows : List (List Bool)) :
    SourceListMachineOuter.joined rows oneResult =
      List.replicate rows.length true := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simpa [SourceListMachineOuter.joined_cons, oneResult, ih,
        List.replicate_succ]

noncomputable def machine : BitMachine.Machine :=
  BitMachineComposition.composition
    (SourceListMachineOuter.machine oneMachine)
    GaussHeaderStrip.machine

theorem outer_outputs (rows : List (List Bool)) :
    (SourceListMachineOuter.machine oneMachine).OutputsWithin
      (SourceListEncoding.encode rows)
      (natField rows.length ++ List.replicate rows.length true)
      (SourceListMachineOuter.canonicalBound oneMachine rows oneResult oneClock) := by
  have h := SourceListMachineOuter.canonical_outputsWithin
    oneMachine rows oneResult oneClock
    (by intro x hx; exact one_outputs x)
  simpa only [joined_ones] using h

theorem outputs (rows : List (List Bool)) :
    machine.OutputsWithin (SourceListEncoding.encode rows)
      (List.replicate rows.length true)
      (SourceListMachineOuter.canonicalBound oneMachine rows oneResult oneClock +
       2 * (natField rows.length ++ List.replicate rows.length true).length + 2 +
       (2 * (natField rows.length ++ List.replicate rows.length true).length + 3)) := by
  have hs := GaussHeaderStrip.outputs_valid rows.length
    (List.replicate rows.length true)
  exact BitMachineComposition.composition_outputsWithin
    (SourceListMachineOuter.machine oneMachine) GaussHeaderStrip.machine
    (outer_outputs rows) hs

noncomputable def itemEnvelope (N : Nat) : Nat :=
  20 * (N + 1) * (N + 1) + 1 + 4 * N + 1 +
    oneMachine.stackCount * (N + oneMachine.pushBound + 1) + 9

noncomputable def polynomialClock (N : Nat) : Nat :=
  N * (itemEnvelope N + 4 * N + 8) + 11 * N + 17 +
    2 * (3 * N + 1) + 2 + (2 * (3 * N + 1) + 3)

theorem polynomialClock_mono {a b : Nat} (hab : a ≤ b) :
    polynomialClock a ≤ polynomialClock b := by
  unfold polynomialClock itemEnvelope
  gcongr

theorem rows_le_input (rows : List (List Bool)) :
    rows.length ≤ (SourceListEncoding.encode rows).length := by
  have h := SourceListMachineSemantics.count_le_fields_length rows
  simp only [SourceListEncoding.encode, List.length_append]
  omega

theorem item_le_input (rows : List (List Bool)) (x : List Bool)
    (hx : x ∈ rows) :
    x.length ≤ (SourceListEncoding.encode rows).length := by
  have h : x.length ≤ (SourceListEncoding.fields rows).length := by
    induction rows with
    | nil => simp at hx
    | cons y ys ih =>
        rcases List.mem_cons.mp hx with rfl | hy
        · simp only [SourceListEncoding.fields, List.length_append]
          omega
        · have ht := ih hy
          simp only [SourceListEncoding.fields, List.length_append]
          omega
  simp [SourceListEncoding.encode]
  omega

theorem outer_clock_le (rows : List (List Bool)) :
    SourceListMachineOuter.canonicalBound oneMachine rows oneResult oneClock ≤
      let N := (SourceListEncoding.encode rows).length
      N * (itemEnvelope N + 4 * N + 8) + 11 * N + 17 := by
  let N := (SourceListEncoding.encode rows).length
  have hc : rows.length ≤ N := rows_le_input rows
  have hd : rows.length.bits.length ≤ N :=
    (UnaryBinaryEncoding.bits_length_le rows.length).trans hc
  have hi : ∀ x ∈ rows,
      SourceListMachineWork.itemCost oneMachine x (oneResult x) (oneClock x) ≤
        itemEnvelope N := by
    intro x hx
    exact SourceListMachineWork.itemCost_le_envelope oneMachine x
      (oneResult x) (oneClock x) N 1 1 (item_le_input rows x hx)
      (by rfl) (by rfl)
  have ho : ∀ x ∈ rows, (oneResult x).length ≤ 1 := by
    intro x hx; rfl
  have h := SourceListMachineOuter.canonicalBound_le_source
    oneMachine rows oneResult oneClock N
    (fun _ => N) (fun _ => N) itemEnvelope (fun _ => 1)
    hc hd hi ho
  simpa only [Nat.add_assoc] using h

theorem outputs_polynomial (rows : List (List Bool)) :
    machine.OutputsWithin (SourceListEncoding.encode rows)
      (List.replicate rows.length true)
      (polynomialClock (SourceListEncoding.encode rows).length) := by
  let N := (SourceListEncoding.encode rows).length
  have h := outputs rows
  have houter := outer_clock_le rows
  have hm : rows.length ≤ N := rows_le_input rows
  have hfield := EncodedGraph.natField_length_upper rows.length
  have hlen : (natField rows.length ++ List.replicate rows.length true).length ≤
      3 * N + 1 := by
    simp only [List.length_append, List.length_replicate]
    omega
  apply BitMachine.outputsWithin_mono _ h
  unfold polynomialClock
  dsimp only [N] at *
  omega

#print axioms outputs
#print axioms outputs_polynomial

end CurrentAdditive.GaussRowCount
