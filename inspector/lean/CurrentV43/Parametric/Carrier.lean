import CurrentV43.Parametric.Source
import CurrentAdditive.DynamicGetterPrimitives
import CurrentAdditive.CodeDFixedWordProducer

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 32768
namespace CurrentV43.ParametricSource
noncomputable section
open Paper2 Turing EthInapproximability.CurrentPaper CurrentAdditive
open PhysicalConcat

/-- Literal composition with its complete transfer clock. -/
def compose (A B : Producer) : Producer where
  machine := BitMachineComposition.composition A.machine B.machine
  result := fun x => B.result (A.result x)
  clock := fun x => A.clock x+2*(A.result x).length+2+B.clock (A.result x)
  outputs x := BitMachineComposition.composition_outputsWithin _ _ (A.outputs x) (B.outputs _)

/-- Literal same-input concatenation, including copying and serialization. -/
def append (A B : Producer) : Producer where
  machine := PhysicalConcat.machine (A:=A) (B:=B)
  result := fun x => A.result x++B.result x
  clock := PhysicalConcat.clock (A:=A) (B:=B)
  outputs := PhysicalConcat.outputs

def identity : Producer where
  machine := BitMachineCopy.bitMachine
  result := id
  clock := fun x => 2*x.length+2
  outputs := BitMachineCopy.bitMachine_outputs

def pair (A B : Producer) : Producer :=
  append (compose A (PhysicalProducer.localProducer PhysicalProducer.field)) B

theorem pair_result (A B : Producer) (x : List Bool) :
    (pair A B).result x=EncodedComplexity.pair (A.result x) (B.result x) := rfl

/-- The resource printer is genuinely run; its output length, together
with the retained input, requests the two random blocks. -/
def inner (R : Producer) := pair identity R

def blockLength (R : Producer) (w : List Bool) := ((inner R).result w).length+1

def carrierLength (R : Producer) (w : List Bool) := 2*blockLength R w

/-- The carrier length is printed by a fixed actual finite machine. -/
def carrierProducer (R : Producer) : Producer :=
  let L := compose (inner R) (PhysicalProducer.localProducer DynamicGetterPrimitives.literalLength)
  append (append L L) (PhysicalProducer.localProducer (CodeDFixedWordProducer.producer [true,true]))

theorem carrier_result (R : Producer) (w : List Bool) :
    (carrierProducer R).result w=List.replicate (carrierLength R w) true := by
  change List.replicate (((inner R).result w).length) true ++
    List.replicate (((inner R).result w).length) true ++ [true,true] = _
  rw [←List.replicate_add]
  change List.replicate (((inner R).result w).length+((inner R).result w).length) true ++
    List.replicate 2 true = _
  rw [←List.replicate_add]
  congr 1
  unfold carrierLength blockLength
  omega

theorem carrier_outputs (R : Producer) (w : List Bool) :
    (carrierProducer R).machine.OutputsWithin w
      (List.replicate (carrierLength R w) true) ((carrierProducer R).clock w) := by
  rw [←carrier_result R w]
  exact (carrierProducer R).outputs w

theorem resource_le_block (R : Producer) (w : List Bool) :
    (R.result w).length ≤ blockLength R w := by
  unfold blockLength inner
  rw [pair_result,EncodedComplexity.pair_length]
  change (R.result w).length ≤ 2*w.length+1+(R.result w).length+1
  omega

/-- Generic two-block cut: the inner resource printer is fixed before
any source input or tape, and no tape length is inferred semantically. -/
def cutter (R : Producer) : BitMachine.Machine :=
  BitMachineComposition.composition (AEth2.Cut.machine (inner R).machine 2 1)
    (SelectedTape.Bind.Retain.machine SelectedTape.Bind.idMachine 1 1)

def cutWord (R : Producer) (w tape : List Bool) :=
  EncodedComplexity.pair (EncodedComplexity.pair ((inner R).result w)
    (tape.take (blockLength R w))) ((tape.take (carrierLength R w)).drop (blockLength R w))

def cutClock (R : Producer) (w : List Bool) :=
  let mid := 2*((inner R).result w).length+1+carrierLength R w
  AEth2.Cut.cutTimeG 2 1 (inner R).machine.pushBound w.length ((inner R).clock w)+
    2*mid+2+SelectedTape.Bind.Retain.timeBound 1 1 SelectedTape.Bind.idC
      SelectedTape.Bind.idD SelectedTape.Bind.idMachine.pushBound mid

theorem cutter_outputs (R : Producer) (w tape : List Bool) :
    (cutter R).OutputsWithin (EncodedComplexity.pair w tape)
      (cutWord R w tape) (cutClock R w) := by
  have h1 := AEth2.Cut.cut_outputs_gen (inner R).machine 2 1
    (inner R).result (inner R).clock w ((inner R).outputs w) tape
  have hL : 2*(((inner R).result w).length+1)^1=carrierLength R w := by
    simp [carrierLength,blockLength]
  rw [hL] at h1
  let P := tape.take (carrierLength R w)
  have h2 := SelectedTape.Bind.Retain.machine_outputs SelectedTape.Bind.idMachine 1 1
    id SelectedTape.Bind.idC SelectedTape.Bind.idD SelectedTape.Bind.idRuns
    (EncodedComplexity.pair ((inner R).result w) P)
  rw [SelectedTape.Bind.Retain.result_pair] at h2
  have hL2 : 1*(((inner R).result w).length+1)^1=blockLength R w := by
    simp [blockLength]
  simp only [id] at h2
  rw [hL2] at h2
  have he : P.take (blockLength R w)=tape.take (blockLength R w) := by
    dsimp [P]
    rw [List.take_take,Nat.min_eq_left]
    unfold carrierLength
    omega
  rw [he] at h2
  have hm : (EncodedComplexity.pair ((inner R).result w) P).length ≤
      2*((inner R).result w).length+1+carrierLength R w := by
    rw [EncodedComplexity.pair_length]
    have := List.length_take_le (carrierLength R w) tape
    dsimp [P]
    omega
  have h2' := BitMachine.outputsWithin_mono _ h2 (AEth5.retain_timeBound_mono _ _ _ hm)
  have h := BitMachineComposition.composition_outputsWithin _ _ h1 h2'
  apply BitMachine.outputsWithin_mono _ h
  dsimp only [cutClock]
  dsimp only [P] at *
  have := List.length_take_le (carrierLength R w) tape
  rw [EncodedComplexity.pair_length]
  omega

/-- Remove only the paid resource word, preserving both physical random
blocks.  This is an execution theorem for every raw input and raw tape. -/
def splitMachine (R : Producer) := BitMachineComposition.composition (cutter R)
  (Unit4Shell.PairMap.machine (Unit4Shell.PairMap.machine AEth3.Fst.machine))

def splitWord (R : Producer) (w tape : List Bool) :=
  EncodedComplexity.pair (EncodedComplexity.pair w (tape.take (blockLength R w)))
    ((tape.take (carrierLength R w)).drop (blockLength R w))

def splitClock (R : Producer) (w : List Bool) :=
  let L := blockLength R w
  let I := ((inner R).result w).length
  cutClock R w+2*(2*(2*I+1+L)+1+2*L)+2+
    (2*(2*I+1+L)+(2*I+(2*w.length+3)+2*w.length+6)+2*(2*w.length+1+L)+6)

theorem split_outputs (R : Producer) (w tape : List Bool) :
    (splitMachine R).OutputsWithin (EncodedComplexity.pair w tape)
      (splitWord R w tape) (splitClock R w) := by
  have hf := AEth3.Fst.machine_outputs w (R.result w)
  have h1 := Unit4Shell.PairMap.machine_outputs AEth3.Fst.machine ((inner R).result w) w
    (tape.take (blockLength R w)) _ hf
  have h2 := Unit4Shell.PairMap.machine_outputs (Unit4Shell.PairMap.machine AEth3.Fst.machine)
    _ _ ((tape.take (carrierLength R w)).drop (blockLength R w)) _ h1
  have h := BitMachineComposition.composition_outputsWithin _ _ (cutter_outputs R w tape) h2
  apply BitMachine.outputsWithin_mono _ h
  have ht := List.length_take_le (blockLength R w) tape
  have hc := List.length_take_le (carrierLength R w) tape
  dsimp only [cutWord,splitClock,carrierLength] at *
  simp only [EncodedComplexity.pair_length,List.length_drop]
  omega

/-- Exact independence for the very two blocks delivered by splitMachine. -/
theorem split_law (R : Producer) (w : List Bool) (I s : Nat)
    (hI : I≤blockLength R w) (hs : s≤blockLength R w)
    (event : List Bool→List Bool→Prop) :
    (Unit4Shell.Definitions.uniformTape (carrierLength R w)).prob
      (fun t => event (((List.ofFn t).take (blockLength R w)).take I)
        ((((List.ofFn t).take (carrierLength R w)).drop (blockLength R w)).take s)) =
    ((Unit4Shell.Definitions.uniformTape I).prod (Unit4Shell.Definitions.uniformTape s)).prob
      (fun x => event (List.ofFn x.1) (List.ofFn x.2)) := by
  apply AEth5.blocks_law (j:=1) hI
  · simpa only [pow_one] using (show blockLength R w+s≤2*blockLength R w by omega)
  · exact le_rfl

#print axioms carrier_outputs
#print axioms cutter_outputs
#print axioms split_outputs
#print axioms split_law
end
end CurrentV43.ParametricSource


