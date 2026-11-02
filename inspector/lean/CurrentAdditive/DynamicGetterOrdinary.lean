import CurrentAdditive.DynamicGetterBounded
import CurrentAdditive.DynamicGetterPrepared

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace CurrentAdditive.DynamicGetterOrdinary
open EthInapproximability.CurrentPaper PhysicalProducer
open IndexedExecutableStepRecovery GaussListContext
noncomputable section

def composeCoefficient (M : BitMachine.Machine) (a b e : Nat) :=
  a+2*(a*M.pushBound+1)+b*(a*M.pushBound+1)^e
def composeDegree (d e : Nat) := (d+1)*(e+1)
theorem compose_outputs (M N : BitMachine.Machine) (x y z : List Bool)
    (a d b e : Nat)
    (hM : M.OutputsWithin x y (a*(x.length+1)^d))
    (hN : N.OutputsWithin y z (b*(y.length+1)^e)) :
    (BitMachineComposition.composition M N).OutputsWithin x z
      (composeCoefficient M a b e*(x.length+1)^composeDegree d e) := by
  apply BitMachine.outputsWithin_mono _
    (BitMachineComposition.composition_outputsWithin M N hM hN)
  exact BitMachineCompositionArithmetic.composition_time_bound x.length a d b e
    M.pushBound y.length (BitMachine.output_length_bound M hM)

def bankFields : List Producer → Producer
  | [] => DynamicGetterPrimitives.empty
  | A :: rest => concat (compose A field) (bankFields rest)
theorem bankFields_result (As : List Producer) (x : List Bool) :
    (bankFields As).result x = As.flatMap (fun A => EncodedCommunication.field (A.result x)) := by
  induction As with
  | nil => rfl
  | cons A As ih =>
    change EncodedCommunication.field (A.result x) ++ (bankFields As).result x = _
    rw [ih]; rfl

def request := bankFields [projection (1 : Fin 2),
  DynamicGetterPrimitives.literalLength,DynamicGetterPrimitives.empty,
  DynamicGetterPrimitives.empty]
def indexBits (x : List Bool) := BankFieldProjection.result (1 : Fin 2) x
def budget (x : List Bool) := List.replicate x.length true
theorem request_result (x : List Bool) : request.result x =
    DynamicGetterBounded.packet (indexBits x) (budget x) := by
  rw [show request = bankFields _ from rfl,bankFields_result]
  simp [DynamicGetterBounded.packet,BitMachineBankCodec.encode_eq_list,
    PhysicalProducer.projection,DynamicGetterPrimitives.literalLength,
    DynamicGetterPrimitives.empty,indexBits,budget]

def flag : Producer where
  machine := BitMachineComposition.composition request.machine DynamicGetterBounded.machine
  result := fun x => ProtocolBoundedUnary.result (indexBits x) (budget x) []
  coefficient := composeCoefficient request.machine request.coefficient 500 2
  degree := composeDegree request.degree 2
  outputs x := by
    have h := request.outputs x
    rw [request_result] at h
    exact compose_outputs _ _ _ _ _ _ _ _ _ h (DynamicGetterBounded.outputs _ _)

def unaryIndex := compose flag DynamicGetterPrimitives.tail
def source := projection (0 : Fin 2)
def prep := bankFields [DynamicGetterPrimitives.empty,DynamicGetterPrimitives.empty,
  DynamicGetterPrimitives.empty,DynamicGetterPrimitives.empty,DynamicGetterPrimitives.empty,
  DynamicGetterPrimitives.empty,DynamicGetterPrimitives.empty,unaryIndex,source,
  DynamicGetterPrimitives.empty]

def packet (xs : List (List Bool)) (bits : List Bool) :=
  BitMachineBankCodec.encode (![SourceListEncoding.encode xs,bits] : Fin 2 → List Bool)

theorem cap_fits (xs : List (List Bool)) (bits : List Bool)
    (hi : EncodedCommunication.bitsValue bits < xs.length) :
    EncodedCommunication.bitsValue bits ≤ (packet xs bits).length := by
  have hc := IndexedV2Clock.fields_length_ge_count xs
  have he : xs.length ≤ (SourceListEncoding.encode xs).length := by
    simp only [SourceListEncoding.encode,List.length_append]; omega
  rw [packet,BitMachineBankCodec.encode_length]
  simp [Fin.sum_univ_succ]
  omega

theorem unaryIndex_packet (xs : List (List Bool)) (bits : List Bool)
    (hi : EncodedCommunication.bitsValue bits < xs.length) :
    unaryIndex.result (packet xs bits) =
      List.replicate (EncodedCommunication.bitsValue bits) true := by
  have hcap := cap_fits xs bits hi
  change (ProtocolBoundedUnary.result (indexBits (packet xs bits))
    (budget (packet xs bits)) []).tail = _
  have hidx : indexBits (packet xs bits) = bits :=
    BankFieldProjection.result_encode (1 : Fin 2) _
  rw [hidx]
  simp only [ProtocolBoundedUnary.result,budget,List.length_replicate,
    Nat.min_eq_left hcap,List.append_nil,List.tail_cons]

theorem prep_packet (xs : List (List Bool)) (bits : List Bool)
    (hi : EncodedCommunication.bitsValue bits < xs.length) :
    prep.result (packet xs bits) = codeDGetterPacket (SourceListEncoding.encode xs)
      (EncodedCommunication.bitsValue bits) := by
  rw [show prep = bankFields _ from rfl,bankFields_result]
  simp only [List.flatMap_cons,List.flatMap_nil,DynamicGetterPrimitives.empty,
    unaryIndex_packet xs bits hi]
  have hs : source.result (packet xs bits) = SourceListEncoding.encode xs := by
    exact BankFieldProjection.result_encode (0 : Fin 2) _
  rw [hs]
  simp [codeDGetterPacket,PreservingV2Program.initialBank,BitMachineBankCodec.encode_eq_list]

def machine := BitMachineComposition.composition prep.machine codeDSelectedRecordMachine

/-- One fixed ordinary-input machine selects an arbitrary ordered word from its
V2 list serialization. The binary index may have harmless zero padding. -/
theorem uniform_bits : ∃ c d : Nat, ∀ xs : List (List Bool), ∀ bits : List Bool,
    ∀ hi : EncodedCommunication.bitsValue bits < xs.length,
    machine.OutputsWithin (packet xs bits) xs[EncodedCommunication.bitsValue bits]
      (c*((packet xs bits).length+1)^d) := by
  refine ⟨composeCoefficient prep.machine prep.coefficient 5000 3,
    composeDegree prep.degree 3,fun xs bits hi => ?_⟩
  let i := EncodedCommunication.bitsValue bits
  have hsplit : xs.take i ++ xs[i] :: xs.drop (i+1) = xs := by
    rw [← List.drop_eq_getElem_cons hi,List.take_append_drop]
  have hlen : (xs.take i).length = i := by
    rw [List.length_take]
    exact Nat.min_eq_left (Nat.le_of_lt hi)
  have hg := DynamicGetterPrepared.outputs (xs.take i) xs[i] (xs.drop (i+1))
  simp only [hsplit,hlen] at hg
  have hp := prep.outputs (packet xs bits)
  rw [prep_packet xs bits hi] at hp
  exact compose_outputs _ _ _ _ _ _ _ _ _ hp hg

theorem uniform : ∃ c d : Nat, ∀ xs : List (List Bool), ∀ n : Nat, ∀ hn : n < xs.length,
    machine.OutputsWithin (packet xs n.bits) xs[n]
      (c*((packet xs n.bits).length+1)^d) := by
  obtain ⟨c,d,h⟩ := uniform_bits
  refine ⟨c,d,fun xs n hn => ?_⟩
  simpa only [EncodedCommunication.bitsValue_bits] using
    h xs n.bits (by simpa only [EncodedCommunication.bitsValue_bits] using hn)

#print axioms uniform_bits
#print axioms uniform
end
end CurrentAdditive.DynamicGetterOrdinary
