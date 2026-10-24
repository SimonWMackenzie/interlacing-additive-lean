import CurrentAdditive.PhysicalProducer
import CurrentAdditive.CodeDAppendTargetV2

/-! A fixed ordinary-input physical append-entry evaluator. Both inputs are
parsed from their original serialized records; no product, new word, or run
is supplied to this machine. Signed and zero rational weights are accepted. -/
namespace CurrentAdditive.AppendEntryPhysical
open EthInapproximability.CurrentPaper
open EncodedCommunication CodeDSourceCodecV2 CodeDCanonicalSourceV2
open PhysicalProducer
noncomputable section

def packet (x : Entry) (y : Nat × ℚ) : List Bool :=
  BitMachineBankCodec.encode (![encodeEntry x,CodeDTargetV2.alphabetEntry y] : Fin 2 → List Bool)

def source := projection (0 : Fin 2)
def alphabet := projection (1 : Fin 2)
def word := compose source (projection (0 : Fin 2))
def weight := compose source (projection (1 : Fin 2))
def symbol := compose alphabet (projection (0 : Fin 2))
def symbolWeight := compose alphabet (projection (1 : Fin 2))
def newWord := concat (compose word countSuccessor)
  (concat (compose word stripHeader) (compose symbol item))
def weightRequest := concat (compose weight field) (compose symbolWeight field)
def newWeight := compose weightRequest rationalProduct
def producer := concat (compose newWord field) (compose newWeight field)
def machine : BitMachine.Machine := producer.machine

theorem compose_result (A B : Producer) (x : List Bool) :
    (compose A B).result x = B.result (A.result x) := rfl

theorem concat_result (A B : Producer) (x : List Bool) :
    (concat A B).result x = A.result x ++ B.result x := rfl

theorem projection_result {K : Nat} (j : Fin K) (x : List Bool) :
    (projection j).result x = BankFieldProjection.result j x := rfl

theorem source_packet (x : Entry) (y : Nat × ℚ) :
    source.result (packet x y) = encodeEntry x := by
  simp [source, projection_result,packet,BankFieldProjection.result_encode]

theorem alphabet_packet (x : Entry) (y : Nat × ℚ) :
    alphabet.result (packet x y) = CodeDTargetV2.alphabetEntry y := by
  simp [alphabet,projection_result,packet,BankFieldProjection.result_encode]

theorem word_packet (x : Entry) (y : Nat × ℚ) :
    word.result (packet x y) = CodeDCodecV2.encodeItems x.word := by
  simp [word,compose_result,source_packet,projection_result,
    encodeEntry,BankFieldProjection.result_encode]

theorem weight_packet (x : Entry) (y : Nat × ℚ) :
    weight.result (packet x y) = CodeDCodec.encodeRawRat x.weight := by
  simp [weight,compose_result,source_packet,projection_result,
    encodeEntry,BankFieldProjection.result_encode]

theorem symbol_packet (x : Entry) (y : Nat × ℚ) :
    symbol.result (packet x y) = y.1.bits := by
  simp [symbol,compose_result,alphabet_packet,projection_result,
    CodeDTargetV2.alphabetEntry,BankFieldProjection.result_encode]

theorem symbolWeight_packet (x : Entry) (y : Nat × ℚ) :
    symbolWeight.result (packet x y) = CodeDCodec.encodeRawRat (rawOfRat y.2) := by
  simp [symbolWeight,compose_result,alphabet_packet,projection_result,
    CodeDTargetV2.alphabetEntry,BankFieldProjection.result_encode]

theorem successor_encode (xs : List (List Bool)) :
    countSuccessor.result (CodeDCodecV2.encodeItems xs) = natField (xs.length+1) := by
  simp [countSuccessor,FeatureCountFieldSuccessor.result,
    CodeDCodecV2.encodeItems,SourceListEncoding.encode,natField,readField_append,
    BinarySuccessorMachine.successor_bits]

theorem strip_encode (xs : List (List Bool)) :
    stripHeader.result (CodeDCodecV2.encodeItems xs) = SourceListEncoding.fields xs := by
  exact BitMachine.outputsWithin_unique CodeDStripHeaderV2.machine
    (CodeDStripHeaderV2.outputs_total (CodeDCodecV2.encodeItems xs))
    (CodeDStripHeaderV2.outputs_valid xs.length (SourceListEncoding.fields xs))

theorem fields_append (xs ys : List (List Bool)) :
    SourceListEncoding.fields (xs++ys) =
      SourceListEncoding.fields xs ++ SourceListEncoding.fields ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [SourceListEncoding.fields,ih,List.append_assoc]

theorem newWord_packet (x : Entry) (y : Nat × ℚ) :
    newWord.result (packet x y) = CodeDCodecV2.encodeItems (x.word++[y.1.bits]) := by
  simp only [newWord,concat_result,compose_result,word_packet,symbol_packet,
    successor_encode,strip_encode]
  simp [PhysicalProducer.item,SourceListMachineWriter.result,
    CodeDCodecV2.encodeItems,SourceListEncoding.encode,fields_append,
    SourceListEncoding.fields,List.append_assoc]

theorem weightRequest_packet (x : Entry) (y : Nat × ℚ) :
    weightRequest.result (packet x y) =
      CodeDPairProductTargetV2.pairBytes x.weight (rawOfRat y.2) := by
  simp only [weightRequest,concat_result,compose_result,weight_packet,symbolWeight_packet]
  simp [PhysicalProducer.field,CodeDPairProductTargetV2.pairBytes,
    CodeDPairProductTargetV2.pairBank,BitMachineBankCodec.encode_eq_list]

theorem newWeight_packet (x : Entry) (y : Nat × ℚ) (hx : x.weight.Valid) :
    newWeight.result (packet x y) =
      CodeDCodec.encodeRawRat (rawOfRat (x.weight.value*y.2)) := by
  rw [newWeight,compose_result,weightRequest_packet]
  change RationalCanonicalCallback.productResult
    (CodeDPairProductTargetV2.pairBytes x.weight (rawOfRat y.2)) = _
  rw [RationalCanonicalCallback.product_result_pair x.weight (rawOfRat y.2)
    hx (rawOfRat_valid y.2),rawOfRat_value]
  rfl

theorem result_packet (x : Entry) (y : Nat × ℚ) (hx : x.weight.Valid) :
    producer.result (packet x y) =
      encodeEntry ⟨x.word++[y.1.bits],rawOfRat (x.weight.value*y.2)⟩ := by
  simp only [producer,concat_result,compose_result,newWord_packet,newWeight_packet x y hx]
  simp [PhysicalProducer.field,encodeEntry,BitMachineBankCodec.encode_eq_list]

theorem outputs_packet (x : Entry) (y : Nat × ℚ) (hx : x.weight.Valid) :
    machine.OutputsWithin (packet x y)
      (encodeEntry ⟨x.word++[y.1.bits],rawOfRat (x.weight.value*y.2)⟩)
      (producer.coefficient*((packet x y).length+1)^producer.degree) := by
  have h := producer.outputs (packet x y)
  rw [result_packet x y hx] at h
  exact h

theorem uniform_clock : ∃ c d : Nat, ∀ x : Entry, ∀ y : Nat × ℚ,
    x.weight.Valid → machine.OutputsWithin (packet x y)
      (encodeEntry ⟨x.word++[y.1.bits],rawOfRat (x.weight.value*y.2)⟩)
      (c*((packet x y).length+1)^d) :=
  ⟨producer.coefficient,producer.degree,outputs_packet⟩

#print axioms outputs_packet
#print axioms uniform_clock
end
end CurrentAdditive.AppendEntryPhysical
