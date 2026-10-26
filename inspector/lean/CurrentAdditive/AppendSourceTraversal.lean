import CurrentAdditive.AppendNestedPolynomial
import CurrentAdditive.AppendSourceEncoding
import CurrentAdditive.PhysicalConcatLocal

set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

/-! An ordinary-input fixed machine for ordered source extension. Its count
header is produced by a second physical traversal that writes one unary bit
per indexed source/alphabet pair, followed by the checked count writer. -/
namespace CurrentAdditive.AppendSourceTraversal
open EthInapproximability.CurrentPaper
open CodeDSourceCodecV2 CodeDCanonicalSourceV2 AppendNestedMap
noncomputable section

def ones (xs : List (List Bool)) : xs.flatMap (fun _ => [true]) = List.replicate xs.length true := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih,List.replicate_succ]

theorem count_body (xs ys : List (List Bool)) :
    bodyResult AppendOrdinaryPrep.one false xs ys = List.replicate (xs.length*ys.length) true := by
  unfold bodyResult rowResult
  simp only [Bool.false_eq_true,↓reduceIte]
  have hrow (x : List Bool) : ys.flatMap (pairResult AppendOrdinaryPrep.one x) =
      List.replicate ys.length true := ones ys
  simp_rw [hrow]
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.length_cons,ih,List.replicate_append_replicate]
    congr 1
    simp only [Nat.add_mul,Nat.one_mul]
    omega

def headerMachine : BitMachine.Machine := BitMachineComposition.composition
  (bodyMachine AppendOrdinaryPrep.one false) AppendOrdinaryPrep.unaryField.machine

def headerClock (xs ys : List (List Bool)) :=
  bodyClock AppendOrdinaryPrep.one false xs ys + 2*(xs.length*ys.length)+2+
    AppendOrdinaryPrep.unaryField.coefficient*(xs.length*ys.length+1)^AppendOrdinaryPrep.unaryField.degree

theorem header_outputs (xs ys : List (List Bool)) :
    headerMachine.OutputsWithin (input xs ys)
      (EncodedCommunication.natField (xs.length*ys.length)) (headerClock xs ys) := by
  have h := body_outputs AppendOrdinaryPrep.one false xs ys
  rw [count_body] at h
  have hc := BitMachineComposition.composition_outputsWithin _ _ h
    (AppendOrdinaryPrep.unaryField.outputs (List.replicate (xs.length*ys.length) true))
  simpa [headerMachine,headerClock,AppendOrdinaryPrep.unaryField,List.length_replicate] using hc

theorem header_uniform : ∃ c d : Nat,∀ xs ys : List (List Bool),
    headerMachine.OutputsWithin (input xs ys) (EncodedCommunication.natField (xs.length*ys.length))
      (c*((input xs ys).length+1)^d) := by
  obtain ⟨a,e,h⟩ := AppendNestedPolynomial.body_uniform AppendOrdinaryPrep.one false
  refine ⟨AppendNestedPolynomial.composeCoefficient (bodyMachine AppendOrdinaryPrep.one false)
    a AppendOrdinaryPrep.unaryField.coefficient AppendOrdinaryPrep.unaryField.degree,
    AppendNestedPolynomial.composeDegree e AppendOrdinaryPrep.unaryField.degree,fun xs ys => ?_⟩
  have hb := h xs ys
  rw [count_body] at hb
  have hc := AppendNestedPolynomial.compose_outputs _ _ _ _ _ _ _ _ _ hb
    (AppendOrdinaryPrep.unaryField.outputs (List.replicate (xs.length*ys.length) true))
  simpa only [AppendOrdinaryPrep.unaryField,List.length_replicate] using hc

def headerCoefficient : Nat := Classical.choose header_uniform
def headerDegree : Nat := Classical.choose (Classical.choose_spec header_uniform)
def bodyCoefficient : Nat := Classical.choose (AppendNestedPolynomial.body_uniform AppendEntryPhysical.producer true)
def bodyDegree : Nat := Classical.choose (Classical.choose_spec (AppendNestedPolynomial.body_uniform AppendEntryPhysical.producer true))

theorem header_poly_outputs (xs ys : List (List Bool)) :
    headerMachine.OutputsWithin (input xs ys) (EncodedCommunication.natField (xs.length*ys.length))
      (headerCoefficient*((input xs ys).length+1)^headerDegree) :=
  Classical.choose_spec (Classical.choose_spec header_uniform) xs ys

theorem body_poly_outputs (xs ys : List (List Bool)) :
    (bodyMachine AppendEntryPhysical.producer true).OutputsWithin (input xs ys)
      (bodyResult AppendEntryPhysical.producer true xs ys)
      (bodyCoefficient*((input xs ys).length+1)^bodyDegree) :=
  Classical.choose_spec (Classical.choose_spec (AppendNestedPolynomial.body_uniform AppendEntryPhysical.producer true)) xs ys

def decodeInput (w : List Bool) : Option (List (List Bool) × List (List Bool)) := do
  let bank ← BitMachineBankCodec.decode 2 w
  let xs ← SourceListEncoding.decode (bank 0)
  let ys ← SourceListEncoding.decode (bank 1)
  pure (xs,ys)

theorem decode_input (xs ys : List (List Bool)) : decodeInput (input xs ys) = some (xs,ys) := by
  simp [decodeInput,input,packet,FeatureMapPairLoader.packet,SourceListEncoding.decode_encode]

def H : PhysicalConcatLocal.Producer where
  machine := headerMachine
  result w := match decodeInput w with
    | none => []
    | some (xs,ys) => EncodedCommunication.natField (xs.length*ys.length)
  clock w := headerCoefficient*(w.length+1)^headerDegree

def B : PhysicalConcatLocal.Producer where
  machine := bodyMachine AppendEntryPhysical.producer true
  result w := match decodeInput w with
    | none => []
    | some (xs,ys) => bodyResult AppendEntryPhysical.producer true xs ys
  clock w := bodyCoefficient*(w.length+1)^bodyDegree

def machine : BitMachine.Machine := PhysicalConcatLocal.machine (A := H) (B := B)

def output (xs ys : List (List Bool)) := EncodedCommunication.natField (xs.length*ys.length) ++
  bodyResult AppendEntryPhysical.producer true xs ys

def clock (xs ys : List (List Bool)) :=
  2*(input xs ys).length+2+1+headerCoefficient*((input xs ys).length+1)^headerDegree+1+
  bodyCoefficient*((input xs ys).length+1)^bodyDegree+
  2*(bodyResult AppendEntryPhysical.producer true xs ys).length+2+
  2*(EncodedCommunication.natField (xs.length*ys.length)).length+2+1

theorem outputs_lists (xs ys : List (List Bool)) :
    machine.OutputsWithin (input xs ys) (output xs ys) (clock xs ys) := by
  have hh : H.machine.OutputsWithin (input xs ys) (H.result (input xs ys)) (H.clock (input xs ys)) := by
    simpa only [H,decode_input] using header_poly_outputs xs ys
  have hb : B.machine.OutputsWithin (input xs ys) (B.result (input xs ys)) (B.clock (input xs ys)) := by
    simpa only [B,decode_input] using body_poly_outputs xs ys
  have hr := PhysicalConcatLocal.outputs (A := H) (B := B) (input xs ys) (hA := hh) (hB := hb)
  simpa only [machine,PhysicalConcatLocal.output,PhysicalConcatLocal.clock,H,B,decode_input,output,clock] using hr

theorem uniform_lists : ∃ c d : Nat,∀ xs ys : List (List Bool),
    machine.OutputsWithin (input xs ys) (output xs ys) (c*((input xs ys).length+1)^d) := by
  let c := 10+headerCoefficient*(1+2*headerMachine.pushBound)+
    bodyCoefficient*(1+2*(bodyMachine AppendEntryPhysical.producer true).pushBound)
  let d := headerDegree+bodyDegree+1
  refine ⟨c,d,fun xs ys => ?_⟩
  apply BitMachine.outputsWithin_mono _ (outputs_lists xs ys)
  have ha := BitMachine.output_length_bound headerMachine (header_poly_outputs xs ys)
  have hb := BitMachine.output_length_bound (bodyMachine AppendEntryPhysical.producer true) (body_poly_outputs xs ys)
  let n := (input xs ys).length
  let p := (n+1)^d
  have hbase : 1≤n+1 := by omega
  have hp : 1≤p := Nat.one_le_pow _ _ hbase
  have hpa : (n+1)^headerDegree≤p := Nat.pow_le_pow_right hbase (by dsimp [d];omega)
  have hpb : (n+1)^bodyDegree≤p := Nat.pow_le_pow_right hbase (by dsimp [d];omega)
  have hpx : n+1≤p := by
    simpa only [pow_one] using Nat.pow_le_pow_right hbase (show 1≤d by dsimp [d];omega)
  have hma := Nat.mul_le_mul_left (headerCoefficient*(1+2*headerMachine.pushBound)) hpa
  have hmb := Nat.mul_le_mul_left
    (bodyCoefficient*(1+2*(bodyMachine AppendEntryPhysical.producer true).pushBound)) hpb
  change clock xs ys≤c*p
  dsimp only [clock]
  dsimp only [c]
  change (EncodedCommunication.natField (xs.length*ys.length)).length≤
    n+headerCoefficient*(n+1)^headerDegree*headerMachine.pushBound at ha
  change (bodyResult AppendEntryPhysical.producer true xs ys).length≤
    n+bodyCoefficient*(n+1)^bodyDegree*(bodyMachine AppendEntryPhysical.producer true).pushBound at hb
  change 2*n+2+1+headerCoefficient*(n+1)^headerDegree+1+
    bodyCoefficient*(n+1)^bodyDegree+2*(bodyResult AppendEntryPhysical.producer true xs ys).length+2+
    2*(EncodedCommunication.natField (xs.length*ys.length)).length+2+1≤_
  nlinarith

def sourceItems {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) :=
  (canonicalSource source).map encodeEntry

def alphabetItems (alphabet : Array (Nat × ℚ)) := alphabet.toList.map CodeDTargetV2.alphabetEntry

theorem output_exact {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) (alphabet : Array (Nat × ℚ)) :
    output (sourceItems source) (alphabetItems alphabet) =
      encodedSource (SequentialCode.appendSource source alphabet) := by
  exact AppendSourceEncoding.output_exact source alphabet

theorem append_outputs {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) (alphabet : Array (Nat × ℚ)) :
    machine.OutputsWithin
      (BitMachineBankCodec.encode (![encodedSource source,CodeDTargetV2.alphabetBytes alphabet] : Fin 2 → List Bool))
      (encodedSource (SequentialCode.appendSource source alphabet))
      (clock (sourceItems source) (alphabetItems alphabet)) := by
  have h := outputs_lists (sourceItems source) (alphabetItems alphabet)
  rw [output_exact] at h
  exact h

/-- One fixed finite machine and one polynomial cover every actual serialized
source/alphabet input. The only arguments are the original indexed arrays. -/
theorem uniform_append : ∃ c d : Nat,∀ q : Nat,
    ∀ source : Array ((Fin q → Nat) × ℚ),∀ alphabet : Array (Nat × ℚ),
    machine.OutputsWithin
      (BitMachineBankCodec.encode (![encodedSource source,CodeDTargetV2.alphabetBytes alphabet] : Fin 2 → List Bool))
      (encodedSource (SequentialCode.appendSource source alphabet))
      (c*((BitMachineBankCodec.encode (![encodedSource source,CodeDTargetV2.alphabetBytes alphabet] : Fin 2 → List Bool)).length+1)^d) := by
  obtain ⟨c,d,h⟩ := uniform_lists
  refine ⟨c,d,fun q source alphabet => ?_⟩
  have ho := h (sourceItems source) (alphabetItems alphabet)
  rw [output_exact] at ho
  exact ho

#print axioms append_outputs
#print axioms uniform_append
end
end CurrentAdditive.AppendSourceTraversal
