import CurrentAdditive.StoredRetainedGetter
import CurrentAdditive.StoredBinaryBitLookup
import CurrentAdditive.StoredBinaryAdd

/-! Finite ordinary computations used by the actual stored-cell decoder.
Each combinator supplies a literal machine and a polynomial in its original
input bytes. Option-valued semantics specify valid data, including canonical
list packets and in-range indices. A final concrete query is assembled from
these constructors; no query implementation is accepted from the caller. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace CurrentAdditive.StoredQuery
open EthInapproximability.CurrentPaper PhysicalProducer
noncomputable section

structure Query where
  result : List Bool → Option (List Bool)
  machine : BitMachine.Machine
  coefficient : Nat
  degree : Nat
  outputs : ∀ x y, result x=some y →
    machine.OutputsWithin x y (coefficient*(x.length+1)^degree)

def total (A : Producer) : Query where
  result x := some (A.result x)
  machine := A.machine
  coefficient := A.coefficient
  degree := A.degree
  outputs x y h := by cases h; exact A.outputs x

def compose (A B : Query) : Query where
  result x := (A.result x).bind B.result
  machine := BitMachineComposition.composition A.machine B.machine
  coefficient := DynamicGetterOrdinary.composeCoefficient A.machine A.coefficient B.coefficient B.degree
  degree := DynamicGetterOrdinary.composeDegree A.degree B.degree
  outputs x z h := by
    cases ha : A.result x with
    | none => simp [ha] at h
    | some y =>
      have hb : B.result y=some z := by simpa [ha] using h
      exact DynamicGetterOrdinary.compose_outputs _ _ _ _ _ _ _ _ _
        (A.outputs x y ha) (B.outputs y z hb)

def retainRouter := StoredRetainedGetter.bank2 StoredRetainedGetter.identity StoredRetainedGetter.identity

theorem retainRouter_result (x : List Bool) : retainRouter.result x=ContextualInvoke.packet x x := by
  simp [retainRouter,StoredRetainedGetter.bank2_result,StoredRetainedGetter.identity,
    ContextualInvoke.packet]

def retain (A : Query) : Query where
  result x := (A.result x).map (fun y => BitMachineBankCodec.encode ![x,y])
  machine := BitMachineComposition.composition retainRouter.machine (ContextualInvoke.machine A.machine)
  coefficient := DynamicGetterOrdinary.composeCoefficient retainRouter.machine retainRouter.coefficient
    (ContextualInvoke.polynomialCoefficient A.machine A.coefficient) (A.degree+1)
  degree := DynamicGetterOrdinary.composeDegree retainRouter.degree (A.degree+1)
  outputs x z h := by
    cases ha : A.result x with
    | none => simp [ha] at h
    | some y =>
      have hz : BitMachineBankCodec.encode ![x,y]=z := by simpa [ha] using h
      subst z
      have hA := A.outputs x y ha
      have hc := ContextualInvoke.outputs_polynomial A.machine A.coefficient A.degree x x y hA
      exact DynamicGetterOrdinary.compose_outputs _ _ _ _ _ _ _ _ _
        (retainRouter.outputs x) (by simpa only [retainRouter_result] using hc)

def pairFinish := StoredRetainedGetter.bank2
  (PhysicalProducer.compose (projection (0 : Fin 2)) (projection (1 : Fin 2)))
  (projection (1 : Fin 2))

def pair (A B : Query) : Query :=
  compose (compose (retain A) (retain (compose (total (projection (0 : Fin 2))) B)))
    (total pairFinish)

theorem pair_result (A B : Query) (x a b : List Bool)
    (ha : A.result x=some a) (hb : B.result x=some b) :
    (pair A B).result x=some (BitMachineBankCodec.encode ![a,b]) := by
  simp [pair,compose,retain,ha,hb,total,pairFinish,StoredRetainedGetter.bank2_result,
    PhysicalProducer.compose,projection,BankFieldProjection.result_encode]

def lookupResult (x : List Bool) : Option (List Bool) :=
  match BitMachineBankCodec.decode 2 x with
  | none => none
  | some S => match SourceListEncoding.decode (S 0) with
    | none => none
    | some xs =>
      if h : S 0=SourceListEncoding.encode xs then
        if hi : EncodedCommunication.bitsValue (S 1)<xs.length then
          some xs[EncodedCommunication.bitsValue (S 1)]
        else none
      else none

theorem lookupResult_packet (xs : List (List Bool)) (bits : List Bool)
    (hi : EncodedCommunication.bitsValue bits<xs.length) :
    lookupResult (BitMachineBankCodec.encode ![SourceListEncoding.encode xs,bits])=
      some xs[EncodedCommunication.bitsValue bits] := by
  simp [lookupResult,SourceListEncoding.decode_encode,hi]

def selected : Query where
  result := lookupResult
  machine := DynamicGetterOrdinary.machine
  coefficient := StoredRetainedGetter.getterCoefficient
  degree := StoredRetainedGetter.getterDegree
  outputs x y h := by
    unfold lookupResult at h
    cases hd : BitMachineBankCodec.decode 2 x with
    | none => simp [hd] at h
    | some S =>
      cases hs : SourceListEncoding.decode (S 0) with
      | none => simp [hd,hs] at h
      | some xs =>
        simp only [hd,hs] at h
        split at h
        · rename_i hc
          split at h
          · rename_i hi
            have hy : xs[EncodedCommunication.bitsValue (S 1)]=y := Option.some.inj h
            subst y
            have he : x=BitMachineBankCodec.encode ![SourceListEncoding.encode xs,S 1] := by
              rw [← BitMachineBankCodec.encode_decode hd]
              congr 1
              funext j;fin_cases j <;> simp [hc]
            rw [he]
            exact StoredRetainedGetter.getter_outputs xs (S 1) hi
          · contradiction
        · contradiction

def lookup (source address : Query) := compose (pair source address) selected

theorem lookup_result (source address : Query) (x bits : List Bool) (xs : List (List Bool))
    (hs : source.result x=some (SourceListEncoding.encode xs))
    (ha : address.result x=some bits)
    (hi : EncodedCommunication.bitsValue bits<xs.length) :
    (lookup source address).result x=some xs[EncodedCommunication.bitsValue bits] := by
  simp only [lookup,compose,pair_result source address x _ _ hs ha,Option.bind_some,selected]
  exact lookupResult_packet xs bits hi

def add (A B : Query) := compose (pair A B) (total StoredBinaryAdd.producer)
def bitAt (A B : Query) := compose (pair A B) (total StoredBinaryBitLookup.producer)

end
end CurrentAdditive.StoredQuery

#print axioms CurrentAdditive.StoredQuery.retain
#print axioms CurrentAdditive.StoredQuery.pair
#print axioms CurrentAdditive.StoredQuery.selected
#print axioms CurrentAdditive.StoredQuery.lookup
