import CurrentAdditive.StoredQuery
import CurrentAdditive.CylinderEvalMapPolynomial

/-! Ordered, charged list traversal for concrete stored-cell queries. The
callback is the physically compiled fixed query, and its clock constants are
chosen before the context and list. Empty lists and duplicate positions are
preserved by the underlying physical mapper. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace CurrentAdditive.StoredQuery
open EthInapproximability.CurrentPaper
noncomputable section
attribute [local instance] Classical.propDecidable

def answers (A : Query) (context : List Bool) (w : List Bool) : List Bool :=
  (A.result (FeatureMapPairLoader.packet context w)).getD []

def validItems (A : Query) (context : List Bool) (xs : List (List Bool)) : Prop :=
  ∀ w∈xs,(A.result (FeatureMapPairLoader.packet context w)).isSome

theorem answer_result (A : Query) (context : List Bool) (xs : List (List Bool))
    (hv : validItems A context xs) (w : List Bool) (hw : w∈xs) :
    A.result (FeatureMapPairLoader.packet context w)=some (answers A context w) := by
  have hh := hv w hw
  unfold answers
  cases he : A.result (FeatureMapPairLoader.packet context w) with
  | none => simp [he] at hh
  | some ans => simp

def mapResult (A : Query) (framed : Bool) (x : List Bool) : Option (List Bool) :=
  match BitMachineBankCodec.decode 2 x with
  | none => none
  | some S => match SourceListEncoding.decode (S 1) with
    | none => none
    | some xs =>
      if hc : S 1=SourceListEncoding.encode xs then
        if hv : validItems A (S 0) xs then
          some (FeatureContextMap.result framed xs (answers A (S 0)))
        else none
      else none

theorem mapResult_packet (A : Query) (framed : Bool) (context : List Bool)
    (xs : List (List Bool)) (hv : validItems A context xs) :
    mapResult A framed (FeatureMapPairLoader.packet context (SourceListEncoding.encode xs))=
      some (FeatureContextMap.result framed xs (answers A context)) := by
  simp [mapResult,FeatureMapPairLoader.packet,SourceListEncoding.decode_encode,hv]

def mapCoefficient (A : Query) (framed : Bool) : Nat :=
  Classical.choose (CylinderEvalMapPolynomial.uniform_from_callback A.machine framed A.coefficient A.degree)
def mapDegree (A : Query) (framed : Bool) : Nat :=
  Classical.choose (Classical.choose_spec
    (CylinderEvalMapPolynomial.uniform_from_callback A.machine framed A.coefficient A.degree))

theorem mapped_outputs (A : Query) (framed : Bool) (context : List Bool)
    (xs : List (List Bool)) (hv : validItems A context xs) :
    (FeatureContextMap.machine A.machine framed).OutputsWithin
      (FeatureMapPairLoader.packet context (SourceListEncoding.encode xs))
      (FeatureContextMap.result framed xs (answers A context))
      (mapCoefficient A framed*
        ((FeatureMapPairLoader.packet context (SourceListEncoding.encode xs)).length+1)^mapDegree A framed) := by
  let b := fun w => A.coefficient*((FeatureMapPairLoader.packet context w).length+1)^A.degree
  have hM : ∀w∈xs,A.machine.OutputsWithin (FeatureMapPairLoader.packet context w)
      (answers A context w) (b w) := by
    intro w hw
    exact A.outputs _ _ (answer_result A context xs hv w hw)
  have ht := Classical.choose_spec (Classical.choose_spec
    (CylinderEvalMapPolynomial.uniform_from_callback A.machine framed A.coefficient A.degree))
    context xs (answers A context) b hM (fun _ _ => le_rfl)
  exact BitMachine.outputsWithin_mono _
    (FeatureContextMap.outputs_explicit A.machine framed context xs (answers A context) b hM) ht

def mapItems (A : Query) (framed : Bool) : Query where
  result := mapResult A framed
  machine := FeatureContextMap.machine A.machine framed
  coefficient := mapCoefficient A framed
  degree := mapDegree A framed
  outputs x y h := by
    unfold mapResult at h
    cases hd : BitMachineBankCodec.decode 2 x with
    | none => simp [hd] at h
    | some S =>
      cases hs : SourceListEncoding.decode (S 1) with
      | none => simp [hd,hs] at h
      | some xs =>
        simp only [hd,hs] at h
        split at h
        · rename_i hc
          split at h
          · rename_i hv
            have hy : FeatureContextMap.result framed xs (answers A (S 0))=y := Option.some.inj h
            subst y
            have he : x=FeatureMapPairLoader.packet (S 0) (SourceListEncoding.encode xs) := by
              rw [← BitMachineBankCodec.encode_decode hd]
              congr 1
              funext j;fin_cases j <;> simp [FeatureMapPairLoader.packet,hc]
            rw [he]
            exact mapped_outputs A framed (S 0) xs hv
          · contradiction
        · contradiction

end
end CurrentAdditive.StoredQuery

#print axioms CurrentAdditive.StoredQuery.mapItems
#print axioms CurrentAdditive.StoredQuery.mapped_outputs
