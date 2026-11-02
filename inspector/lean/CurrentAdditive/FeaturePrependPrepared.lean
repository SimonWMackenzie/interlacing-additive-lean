import CurrentAdditive.FeaturePairPrepared
import CurrentAdditive.FeatureCountFieldSuccessor
import CurrentAdditive.FeaturePreparedJoin

/-! Exact ordered feature-cons bytes from three physically prepared fields. -/

namespace CurrentAdditive.FeaturePrependPrepared

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open CurrentAdditive.CylinderFeatureCodec
open Turing BitMachineEncoding

def pairField (j y : Nat) : List Bool :=
  natField (encodePair (j,y)).length ++ encodePair (j,y)

def oldSuffix (c : List (Nat × Nat)) : List Bool :=
  SourceListEncoding.fields (c.map encodePair)

theorem encodeFeature_cons (j y : Nat) (c : List (Nat × Nat)) :
    encodeFeature ((j,y)::c) =
      natField (c.length+1) ++ pairField j y ++ oldSuffix c := by
  simp [encodeFeature, CodeDCodecV2.encodeItems, SourceListEncoding.encode,
    SourceListEncoding.fields, pairField, oldSuffix,
    List.map_cons, List.length_map, List.length_cons, List.append_assoc]

theorem pair_prepend_prepared (j y : Nat) (c : List (Nat × Nat)) :
    let header := natField (c.length+1)
    let pair := pairField j y
    let suffix := oldSuffix c
    let t := 2*suffix.length+2 + (2*pair.length+2) +
      (2*header.length+2) + 1
    let z := FeaturePreparedJoin.run t
      (⟨some .suffixScan,((),none),
        FeaturePreparedJoin.initialBank header pair suffix⟩ :
        TM2.Cfg (fun _ : FeaturePreparedJoin.Stack => Bool)
          FeaturePreparedJoin.Label FeaturePreparedJoin.Control)
    z.l = none ∧ z.stk 4 = encodeFeature ((j,y)::c) := by
  have h := FeaturePreparedJoin.prepared_run
    (natField (c.length+1)) (pairField j y) (oldSuffix c)
  simpa only [encodeFeature_cons] using h

theorem pair_prepend_clock (j y : Nat) (c : List (Nat × Nat)) :
    let header := natField (c.length+1)
    let pair := pairField j y
    let suffix := oldSuffix c
    let t := 2*suffix.length+2 + (2*pair.length+2) +
      (2*header.length+2) + 1
    t = 2*(header.length+pair.length+suffix.length)+7 := by
  dsimp
  omega

#print axioms encodeFeature_cons
#print axioms pair_prepend_prepared
#print axioms pair_prepend_clock

end CurrentAdditive.FeaturePrependPrepared
