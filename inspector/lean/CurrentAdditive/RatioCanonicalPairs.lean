import CurrentAdditive.RatioPairList
import CurrentAdditive.RatioCanonicalRequests
import CurrentAdditive.RatioArrayIdentity

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace CurrentAdditive.RatioCanonicalPairs
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open MinimumRatioCallbackLayout RatioCanonicalRequests

theorem pairs_exact {q : Nat} (source : Array ((Fin q → Nat) × ℚ))
    (coeff : Array ℚ) (hsize : coeff.size=source.size) :
    RatioPairListSpec.pairs (records source) (coeffWords coeff) =
      RatioPhysicalFold.pairWords
        (MinimumRatioFoldSemanticJoin.pairs (source.map Prod.snd) coeff) := by
  apply List.ext_getElem
  · simp [RatioPairListSpec.pairs,records,RatioPhysicalFold.pairWords,
      MinimumRatioFoldSemanticJoin.pairs,hsize]
  · intro i hi hj
    have hs : i < source.size := by simpa [RatioPairListSpec.pairs,records] using hi
    have hc : i < coeff.size := by omega
    have hcoef : RatioPairListSpec.coefficient (coeffWords coeff) i = ratWord coeff[i] := by
      simp [RatioPairListSpec.coefficient,coeffWords,ratWord,Array.getElem?_eq_getElem hc]
    simp [RatioPairListSpec.pairs,records,List.getElem_mapIdx,List.getElem_map,
      hcoef,RatioPairItem.pairWord,RatioPairItem.massWord,RatioMassProjection.result_entry,
      CodeDCanonicalSourceV2.canonicalEntry,ratWord,RatioPairSerializer.bytes_pair,
      RatioPhysicalFold.pairWords,MinimumRatioFoldSemanticJoin.pairs,
      MinimumRatioFoldSemanticJoin.pairAt,Array.getElem?_eq_getElem hs,
      Array.getElem?_eq_getElem hc,CodeDCanonicalSourceV2.rawOfRat,GaussPhysical.rawOfRat]
    rfl

theorem runs {q : Nat} (source : Array ((Fin q → Nat) × ℚ))
    (coeff : Array ℚ) (hsize : coeff.size=source.size) :
    ∃ t ≤ RatioPairList.clock (records source) (coeffWords coeff)
      (by simpa [records,coeffWords] using hsize), ∃ v,
      ((advance RatioPairList.program)^[t])
        (⟨some (.inr (.inr .check)),
          StatefulListScheduler.getterControl RatioPairItem.control
            (CylinderContextScanStep.copyControl ((),none)),
          RatioRequestFrame.boundary (SourceListEncoding.encode (records source))
            (EncodedCommunication.natField source.size)
            (SourceListEncoding.encode (coeffWords coeff)) [] 0 source.size⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,v,RatioRequestFrame.boundary (SourceListEncoding.encode (records source))
          (SourceListEncoding.encode (RatioPhysicalFold.pairWords
            (MinimumRatioFoldSemanticJoin.pairs (source.map Prod.snd) coeff)))
          (SourceListEncoding.encode (coeffWords coeff)) [] source.size 0⟩ := by
  have hr := RatioPairList.runs (records source) (coeffWords coeff)
    (by simpa [records,coeffWords] using hsize)
  rw [pairs_exact source coeff hsize] at hr
  simpa only [records,List.length_map,Array.length_toList] using hr

#print axioms pairs_exact
#print axioms runs
end CurrentAdditive.RatioCanonicalPairs
