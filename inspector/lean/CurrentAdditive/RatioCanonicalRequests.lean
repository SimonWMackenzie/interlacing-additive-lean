import CurrentAdditive.RatioRequestList
import CurrentAdditive.CodeDUpdateRequestABI

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-! The literal positional request-list producer agrees with the canonical
source-position arithmetic ABI. It preserves every source position. -/
noncomputable section
namespace CurrentAdditive.RatioCanonicalRequests
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open MinimumRatioCallbackLayout RatioRequestListSpec

noncomputable def records {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) :
    List (List Bool) :=
  source.toList.map (fun old => CodeDSourceCodecV2.encodeEntry (CodeDCanonicalSourceV2.canonicalEntry old))
noncomputable def coeffWords (coeff : Array ℚ) : List (List Bool) :=
  coeff.toList.map (fun c => CodeDCodec.encodeRawRat (CodeDCanonicalSourceV2.rawOfRat c))
def ratWord (r : ℚ) : List Bool := CodeDCodec.encodeRawRat (CodeDCanonicalSourceV2.rawOfRat r)

theorem requests_exact {q : Nat} (source : Array ((Fin q → Nat) × ℚ))
    (coeff : Array ℚ) (lambda : ℚ) (hsize : coeff.size=source.size) :
    requests (records source) (coeffWords coeff) (ratWord lambda) =
      CodeDUpdateRequestABI.requestItems source coeff lambda := by
  let old (i : Nat) := (source[i]?).getD ((fun _ => 0),0)
  let item (i : Nat) := CodeDUpdateProductPairFields.requestPacket
    (CodeDCanonicalSourceV2.canonicalEntry (old i)) lambda (coeff[i]?.getD 0)
  have hitems : CodeDUpdateRequestABI.requestItems source coeff lambda =
      (List.range source.size).map item := by
    apply List.filterMap_eq_map_iff_forall_eq_some.mpr
    intro i hi
    have hs : i < source.size := List.mem_range.mp hi
    simp [item,old,Array.getElem?_eq_getElem hs]
  rw [hitems]
  apply List.ext_getElem
  · simp [requests,records]
  · intro i hi hj
    have hs : i < source.size := by simpa [requests,records] using hi
    have hc : i < coeff.size := by omega
    have hw : i < (coeffWords coeff).length := by simpa [coeffWords] using hc
    have hcoef : coefficient (coeffWords coeff) i = ratWord coeff[i] := by
      simp [coefficient,List.getElem?_eq_getElem hw,coeffWords,ratWord,Array.getElem?_eq_getElem hc]
    simp [requests,records,List.getElem_mapIdx,List.getElem_map,
      hcoef,ratWord,RatioRequestSerializer.bytes_request,item,old,
      Array.getElem?_eq_getElem hs,Array.getElem?_eq_getElem hc]

theorem runs {q : Nat} (source : Array ((Fin q → Nat) × ℚ))
    (coeff : Array ℚ) (lambda : ℚ) (hsize : coeff.size=source.size) :
    ∃ t ≤ RatioRequestList.clock (records source) (coeffWords coeff) (ratWord lambda)
      (by simpa [records,coeffWords] using hsize), ∃ v,
      ((advance RatioRequestList.program)^[t])
        (⟨some (.inr (.inr .check)),
          StatefulListScheduler.getterControl RatioUpdateAppendItem.control
            (CylinderContextScanStep.copyControl ((),none)),
          RatioRequestFrame.boundary (SourceListEncoding.encode (records source))
            (EncodedCommunication.natField source.size)
            (SourceListEncoding.encode (coeffWords coeff)) (ratWord lambda)
            0 source.size⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,v,RatioRequestFrame.boundary (SourceListEncoding.encode (records source))
          (CodeDUpdateRequestABI.requestPacketList source coeff lambda)
          (SourceListEncoding.encode (coeffWords coeff)) (ratWord lambda) source.size 0⟩ := by
  have hr := RatioRequestList.runs (records source) (coeffWords coeff) (ratWord lambda)
    (by simpa [records,coeffWords] using hsize)
  rw [requests_exact source coeff lambda hsize] at hr
  simpa only [records,List.length_map,Array.length_toList,
    CodeDUpdateRequestABI.requestPacketList,CodeDCodecV2.encodeItems] using hr

#print axioms requests_exact
#print axioms runs
end CurrentAdditive.RatioCanonicalRequests
