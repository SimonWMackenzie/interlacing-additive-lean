import CurrentAdditive.CodeDUpdatePacketSize

/-! A single-parameter polynomial clock on canonical request packets. -/

namespace CurrentAdditive.CodeDUpdateUnivariateClock

open EthInapproximability.CurrentPaper
open CodeDUpdateArithmeticClock

set_option maxHeartbeats 1000000

private theorem finalTime_mono {a b : Nat} (h : a ≤ b) :
    finalItemTimeBound a ≤ finalItemTimeBound b := by
  unfold finalItemTimeBound differenceFrameTimeBound
    differenceFrameOutputBound differenceWordBound
    subtractTimeBound subtractPairOutputBound subtractPairTimeBound
    productFrameTimeBound productFrameOutputBound
    productWordBound productTimeBound
  gcongr

private theorem finalOutput_mono {a b : Nat} (h : a ≤ b) :
    finalItemOutputBound a ≤ finalItemOutputBound b := by
  unfold finalItemOutputBound
  gcongr
  exact finalTime_mono h

private theorem arithmeticClock_mono {n m a b : Nat}
    (hn : n ≤ m) (ha : a ≤ b) :
    polynomialClock n a ≤ polynomialClock m b := by
  unfold polynomialClock itemEnvelope timeBound frameBound
  gcongr
  all_goals first | exact finalTime_mono ha | exact finalOutput_mono ha

private theorem updatedClock_mono {n m a b : Nat}
    (hn : n ≤ m) (ha : a ≤ b) :
    CodeDUpdatedEntryClockV2.polynomialClock n a ≤
      CodeDUpdatedEntryClockV2.polynomialClock m b := by
  unfold CodeDUpdatedEntryClockV2.polynomialClock
    CodeDUpdatedEntryClockV2.itemEnvelope
    CodeDUpdatedEntryClockV2.timeBound
    CodeDUpdatedEntryClockV2.frameBound
    CodeDUpdatedEntryClockV2.itemResultBound
  gcongr

private theorem zeroClock_mono {n m a b : Nat}
    (hn : n ≤ m) (ha : a ≤ b) :
    CodeDZeroListClockV2.polynomialClock n a ≤
      CodeDZeroListClockV2.polynomialClock m b := by
  unfold CodeDZeroListClockV2.polynomialClock
    CodeDZeroListClockV2.itemEnvelope
    CodeDZeroListClockV2.framedTime
  gcongr

private theorem compactClock_mono {n m a b : Nat}
    (hn : n ≤ m) (ha : a ≤ b) :
    CodeDCompactClockV2.polynomialClock n a ≤
      CodeDCompactClockV2.polynomialClock m b := by
  unfold CodeDCompactClockV2.polynomialClock
    CodeDCompactClockV2.bodyResultBound
    CodeDCompactClockV2.headerResultBound
    CodeDCompactClockV2.inputBound
    CodeDCompactClockV2.headerClockBound
    CodeDCompactClockV2.bodyClockBound
    CodeDCompactClockV2.bodyListBound
    CodeDCompactClockV2.itemEnvelope
    CodeDCompactClockV2.itemTime
    CodeDCompactClockV2.itemOutput
    CodeDCompactClockV2.bodyOutputBound
    CodeDCompactClockV2.zeroOutputBound
    CodeDCompactClockV2.keepFlagClockBound
    CodeDCompactClockV2.keepMarkedBound
    CodeDCompactClockV2.keepMarkedOutputBound
  gcongr
  all_goals first
    | exact zeroClock_mono hn ha
    | (unfold CodeDCompactClockV2.itemOutput; gcongr)

private theorem compactInput_mono {n m a b : Nat}
    (hn : n ≤ m) (ha : a ≤ b) :
    CodeDCompactClockV2.inputBound n a ≤
      CodeDCompactClockV2.inputBound m b := by
  unfold CodeDCompactClockV2.inputBound
  gcongr

private theorem updatedItemResult_mono {a b : Nat} (h : a ≤ b) :
    CodeDUpdatedEntryClockV2.itemResultBound a ≤
      CodeDUpdatedEntryClockV2.itemResultBound b := by
  unfold CodeDUpdatedEntryClockV2.itemResultBound
  gcongr

private theorem updatedPipeline_mono {n m a b : Nat}
    (hn : n ≤ m) (ha : a ≤ b) :
    CodeDUpdatedEntryClockV2.pipelineClock n a ≤
      CodeDUpdatedEntryClockV2.pipelineClock m b := by
  unfold CodeDUpdatedEntryClockV2.pipelineClock
  have hi := updatedItemResult_mono ha
  gcongr
  · exact updatedClock_mono hn ha
  · exact compactInput_mono hn hi
  · exact compactClock_mono hn hi

theorem fullPipelineBound_mono (N L m : Nat)
    (hN : N ≤ m) (hL : L ≤ m) :
    fullPipelineBound N L ≤ fullPipelineBound m m := by
  unfold fullPipelineBound
  have ho := finalOutput_mono hL
  gcongr
  · exact arithmeticClock_mono hN hL
  · exact compactInput_mono hN ho
  · exact updatedPipeline_mono hN ho

/-- The clock bound is a fixed polynomial in the actual canonical request
packet length; this theorem deliberately applies only to those packets. -/
theorem valid_packet_clock_le {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ)
    (lambda : ℚ) :
    CodeDUpdateFullPipeline.clock source coeff lambda ≤
      fullPipelineBound
        (CodeDUpdateRequestABI.requestPacketList source coeff lambda).length
        (CodeDUpdateRequestABI.requestPacketList source coeff lambda).length := by
  let requests := CodeDUpdateRequestABI.requestItems source coeff lambda
  let m := (CodeDUpdateRequestABI.requestPacketList source coeff lambda).length
  have hitem : ∀ x ∈ requests, x.length ≤ m := by
    intro x hx
    exact CodeDUpdatePacketSize.item_length_le_packet requests x hx
  have hcount : requests.length ≤ m :=
    CodeDUpdatePacketSize.count_le_packet requests
  have hc := full_pipeline_clock_le source coeff lambda m hitem
  exact le_trans hc (fullPipelineBound_mono requests.length m m hcount (le_refl m))

#print axioms fullPipelineBound_mono
#print axioms valid_packet_clock_le

end CurrentAdditive.CodeDUpdateUnivariateClock
