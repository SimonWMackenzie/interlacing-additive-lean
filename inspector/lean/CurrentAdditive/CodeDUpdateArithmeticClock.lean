import CurrentAdditive.CodeDUpdateFullPipeline
import EthInapproximability.CurrentPaper.SourceListMachineWork
import EthInapproximability.CurrentPaper.UnaryBinaryEncoding

/-! Polynomial envelopes for the physical arithmetic callback and ordered map. -/

namespace CurrentAdditive.CodeDUpdateArithmeticClock

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication

noncomputable def productTimeBound (L : Nat) : Nat :=
  CodeDUpdateProductPolytime.coefficient *
    (L+1)^CodeDUpdateProductPolytime.exponent

noncomputable def productWordBound (L : Nat) : Nat :=
  L + productTimeBound L * CodeDUpdateProductPolytime.machine.pushBound

noncomputable def productFrameTimeBound (L : Nat) : Nat :=
  productTimeBound L + 6*productWordBound L+6

noncomputable def productFrameOutputBound (L : Nat) : Nat :=
  2*productWordBound L+1

theorem product_time_le (x : List Bool) (L : Nat) (hL : x.length ≤ L) :
    CodeDUpdateProductPolytime.coefficient *
      (x.length+1)^CodeDUpdateProductPolytime.exponent ≤
      productTimeBound L := by
  unfold productTimeBound
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

theorem product_word_length_le (x : List Bool) (L : Nat)
    (hL : x.length ≤ L) :
    (CodeDUpdateProductFramed.productWord x).length ≤
      productWordBound L := by
  have ho := BitMachine.output_length_bound
    CodeDUpdateProductPolytime.machine
    (CodeDUpdateProductPolytime.outputs x)
  have ht := product_time_le x L hL
  have hm := Nat.mul_le_mul_right
    CodeDUpdateProductPolytime.machine.pushBound ht
  unfold productWordBound
  dsimp only [CodeDUpdateProductFramed.productWord,
    CodeDUpdateProductPolytime.outputs, Function.comp_apply] at *
  omega

theorem product_frame_clock_le (x : List Bool) (L : Nat)
    (hL : x.length ≤ L) :
    CodeDUpdateProductFramed.clock x ≤ productFrameTimeBound L := by
  have ht := product_time_le x L hL
  have hw := product_word_length_le x L hL
  unfold CodeDUpdateProductFramed.clock productFrameTimeBound
  omega

theorem product_frame_output_length_le (x : List Bool) (L : Nat)
    (hL : x.length ≤ L) :
    (CodeDUpdateProductFramed.result x).length ≤
      productFrameOutputBound L := by
  have hw := product_word_length_le x L hL
  unfold CodeDUpdateProductFramed.result productFrameOutputBound
  rw [field_length]
  omega

theorem old_weight_clock_le (x : List Bool) :
    CodeDUpdateSourceFields.oldWeightClock x ≤ 40*(x.length+1) := by
  have he := BankFieldProjection.result_length (0 : Fin 3) x
  have hce : (CodeDUpdateSourceFields.oldEntryWord x).length ≤ x.length := by
    simpa only [CodeDUpdateSourceFields.oldEntryWord] using he
  have hw := BankFieldProjection.result_length (1 : Fin 2)
    (CodeDUpdateSourceFields.oldEntryWord x)
  have hEq :
      (BankFieldProjection.result (1 : Fin 2)
        (CodeDUpdateSourceFields.oldEntryWord x)).length =
      (BankFieldProjection.result (1 : Fin 2)
        (BankFieldProjection.result (0 : Fin 3) x)).length := rfl
  have hd :
      (BankFieldProjection.result (1 : Fin 2)
        (CodeDUpdateSourceFields.oldEntryWord x)).length ≤ x.length := by
    exact le_trans hw (by simpa only [CodeDUpdateSourceFields.oldEntryWord] using he)
  unfold CodeDUpdateSourceFields.oldWeightClock
    CodeDUpdateSourceFields.oldWeightWord
  omega

theorem old_entry_clock_le (x : List Bool) :
    CodeDUpdateSourceFields.oldEntryClock x ≤ 20*(x.length+1) := by
  have he := BankFieldProjection.result_length (0 : Fin 3) x
  unfold CodeDUpdateSourceFields.oldEntryClock
    CodeDUpdateSourceFields.oldEntryWord at *
  omega

theorem old_weight_field_length_le (x : List Bool) :
    (CodeDUpdateSourceFields.oldWeightField x).length ≤ 2*x.length+1 := by
  have he := BankFieldProjection.result_length (0 : Fin 3) x
  have hw := BankFieldProjection.result_length (1 : Fin 2)
    (CodeDUpdateSourceFields.oldEntryWord x)
  unfold CodeDUpdateSourceFields.oldWeightField
    CodeDUpdateSourceFields.oldWeightWord
    CodeDUpdateSourceFields.oldEntryWord at *
  rw [field_length]
  omega

theorem old_entry_field_length_le (x : List Bool) :
    (CodeDUpdateSourceFields.oldEntryField x).length ≤ 2*x.length+1 := by
  have he := BankFieldProjection.result_length (0 : Fin 3) x
  unfold CodeDUpdateSourceFields.oldEntryField
    CodeDUpdateSourceFields.oldEntryWord at *
  rw [field_length]
  omega

noncomputable def subtractPairTimeBound (L : Nat) : Nat :=
  2*L+2+1+40*(L+1)+1+productFrameTimeBound L+
    2*productFrameOutputBound L+2+2*(2*L+1)+2+1

theorem subtract_pair_clock_le (x : List Bool) (L : Nat)
    (hL : x.length ≤ L) :
    CodeDUpdateSubtractPairJoin.clock x ≤ subtractPairTimeBound L := by
  have hw := old_weight_clock_le x
  have hp := product_frame_clock_le x L hL
  have hpf := product_frame_output_length_le x L hL
  have hfw := old_weight_field_length_le x
  unfold CodeDUpdateSubtractPairJoin.clock subtractPairTimeBound
  omega

noncomputable def subtractPairOutputBound (L : Nat) : Nat :=
  L + subtractPairTimeBound L * CodeDUpdateSubtractPairJoin.machine.pushBound

theorem subtract_pair_output_length_le (x : List Bool) (L : Nat)
    (hL : x.length ≤ L) :
    (CodeDUpdateSubtractPairJoin.output x).length ≤
      subtractPairOutputBound L := by
  have ho := BitMachine.output_length_bound
    CodeDUpdateSubtractPairJoin.machine
    (CodeDUpdateSubtractPairJoin.outputs x)
  have ht := subtract_pair_clock_le x L hL
  have hm := Nat.mul_le_mul_right
    CodeDUpdateSubtractPairJoin.machine.pushBound ht
  unfold subtractPairOutputBound
  omega

noncomputable def subtractTimeBound (L : Nat) : Nat :=
  RationalSubtractCanonical.coefficient *
    (subtractPairOutputBound L+1)^RationalSubtractCanonical.exponent

theorem subtract_time_le (x : List Bool) (L : Nat)
    (hL : x.length ≤ L) :
    RationalSubtractCanonical.coefficient *
      ((CodeDUpdateSubtractPairJoin.output x).length+1)^
        RationalSubtractCanonical.exponent ≤ subtractTimeBound L := by
  unfold subtractTimeBound
  have ho := subtract_pair_output_length_le x L hL
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

noncomputable def differenceWordBound (L : Nat) : Nat :=
  subtractPairOutputBound L +
    subtractTimeBound L * RationalSubtractCanonical.machine.pushBound

theorem difference_word_length_le (x : List Bool) (L : Nat)
    (hL : x.length ≤ L) :
    (CodeDUpdateDifferenceFramed.differenceWord x).length ≤
      differenceWordBound L := by
  have ho := BitMachine.output_length_bound
    RationalSubtractCanonical.machine
    (RationalSubtractCanonical.outputsWithin
      (CodeDUpdateSubtractPairJoin.output x))
  have hp := subtract_pair_output_length_le x L hL
  have ht := subtract_time_le x L hL
  have hm := Nat.mul_le_mul_right
    RationalSubtractCanonical.machine.pushBound ht
  unfold differenceWordBound
  dsimp only [CodeDUpdateDifferenceFramed.differenceWord] at *
  omega

noncomputable def differenceFrameTimeBound (L : Nat) : Nat :=
  subtractPairTimeBound L + 2*subtractPairOutputBound L+2 +
    subtractTimeBound L + 6*differenceWordBound L+6

theorem difference_frame_clock_le (x : List Bool) (L : Nat)
    (hL : x.length ≤ L) :
    CodeDUpdateDifferenceFramed.clock x ≤
      differenceFrameTimeBound L := by
  have hp := subtract_pair_clock_le x L hL
  have ho := subtract_pair_output_length_le x L hL
  have ht := subtract_time_le x L hL
  have hw := difference_word_length_le x L hL
  unfold CodeDUpdateDifferenceFramed.clock differenceFrameTimeBound
  omega

noncomputable def differenceFrameOutputBound (L : Nat) : Nat :=
  2*differenceWordBound L+1

theorem difference_frame_output_length_le (x : List Bool) (L : Nat)
    (hL : x.length ≤ L) :
    (CodeDUpdateDifferenceFramed.result x).length ≤
      differenceFrameOutputBound L := by
  have hw := difference_word_length_le x L hL
  unfold CodeDUpdateDifferenceFramed.result differenceFrameOutputBound
  rw [field_length]
  omega

noncomputable def finalItemTimeBound (L : Nat) : Nat :=
  2*L+2+1+20*(L+1)+1+differenceFrameTimeBound L+
    2*differenceFrameOutputBound L+2+2*(2*L+1)+2+1

theorem final_item_clock_le (x : List Bool) (L : Nat)
    (hL : x.length ≤ L) :
    CodeDUpdateFinalPairJoin.clock x ≤ finalItemTimeBound L := by
  have he := old_entry_clock_le x
  have hd := difference_frame_clock_le x L hL
  have hdo := difference_frame_output_length_le x L hL
  have hfo := old_entry_field_length_le x
  unfold CodeDUpdateFinalPairJoin.clock finalItemTimeBound
  omega

noncomputable def finalItemOutputBound (L : Nat) : Nat :=
  L + finalItemTimeBound L * CodeDUpdateFinalPairJoin.machine.pushBound

theorem final_item_output_length_le (x : List Bool) (L : Nat)
    (hL : x.length ≤ L) :
    (CodeDUpdateFinalPairJoin.output x).length ≤
      finalItemOutputBound L := by
  have ho := BitMachine.output_length_bound
    CodeDUpdateFinalPairJoin.machine (CodeDUpdateFinalPairJoin.outputs x)
  have ht := final_item_clock_le x L hL
  have hm := Nat.mul_le_mul_right CodeDUpdateFinalPairJoin.machine.pushBound ht
  unfold finalItemOutputBound
  omega

noncomputable def frameBound (L : Nat) : Nat :=
  3*finalItemOutputBound L+1

noncomputable def timeBound (L : Nat) : Nat :=
  finalItemTimeBound L+2*finalItemOutputBound L+2+
    (UnaryBinaryEncoding.coefficient+7)*(finalItemOutputBound L+1)^2

private noncomputable def F :=
  SourceListMachineOuterFramed.itemMachine CodeDUpdateFinalPairJoin.machine

noncomputable def itemEnvelope (L : Nat) : Nat :=
  20*(L+1)*(L+1)+timeBound L+4*L+frameBound L+
    F.stackCount*(L+timeBound L*F.pushBound+1)+9

noncomputable def polynomialClock (N L : Nat) : Nat :=
  N*(itemEnvelope L+4*(N+1)+7+frameBound L)+11*(N+1)+17

theorem framed_length_le (x : List Bool) (L : Nat)
    (hL : x.length ≤ L) :
    (SourceListMachineOuterFramed.framedOutput
      CodeDUpdateFinalPairJoin.output x).length ≤ frameBound L := by
  have hr := final_item_output_length_le x L hL
  have hf := EncodedGraph.natField_length_upper
    (CodeDUpdateFinalPairJoin.output x).length
  unfold SourceListMachineOuterFramed.framedOutput frameBound
  simp only [List.length_append]
  omega

theorem framed_time_le (x : List Bool) (L : Nat)
    (hL : x.length ≤ L) :
    SourceListMachineOuterFramed.framedBound
      CodeDUpdateFinalPairJoin.output CodeDUpdateFinalPairJoin.clock x ≤
      timeBound L := by
  have hc := final_item_clock_le x L hL
  have hr := final_item_output_length_le x L hL
  have hp : ((CodeDUpdateFinalPairJoin.output x).length+1)^2 ≤
      (finalItemOutputBound L+1)^2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hp' := Nat.mul_le_mul_left
    (UnaryBinaryEncoding.coefficient+7) hp
  unfold SourceListMachineOuterFramed.framedBound timeBound
  omega

theorem clock_le_polynomial (requests : List (List Bool)) (L : Nat)
    (hL : ∀ x ∈ requests, x.length ≤ L) :
    CodeDUpdateFinalPairList.clock requests ≤
      polynomialClock requests.length L := by
  have hitem : ∀ x ∈ requests,
      SourceListMachineWork.itemCost F x
        (SourceListMachineOuterFramed.framedOutput
          CodeDUpdateFinalPairJoin.output x)
        (SourceListMachineOuterFramed.framedBound
          CodeDUpdateFinalPairJoin.output CodeDUpdateFinalPairJoin.clock x) ≤
        itemEnvelope L := by
    intro x hx
    exact SourceListMachineWork.itemCost_le_envelope F x _ _ L
      (frameBound L) (timeBound L) (hL x hx)
      (framed_length_le x L (hL x hx))
      (framed_time_le x L (hL x hx))
  have hout : ∀ x ∈ requests,
      (SourceListMachineOuterFramed.framedOutput
        CodeDUpdateFinalPairJoin.output x).length ≤ frameBound L := by
    intro x hx
    exact framed_length_le x L (hL x hx)
  have hdigits : requests.length.bits.length ≤ requests.length+1 := by
    have hb := UnaryBinaryEncoding.bits_length_le requests.length
    omega
  have h := SourceListMachineOuter.canonicalBound_le_source F requests
    (SourceListMachineOuterFramed.framedOutput CodeDUpdateFinalPairJoin.output)
    (SourceListMachineOuterFramed.framedBound
      CodeDUpdateFinalPairJoin.output CodeDUpdateFinalPairJoin.clock)
    requests.length (fun n => n) (fun n => n+1)
    (fun _ => itemEnvelope L) (fun _ => frameBound L)
    (le_refl _) hdigits hitem hout
  simpa only [CodeDUpdateFinalPairList.clock, polynomialClock] using h

noncomputable def fullPipelineBound (N L : Nat) : Nat :=
  polynomialClock N L +
    2*CodeDCompactClockV2.inputBound N (finalItemOutputBound L)+2 +
    CodeDUpdatedEntryClockV2.pipelineClock N (finalItemOutputBound L)

theorem full_pipeline_clock_le {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ)
    (lambda : ℚ) (L : Nat)
    (hL : ∀ x ∈ CodeDUpdateRequestABI.requestItems source coeff lambda,
      x.length ≤ L) :
    CodeDUpdateFullPipeline.clock source coeff lambda ≤
      fullPipelineBound
        (CodeDUpdateRequestABI.requestItems source coeff lambda).length L := by
  let requests := CodeDUpdateRequestABI.requestItems source coeff lambda
  let updated := CodeDUpdatedArithmeticABI.candidateWeights source coeff lambda
  let pairs := CodeDUpdatedEntryList.pairItems source updated
  have hmap := CodeDUpdateFinalPairList.request_map_exact source coeff lambda
  rw [CodeDUpdateFinalPairList.expectedPairs_eq_pairItems] at hmap
  have hsize : pairs.length = requests.length := by
    have hh := congrArg List.length hmap
    simpa only [requests, pairs, List.length_map] using hh.symm
  have hpair : ∀ x ∈ pairs, x.length ≤ finalItemOutputBound L := by
    intro x hx
    change x ∈ CodeDUpdatedEntryList.pairItems source updated at hx
    rw [← hmap] at hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    exact final_item_output_length_le r L (hL r hr)
  have hfirst := clock_le_polynomial requests L hL
  have hmiddle := CodeDCompactClockV2.input_length_le pairs
    (finalItemOutputBound L) hpair
  have hlast := CodeDUpdatedEntryClockV2.pipeline_clock_le
    source updated (finalItemOutputBound L) hpair
  rw [hsize] at hmiddle hlast
  change CodeDUpdateFinalPairList.clock requests +
      2*(CodeDCodecV2.encodeItems pairs).length+2 +
      CodeDUpdatedCompactPipeline.clock source updated ≤
    polynomialClock requests.length L +
      2*CodeDCompactClockV2.inputBound requests.length
        (finalItemOutputBound L)+2 +
      CodeDUpdatedEntryClockV2.pipelineClock requests.length
        (finalItemOutputBound L)
  omega

#print axioms product_frame_clock_le
#print axioms product_frame_output_length_le
#print axioms difference_frame_clock_le
#print axioms difference_frame_output_length_le
#print axioms final_item_clock_le
#print axioms final_item_output_length_le
#print axioms clock_le_polynomial
#print axioms full_pipeline_clock_le

end CurrentAdditive.CodeDUpdateArithmeticClock
