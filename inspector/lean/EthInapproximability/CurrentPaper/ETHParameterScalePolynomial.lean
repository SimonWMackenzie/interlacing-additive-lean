import EthInapproximability.CurrentPaper.ETHParameterScaleActual

/-! Coarse input-only polynomial clock for the physical six-raw-word scale
controller. No promise on the input values is needed. -/

namespace EthInapproximability.CurrentPaper.ETHScalePolynomialClock

open ETHScaleActualComplete

noncomputable section

set_option maxHeartbeats 1000000

def rawMax (i : Parameters.Input) : ℕ :=
  max i.sourceConstant (max i.nextDepth (max i.cost
    (max i.rows (max i.columns i.edges))))

def width (i : Parameters.Input) : ℕ := rawMax i + 4

theorem rawMax_eq_initial_word_lengths (i : Parameters.Input) :
    rawMax i =
      max (ETHParameterScaleMachineInput.words i 0).length
        (max (ETHParameterScaleMachineInput.words i 1).length
          (max (ETHParameterScaleMachineInput.words i 2).length
            (max (ETHParameterScaleMachineInput.words i 3).length
              (max (ETHParameterScaleMachineInput.words i 4).length
                (ETHParameterScaleMachineInput.words i 5).length)))) := by
  simp [rawMax,ETHParameterScaleMachineInput.words]

private theorem field_le (i : Parameters.Input) :
    i.sourceConstant ≤ rawMax i ∧ i.nextDepth ≤ rawMax i ∧
    i.cost ≤ rawMax i ∧ i.rows ≤ rawMax i ∧
    i.columns ≤ rawMax i ∧ i.edges ≤ rawMax i := by
  dsimp [rawMax]
  omega

private theorem clog_self (n : ℕ) : Nat.clog 2 n ≤ n := by
  apply Nat.clog_le_of_le_pow
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    have hp : 0 < 2 ^ n := pow_pos (by omega : 0 < (2 : ℕ)) _
    omega

private theorem input_le (i : Parameters.Input) :
    i.sourceConstant ≤ width i ∧ i.nextDepth ≤ width i ∧
    i.cost ≤ width i ∧ i.rows ≤ width i ∧
    i.columns ≤ width i ∧ i.edges + 2 ≤ width i ∧
    Nat.clog 2 i.rows ≤ width i ∧
    Nat.clog 2 i.columns ≤ width i ∧
    Nat.clog 2 (i.edges+2) ≤ width i ∧
    Parameters.scaleBound i ≤ width i ∧
    Nat.clog 2 (Parameters.scaleBound i) ≤ width i := by
  obtain ⟨hs,hd,hc,hr,hcol,he⟩ := field_le i
  have hlr := clog_self i.rows
  have hlc := clog_self i.columns
  have hle := clog_self (i.edges+2)
  have hsb : Parameters.scaleBound i ≤ width i := by
    simp only [Parameters.scaleBound, Parameters.namingLength,
      max_le_iff]
    repeat' constructor <;> dsimp [width] <;> omega
  have hls := clog_self (Parameters.scaleBound i)
  dsimp [width] at hsb ⊢
  omega

def logEnvelope (w : ℕ) : ℕ :=
  2*w+2 + (UnaryBinaryEncoding.coefficient+6)*(w+1)^2

private theorem logCost_le (n w : ℕ) (h : n ≤ w) :
    ETHScaleColumnCandidate.logCost n ≤ logEnvelope w := by
  dsimp [ETHScaleColumnCandidate.logCost,logEnvelope]
  gcongr

private theorem finalLogCost_le (n w : ℕ) (h : n ≤ w) :
    ScaleFinalScratch.logCost n ≤ logEnvelope w := by
  dsimp [ScaleFinalScratch.logCost,logEnvelope]
  gcongr

private theorem threeBound_le (i : Parameters.Input) :
    ETHScaleGlobalLog.threeBound i ≤
      3*logEnvelope (width i) + 8*width i + 17 := by
  obtain ⟨_,_,_,hr,hcol,he,hlr,hlc,hle,_,_⟩ := input_le i
  have hleCost := logCost_le (i.edges+2) (width i) he
  have hlcCost := logCost_le i.columns (width i) hcol
  have hlrCost := logCost_le i.rows (width i) hr
  have he0 : i.edges ≤ width i := by omega
  dsimp [ETHScaleGlobalLog.threeBound,
    ETHScaleGlobalLog.edgeBound,ETHScaleGlobalLog.simpleBound]
  omega

private theorem candidateBound_le (i : Parameters.Input) :
    ETHScaleCandidateProducer.candidateBound i ≤
      3*logEnvelope (width i) + 14*width i + 26 := by
  have hg := threeBound_le i
  obtain ⟨hs,hd,hc,_,_,_,_,_,_,_,_⟩ := input_le i
  dsimp [ETHScaleCandidateProducer.candidateBound]
  omega

private theorem foldVal_le (i : Parameters.Input) (j : Fin 7) :
    ScaleMaxFoldScratch.foldVal i j ≤ width i := by
  obtain ⟨hs,hd,hc,_,_,_,hlr,hlc,hle,_,_⟩ := input_le i
  have hw : 2 ≤ width i := by dsimp [width]; omega
  fin_cases j <;>
    simp only [ScaleMaxFoldScratch.foldVal,
      ETHParameterScaleMachineInput.candidates,
      List.take, List.foldl] <;>
    omega

private theorem foldCost_le (i : Parameters.Input) :
    ScaleMaxFoldScratch.totalCost i ≤ 6*(width i+1) := by
  have h0 := foldVal_le i 1
  have h1 := foldVal_le i 2
  have h2 := foldVal_le i 3
  have h3 := foldVal_le i 4
  have h4 := foldVal_le i 5
  have h5 := foldVal_le i 6
  dsimp [ScaleMaxFoldScratch.totalCost,ScaleMaxFoldScratch.phaseCost]
  omega

private theorem oldBound_le (i : Parameters.Input) :
    ETHScaleActualScaleBound.totalBound i ≤
      3*logEnvelope (width i) + 20*width i + 33 := by
  have hc := candidateBound_le i
  have hf := foldCost_le i
  dsimp [ETHScaleActualScaleBound.totalBound]
  omega

def preEnvelope (w : ℕ) : ℕ :=
  logEnvelope w + w + 2*ScaleFinalScratch.floorSize + 10

private theorem preCost_le (i : Parameters.Input) :
    ScaleFinalScratch.preCost (Parameters.scaleBound i) ≤
      preEnvelope (width i) := by
  obtain ⟨_,_,_,_,_,_,_,_,_,hs,hl⟩ := input_le i
  have hc := finalLogCost_le (Parameters.scaleBound i) (width i) hs
  have hm : max (Nat.clog 2 (Parameters.scaleBound i))
      ScaleFinalScratch.floorSize ≤ width i + ScaleFinalScratch.floorSize := by
    omega
  dsimp [ScaleFinalScratch.preCost,preEnvelope]
  omega

def polynomialClock (w : ℕ) : ℕ :=
  (3*logEnvelope w + 20*w + 33) +
  ((1 + ScaleFinalScratch.cleanupCount *
      BitMachineStackGrowth.perStep ScaleFinalScratch.program) *
    preEnvelope w + ScaleFinalScratch.cleanupCount + 2) + 1

/-- An explicit degree-two polynomial in the maximum initial raw unary word
length. Every coefficient is a fixed finite-controller constant, including
the floor emitter. -/
theorem totalBound_le_polynomial (i : Parameters.Input) :
    ETHScaleActualComplete.totalBound i ≤ polynomialClock (width i) := by
  have ho := oldBound_le i
  have hp := preCost_le i
  have hf : ScaleFinalScratch.inputClock (Parameters.scaleBound i) ≤
      (1 + ScaleFinalScratch.cleanupCount *
        BitMachineStackGrowth.perStep ScaleFinalScratch.program) *
        preEnvelope (width i) + ScaleFinalScratch.cleanupCount + 2 := by
    calc
      _ = (1 + ScaleFinalScratch.cleanupCount *
          BitMachineStackGrowth.perStep ScaleFinalScratch.program) *
          ScaleFinalScratch.preCost (Parameters.scaleBound i) +
          ScaleFinalScratch.cleanupCount + 2 := by
            dsimp [ScaleFinalScratch.inputClock]
            ring
      _ ≤ _ := by gcongr
  dsimp [ETHScaleActualComplete.totalBound,polynomialClock]
  omega

theorem actual_scale_run_polynomial (i : Parameters.Input) :
    ∃ t ≤ polynomialClock (width i), ∃ F : ETHScaleActualComplete.Stack → List Bool,
      ((BitMachineEncoding.advance ETHScaleActualComplete.program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel ETHScaleActualComplete.oldStart),
          (ETHScaleActualComplete.oldControl,ETHScaleActualComplete.finalControl),
          ETHScaleActualComplete.initialBank i⟩ :
          Turing.TM2.Cfg (fun _ : ETHScaleActualComplete.Stack => Bool)
            ETHScaleActualComplete.Label ETHScaleActualComplete.Control) =
        ⟨none,(ETHScaleActualComplete.oldControl,ScaleFinalScratch.base,none),F⟩ ∧
      F (.inr ScaleFinalScratch.answerKey) =
        List.replicate (Parameters.scale i) true ∧
      F (.inl (ETHScaleGlobalLog.tail 12)) =
        List.replicate (Parameters.scaleBound i) true ∧
      (∀ j : Fin 6, F (.inl (ETHScaleGlobalLog.raw j)) =
        ETHParameterScaleMachineInput.words i j) := by
  obtain ⟨t,ht,F,hr,ha,hs,hraw⟩ := ETHScaleActualComplete.actual_scale_run i
  exact ⟨t,ht.trans (totalBound_le_polynomial i),F,hr,ha,hs,hraw⟩

end
end EthInapproximability.CurrentPaper.ETHScalePolynomialClock
