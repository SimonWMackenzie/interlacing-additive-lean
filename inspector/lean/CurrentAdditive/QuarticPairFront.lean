import CurrentAdditive.QuarticOuterMachine
import CurrentAdditive.QuarticSecondFieldMap
import Paper2.A4Kof

/-! A single fixed bit machine retains the encoded formula while constructing
the v27 numeric input bank from an arbitrary raw suffix. -/

namespace Paper2.CurrentAdditive.QuarticPairFront

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2 Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics
open Paper2.CurrentAdditive.QuarticOuterMachine

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

def frontMachine : BitMachine.Machine :=
  Classical.choose (Paper2.Unit4Shell.KofFront.front_T24_raw D B)
def frontCoefficient : ℕ :=
  Classical.choose (Classical.choose_spec
    (Paper2.Unit4Shell.KofFront.front_T24_raw D B))
def frontExponent : ℕ :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Paper2.Unit4Shell.KofFront.front_T24_raw D B)))

theorem front_outputs (Φ : ValidFormula) (raw : List Bool) :
    (frontMachine D B).OutputsWithin
      (EncodedComplexity.pair (EncodedCNF.encode Φ.val) raw)
      (BitMachineBankCodec.encode
        (FullFront.X0 (t10Graph D B Φ) (kOf Φ.val.variables) raw))
      (frontCoefficient D B *
        ((EncodedComplexity.pair (EncodedCNF.encode Φ.val) raw).length + 1) ^
          frontExponent D B) := by
  simpa only [frontMachine, frontCoefficient, frontExponent, FullFront.X0] using
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (Paper2.Unit4Shell.KofFront.front_T24_raw D B))) Φ raw)

def bankFrontMachine : BitMachine.Machine :=
  BitMachineComposition.composition (frontMachine D B)
    (QuarticOuterMachine.cutMachine B.degreeBound (sourceGap D B))

def pairFrontMachine : BitMachine.Machine :=
  BitMachineComposition.composition Paper2.Unit4Shell.KofLoops.DupField.machine
    (QuarticSecondFieldMap.machine (bankFrontMachine D B))

def pairFrontClock (Φ : ValidFormula) (raw output : List Bool)
    (cutTime : ℕ) : ℕ :=
  let E := EncodedCNF.encode Φ.val
  let input := EncodedComplexity.pair E raw
  let frontTime := frontCoefficient D B * (input.length + 1) ^ frontExponent D B
  6 * (input.length + 1) +
    2 * (EncodedComplexity.pair E input).length + 2 +
    (2 * E.length + 2 * input.length +
      (frontTime + 2 * (BitMachineBankCodec.encode
        (FullFront.X0 (t10Graph D B Φ) (kOf Φ.val.variables) raw)).length + 2 + cutTime) +
      2 * output.length + 2 * E.length + 11)

theorem pair_front_outputs (Φ : ValidFormula) (raw : List Bool) :
    let E := EncodedCNF.encode Φ.val
    let g := t10Graph D B Φ
    let k := kOf Φ.val.variables
    let Y := QuarticCutOutputCopies.outPacket g k
      (raw.take (QuarticCutCount.count27 g.vertices g.edges.length
        (Nat.clog 2 g.vertices) B.degreeBound (sourceGap D B) k))
    ∃ Bwork : QuarticFrontLift.FS → List Bool,
      ∃ H : SamplerParameterBank.Stack → List Bool,
      (pairFrontMachine D B).OutputsWithin
        (EncodedComplexity.pair E raw)
        (EncodedComplexity.pair E (BitMachineBankCodec.encode Y))
        (pairFrontClock D B Φ raw (BitMachineBankCodec.encode Y)
          (QuarticOuterMachine.cutClock (FullFront.X0 g k raw) Y
            (QuarticOuterMachine.localBudget g B.degreeBound
              (sourceGap D B) k raw Bwork H))) := by
  intro E g k Y
  have hF := front_outputs D B Φ raw
  obtain ⟨Bwork, H, hC⟩ := QuarticOuterMachine.cut_machine_outputs
    g (t10Graph_valid D B Φ) B.degreeBound (sourceGap D B)
    (source_gap_pos D B) B.degreeBound_pos
    (t10_vertices_pos D B Φ) (t10_source D B Φ).1 k raw
  let inWord := EncodedComplexity.pair E raw
  let outWord := BitMachineBankCodec.encode Y
  let frontTime := frontCoefficient D B * (inWord.length + 1) ^ frontExponent D B
  let cutTime := QuarticOuterMachine.cutClock (FullFront.X0 g k raw) Y
    (QuarticOuterMachine.localBudget g B.degreeBound (sourceGap D B) k raw Bwork H)
  have hFC : (bankFrontMachine D B).OutputsWithin inWord outWord
      (frontTime + 2 * (BitMachineBankCodec.encode
        (FullFront.X0 g k raw)).length + 2 + cutTime) := by
    simpa only [bankFrontMachine, inWord, outWord, frontTime, cutTime, g, k, Y] using
      (BitMachineComposition.composition_outputsWithin _ _
      (by simpa only [inWord, frontTime, g, k] using hF)
      (by simpa only [cutTime, outWord, g, k] using hC))
  have hDup := Paper2.Unit4Shell.KofLoops.DupField.machine_outputs E raw
  have hMap := QuarticSecondFieldMap.machine_outputs
    (bankFrontMachine D B) E inWord outWord
    (frontTime + 2 * (BitMachineBankCodec.encode
      (FullFront.X0 g k raw)).length + 2 + cutTime) hFC
  have hAll := BitMachineComposition.composition_outputsWithin _ _ hDup hMap
  refine ⟨Bwork, H, ?_⟩
  apply BitMachine.outputsWithin_mono _ hAll
  unfold pairFrontClock
  dsimp only [inWord, outWord, frontTime, cutTime, E, g, k]
  omega

#print axioms pair_front_outputs

end
end Paper2.CurrentAdditive.QuarticPairFront
