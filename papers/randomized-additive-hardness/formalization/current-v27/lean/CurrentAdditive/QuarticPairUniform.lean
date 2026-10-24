import CurrentAdditive.QuarticPairFront
import CurrentAdditive.QuarticOuterUniform

/-! The fixed formula-preserving v27 bank front with a witness-free input cap. -/

namespace Paper2.CurrentAdditive.QuarticPairUniform

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2 Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics
open Paper2.CurrentAdditive.QuarticPairFront
open Paper2.CurrentAdditive.QuarticNumericFront

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

theorem pair_front_outputs_uniform (Φ : ValidFormula) (raw : List Bool)
    (Z : ℕ) (hZ : 1 ≤ Z)
    (hP : (BitMachineBankCodec.encode
      (FullFront.X0 (t10Graph D B Φ) (kOf Φ.val.variables) raw)).length ≤ Z)
    (hRaw : Raw27.clock (t10Graph D B Φ) B.degreeBound
      (sourceGap D B) (kOf Φ.val.variables) raw ≤ Z) :
    let E := EncodedCNF.encode Φ.val
    let g := t10Graph D B Φ
    let k := kOf Φ.val.variables
    let Y := QuarticCutOutputCopies.outPacket g k
      (raw.take (QuarticCutCount.count27 g.vertices g.edges.length
        (Nat.clog 2 g.vertices) B.degreeBound (sourceGap D B) k))
    (pairFrontMachine D B).OutputsWithin
      (EncodedComplexity.pair E raw)
      (EncodedComplexity.pair E (BitMachineBankCodec.encode Y))
      (pairFrontClock D B Φ raw (BitMachineBankCodec.encode Y)
        (QuarticOuterMachine.cutClock (FullFront.X0 g k raw) Y
          (QuarticOuterUniform.localCap g B.degreeBound (sourceGap D B) k raw Z))) := by
  intro E g k Y
  have hF := front_outputs D B Φ raw
  have hC := QuarticOuterUniform.cut_machine_outputs_uniform
    g (t10Graph_valid D B Φ) B.degreeBound (sourceGap D B)
    (source_gap_pos D B) B.degreeBound_pos
    (t10_vertices_pos D B Φ) (t10_source D B Φ).1 k raw Z hZ hP hRaw
  let inWord := EncodedComplexity.pair E raw
  let outWord := BitMachineBankCodec.encode Y
  let frontTime := frontCoefficient D B * (inWord.length + 1) ^ frontExponent D B
  let cutTime := QuarticOuterMachine.cutClock (FullFront.X0 g k raw) Y
    (QuarticOuterUniform.localCap g B.degreeBound (sourceGap D B) k raw Z)
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
  apply BitMachine.outputsWithin_mono _ hAll
  unfold pairFrontClock
  dsimp only [inWord, outWord, frontTime, cutTime, E, g, k]
  omega

#print axioms pair_front_outputs_uniform

end
end Paper2.CurrentAdditive.QuarticPairUniform
