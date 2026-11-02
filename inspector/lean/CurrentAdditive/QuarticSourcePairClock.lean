import CurrentAdditive.QuarticSourceCutInst
import CurrentAdditive.QuarticPairClockBound

/-! The exact pair-front clock on a public bank, with every charged word visible. -/

namespace Paper2.CurrentAdditive.QuarticSourcePairClock

open Paper2 Paper2.A3Assembly Paper2.Unit4Shell.T10Finite
open Paper2.Unit4Shell.Asymptotics
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2.CurrentAdditive.QuarticSourceCutInst
open Paper2.CurrentAdditive.QuarticSourceCutClock
open Paper2.CurrentAdditive.QuarticPairClockBound
open Paper2.CurrentAdditive.QuarticTMClockRepair

noncomputable section
set_option maxHeartbeats 8000000

theorem source_pair_front_clock
    (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))
    (Φ : ValidFormula) (raw : List Bool) (Y : Fin 3 → List Bool)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin (t10Graph D B Φ).vertices)
      (Edges := Fin (t10Graph D B Φ).edges.length)
      (Nat.clog 2 (t10Graph D B Φ).vertices)
      B.degreeBound (sourceGap D B)) :
    let g := t10Graph D B Φ
    let k := kOf Φ.val.variables
    let I := (BitMachineBankCodec.encode (FullFront.X0 g k raw)).length
    let O := (BitMachineBankCodec.encode Y).length
    let Praw := (g.vertices + 2) ^
      (rawExponent B.degreeBound (sourceGap D B) * (k + 1))
    let Pcut := (g.vertices + 2) ^ (360 * (k + 1))
    let S := Praw + Pcut + (EncodedGraph.encode g).length + k + raw.length + O + 1
    let Tcut := QuarticOuterMachine.cutClock (FullFront.X0 g k raw) Y
      (QuarticOuterUniform.localCap g B.degreeBound (sourceGap D B) k raw
        (QuarticUniformInputCap.inputCap g B.degreeBound
          (sourceGap D B) k raw.length))
    let Z := (EncodedCNF.encode Φ.val).length +
      QuarticUniformInputCap.inputCap g B.degreeBound
        (sourceGap D B) k raw.length +
      cutNumericCoefficient B.degreeBound (sourceGap D B) * S +
      O + raw.length + 1
    QuarticPairFront.pairFrontClock D B Φ raw (BitMachineBankCodec.encode Y)
      Tcut ≤
      (QuarticPairFront.frontCoefficient D B + 100) *
        (3 * (Z + 1)) ^ (QuarticPairFront.frontExponent D B + 1) := by
  intro g k I O Praw Pcut S Tcut Z
  have hcut : Tcut ≤
      cutNumericCoefficient B.degreeBound (sourceGap D B) * S :=
    source_cut_clock g B.degreeBound (sourceGap D B) k
      (t10_vertices_pos D B Φ) hc raw Y
  have hI : I ≤ QuarticUniformInputCap.inputCap g B.degreeBound
      (sourceGap D B) k raw.length :=
    QuarticUniformInputCap.encoded_input_le g B.degreeBound
      (sourceGap D B) k raw.length raw (le_refl _)
  apply pair_front_clock_of_atom_cap D B Φ raw (BitMachineBankCodec.encode Y)
    Tcut Z
  all_goals dsimp only [Z, I, O, g, k] at *
  all_goals omega

#print axioms source_pair_front_clock

end
end Paper2.CurrentAdditive.QuarticSourcePairClock
