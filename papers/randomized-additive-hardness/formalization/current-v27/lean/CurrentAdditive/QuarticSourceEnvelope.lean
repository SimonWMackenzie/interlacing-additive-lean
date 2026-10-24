import CurrentAdditive.QuarticSourceAtomFit
import CurrentAdditive.QuarticSourcePairClock

/-! The exact source front atoms fit one fixed multiple of expLen N. -/

namespace Paper2.CurrentAdditive.QuarticSourceEnvelope

open Paper2 Paper2.CurrentAdditive.QuarticConstructor
open Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2.CurrentAdditive.QuarticSourceAtomFit
open Paper2.CurrentAdditive.QuarticSourceCutClock
open Paper2.CurrentAdditive.QuarticTMClockRepair
open Paper2.CurrentAdditive.QuarticClassEndpoint

noncomputable section
set_option maxHeartbeats 8000000

def bankLinearCoefficient (Δ : ℕ) : ℕ := 4 * Δ + 9
def sumLinearCoefficient (Δ : ℕ) : ℕ := 2 * bankLinearCoefficient Δ + 8
def capLinearCoefficient (Δ : ℕ) (γ : ℚ) : ℕ :=
  2 * bankLinearCoefficient Δ + 14 + 6 * rawCoefficient Δ γ
def pairLinearCoefficient (Δ : ℕ) (γ : ℚ) : ℕ :=
  1 + capLinearCoefficient Δ γ +
    cutNumericCoefficient Δ γ * sumLinearCoefficient Δ +
    bankLinearCoefficient Δ + 6

theorem source_pair_atoms_linear
    (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))
    (cs : ℕ) :
    ∃ N₀ : ℕ, ∀ Φ : ValidFormula,
      Φ.val.clauses.length ≤ cs * Φ.val.variables →
      N₀ ≤ Φ.val.variables →
      let g := t10Graph D B Φ
      let hg := t10Graph_valid D B Φ
      let hn := t10_vertices_pos D B Φ
      let k := kOf Φ.val.variables
      let U := Paper2.AEth.expLen Φ.val.variables
      ∀ tape : List Bool,
      ∀ t : (select27 hn (CanonicalEdgeTape.graphEdge g hg)
        B.degreeBound (sourceGap D B) k).Tape,
      let raw := tape.take (Paper2.AEth3.cutLen Φ.val)
      let O := (BitMachineBankCodec.encode
        (QuarticDispatchSpec.inputBank27 B.degreeBound (sourceGap D B)
          g hg hn k t)).length
      let Praw := (g.vertices + 2) ^
        (rawExponent B.degreeBound (sourceGap D B) * (k + 1))
      let Pcut := (g.vertices + 2) ^ (360 * (k + 1))
      let S := Praw + Pcut + (EncodedGraph.encode g).length + k + raw.length + O + 1
      let Zpair := (EncodedCNF.encode Φ.val).length +
        QuarticUniformInputCap.inputCap g B.degreeBound
          (sourceGap D B) k raw.length +
        cutNumericCoefficient B.degreeBound (sourceGap D B) * S +
        O + raw.length + 1
      S ≤ sumLinearCoefficient B.degreeBound * U ∧
      Zpair ≤ pairLinearCoefficient B.degreeBound (sourceGap D B) * U := by
  obtain ⟨N₀, hfit⟩ := source_atom_fit D B cs
  refine ⟨N₀, ?_⟩
  intro Φ hsparse hlarge g hg hn k U tape t raw O Praw Pcut S Zpair
  obtain ⟨hX, hraw, hpraw, hpcut, hO⟩ := hfit Φ hsparse hlarge tape t
  have hX' : (EncodedCNF.encode Φ.val).length ≤ U := by
    simpa only [U] using hX
  have hraw' : raw.length ≤ 5 * U := by
    simpa only [raw, U] using hraw
  have hpraw' : Praw ≤ U := by
    simpa only [Praw, g, k, U] using hpraw
  have hpcut' : Pcut ≤ U := by
    simpa only [Pcut, g, k, U] using hpcut
  let Cb := bankLinearCoefficient B.degreeBound
  let a := rawCoefficient B.degreeBound (sourceGap D B)
  have hO' : O ≤ Cb * U := by
    simpa only [Cb, bankLinearCoefficient, O, g, hg, hn, k, U] using hO
  have hGk : (EncodedGraph.encode g).length + k ≤ O := by
    have heq := inputBank_encoded_length27 B.degreeBound (sourceGap D B)
      g hg hn k t
    dsimp only [O, inputBankLength27] at heq ⊢
    omega
  have hU : 1 ≤ U := Nat.one_le_two_pow
  have hS : S ≤ sumLinearCoefficient B.degreeBound * U := by
    calc
      S ≤ 2 * (Cb * U) + 8 * U := by
        dsimp only [S]
        omega
      _ = sumLinearCoefficient B.degreeBound * U := by
        dsimp only [sumLinearCoefficient, Cb]
        ring
  have hCap : QuarticUniformInputCap.inputCap g B.degreeBound
      (sourceGap D B) k raw.length ≤
      capLinearCoefficient B.degreeBound (sourceGap D B) * U := by
    have hpa : Praw + raw.length ≤ 6 * U := by omega
    have hm := Nat.mul_le_mul_left a hpa
    rw [QuarticInputCapAtoms.input_cap_formula]
    dsimp only [Praw, a, capLinearCoefficient, Cb, bankLinearCoefficient] at *
    nlinarith only [hGk, hraw', hO', hU, hm]
  refine ⟨hS, ?_⟩
  have hCut := Nat.mul_le_mul_left
    (cutNumericCoefficient B.degreeBound (sourceGap D B)) hS
  dsimp only [Zpair, pairLinearCoefficient]
  nlinarith only [hX', hCap, hCut, hO', hraw', hU]

#print axioms source_pair_atoms_linear

end
end Paper2.CurrentAdditive.QuarticSourceEnvelope
