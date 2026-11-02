import CurrentAdditive.QuarticSourceEnvelope
import Paper2.E6Clock3

/-! Sparse-source subexponential time for the actual fixed v27 pair-front clock. -/

namespace Paper2.CurrentAdditive.QuarticSourcePairSubexp

open Paper2 Paper2.CurrentAdditive.QuarticConstructor
open Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2.CurrentAdditive.QuarticSourceEnvelope
open Paper2.CurrentAdditive.QuarticSourcePairClock
open Paper2.CurrentAdditive.QuarticSourceCutClock
open Paper2.CurrentAdditive.QuarticTMClockRepair

noncomputable section
set_option maxHeartbeats 8000000

theorem source_pair_front_subexp
    (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))
    (cs : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C N₀ : ℕ, ∀ Φ : ValidFormula,
      Φ.val.clauses.length ≤ cs * Φ.val.variables →
      N₀ ≤ Φ.val.variables →
      (hc : CurrentAdditive.QuarticSchedule.Checks27
        (V := Fin (t10Graph D B Φ).vertices)
        (Edges := Fin (t10Graph D B Φ).edges.length)
        (Nat.clog 2 (t10Graph D B Φ).vertices)
        B.degreeBound (sourceGap D B)) →
      let g := t10Graph D B Φ
      let hg := t10Graph_valid D B Φ
      let hn := t10_vertices_pos D B Φ
      let k := kOf Φ.val.variables
      ∀ tape : List Bool,
      ∀ t : (select27 hn (CanonicalEdgeTape.graphEdge g hg)
        B.degreeBound (sourceGap D B) k).Tape,
      let raw := tape.take (Paper2.AEth3.cutLen Φ.val)
      let Y := QuarticDispatchSpec.inputBank27 B.degreeBound
        (sourceGap D B) g hg hn k t
      let Tcut := QuarticOuterMachine.cutClock (FullFront.X0 g k raw) Y
        (QuarticOuterUniform.localCap g B.degreeBound (sourceGap D B) k raw
          (QuarticUniformInputCap.inputCap g B.degreeBound
            (sourceGap D B) k raw.length))
      QuarticPairFront.pairFrontClock D B Φ raw (BitMachineBankCodec.encode Y)
        Tcut ≤ C * ⌈(2 : ℝ) ^ (ε * Φ.val.variables)⌉₊ := by
  let E := QuarticPairFront.frontExponent D B + 1
  let F := QuarticPairFront.frontCoefficient D B + 100
  let L := pairLinearCoefficient B.degreeBound (sourceGap D B)
  let A := 3 * (L + 1)
  let a : ℝ := ε / (E + 1)
  have ha : 0 < a := by dsimp [a]; positivity
  have haE : a * E ≤ ε := by
    dsimp [a]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨Nexp, hExp⟩ := Paper2.AEth.expLen_le_rpow a ha
  obtain ⟨Natom, hAtom⟩ := source_pair_atoms_linear D B cs
  refine ⟨F * A ^ E * 2 ^ E, max Nexp Natom, ?_⟩
  intro Φ hsparse hlarge hc g hg hn k tape t raw Y Tcut
  let U := Paper2.AEth.expLen Φ.val.variables
  let O := (BitMachineBankCodec.encode Y).length
  let Praw := (g.vertices + 2) ^
    (rawExponent B.degreeBound (sourceGap D B) * (k + 1))
  let Pcut := (g.vertices + 2) ^ (360 * (k + 1))
  let S := Praw + Pcut + (EncodedGraph.encode g).length + k + raw.length + O + 1
  let Z := (EncodedCNF.encode Φ.val).length +
    QuarticUniformInputCap.inputCap g B.degreeBound
      (sourceGap D B) k raw.length +
    cutNumericCoefficient B.degreeBound (sourceGap D B) * S +
    O + raw.length + 1
  have hNexp : Nexp ≤ Φ.val.variables := (le_max_left _ _).trans hlarge
  have hNatom : Natom ≤ Φ.val.variables := (le_max_right _ _).trans hlarge
  have hZ : Z ≤ L * U := by
    have h := (hAtom Φ hsparse hNatom tape t).2
    simpa only [Z, S, Praw, Pcut, O, Y, raw, g, hg, hn, k, U, L] using h
  have hclock : QuarticPairFront.pairFrontClock D B Φ raw
      (BitMachineBankCodec.encode Y) Tcut ≤ F * (3 * (Z + 1)) ^ E := by
    simpa only [Z, S, Praw, Pcut, O, Y, raw, g, hg, hn, k, F, E, Tcut] using
      (source_pair_front_clock D B Φ raw Y hc)
  have hU : 1 ≤ U := Nat.one_le_two_pow
  have hbase : 3 * (Z + 1) ≤ A * U := by
    dsimp only [A]
    nlinarith only [hZ, hU]
  have hpow : (3 * (Z + 1)) ^ E ≤ A ^ E * U ^ E := by
    calc
      _ ≤ (A * U) ^ E := Nat.pow_le_pow_left hbase E
      _ = A ^ E * U ^ E := by rw [mul_pow]
  have hUr : (U : ℝ) ≤ (2 : ℝ) ^ (a * Φ.val.variables) :=
    hExp Φ.val.variables hNexp
  have hUc : U ≤ ⌈(2 : ℝ) ^ (a * Φ.val.variables)⌉₊ := by
    exact_mod_cast hUr.trans (Nat.le_ceil _)
  have hUclock : U ^ E ≤ 2 ^ E * ⌈(2 : ℝ) ^ (ε * Φ.val.variables)⌉₊ :=
    (Nat.pow_le_pow_left hUc E).trans
      (Paper2.AEth6.ceil_pow_le E ha.le (Nat.cast_nonneg _) haE)
  calc
    _ ≤ F * (3 * (Z + 1)) ^ E := hclock
    _ ≤ F * (A ^ E * U ^ E) := Nat.mul_le_mul_left _ hpow
    _ ≤ F * (A ^ E * (2 ^ E * ⌈(2 : ℝ) ^ (ε * Φ.val.variables)⌉₊)) := by
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hUclock)
    _ = F * A ^ E * 2 ^ E * ⌈(2 : ℝ) ^ (ε * Φ.val.variables)⌉₊ := by ring

#print axioms source_pair_front_subexp

end
end Paper2.CurrentAdditive.QuarticSourcePairSubexp
