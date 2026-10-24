import EthInapproximability.CurrentPaper.ClockB

/-! Lane owner:b-weighted-level-10, unit 2, segment 4b-ii (first piece): the public scale words
at every level are polynomial.

Every round-clock component (`costBound`, `dimsBound`, the Stage-4 writer bound inside
`actualPhysicalBudget`, the bridge start bank) is a function of the level parameter record and of
the derived words `Parameters.scale`, `Parameters.bins`. Here, from the admitted definitions only:
`scaleBound P ≤ c + b + cost + rows + columns + edges + 2`, `scale P ≤ 2^24 + scaleBound P`, and
`bins P ≤ binsConst + 2 scaleBound P` with the FIXED constant `binsConst = 2^(10000 * 24^2)`
(`bins = 2^(10000 clog(scale)^2)`; when `clog(scaleBound) ≤ 2^24` the scale is `2^24`, otherwise
`10000 clog(u)^2 < u` for `u = clog(scaleBound) > 2^24`, so `bins < 2^u < 2 scaleBound`). At the
physical level `j ≤ k` (`level_scaleBound`): `scaleBound ≤ c + 2n + 8T + A(|w|+1)^(d+1) + 3`. -/

namespace EthInapproximability.CurrentPaper.ClockC

open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open ClockA

noncomputable section

/-- The fixed constant `2^(10000 * 24^2)` (never evaluated). -/
@[irreducible] def binsConst : ℕ := 2 ^ (10000 * 24 ^ 2)

theorem binsConst_eq : binsConst = 2 ^ (10000 * 24 ^ 2) := by
  unfold binsConst; rfl

theorem sq_le_two_pow (m : ℕ) (hm : 24 ≤ m) : 10000 * (m + 1) ^ 2 ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have h1 : (m + 1 + 1) ^ 2 ≤ 2 * (m + 1) ^ 2 := by nlinarith
    rw [pow_succ 2 m]
    linarith

theorem clog_sq_lt (u : ℕ) (hu : 2 ^ 24 < u) : 10000 * Nat.clog 2 u ^ 2 < u := by
  have hc : 24 < Nat.clog 2 u := by
    by_contra h
    rw [not_lt] at h
    have h1 := Nat.le_pow_clog (by norm_num : 1 < 2) u
    have h2 : 2 ^ Nat.clog 2 u ≤ 2 ^ 24 := Nat.pow_le_pow_right (by norm_num) h
    omega
  obtain ⟨m, hm⟩ : ∃ m, Nat.clog 2 u = m + 1 := ⟨Nat.clog 2 u - 1, by omega⟩
  have hp := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) (show 1 < u by
    have : 1 < 2 ^ 24 := by norm_num
    omega)
  rw [hm] at hp ⊢
  simp only [Nat.pred_eq_sub_one, Nat.add_sub_cancel] at hp
  have := sq_le_two_pow m (by omega)
  omega

theorem clog_le_self (x : ℕ) : Nat.clog 2 x ≤ x :=
  Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le

theorem scaleBound_le (P : Parameters.Input) :
    Parameters.scaleBound P ≤
      P.sourceConstant + P.nextDepth + P.cost + P.rows + P.columns + P.edges + 2 := by
  unfold Parameters.scaleBound Parameters.namingLength
  have h1 := clog_le_self P.rows
  have h2 := clog_le_self P.columns
  have h3 := clog_le_self (P.edges + 2)
  have h4 : Nat.clog 2 (P.edges + 2) ≤ P.edges + 1 := by
    apply Nat.clog_le_of_le_pow
    have : P.edges + 1 < 2 ^ (P.edges + 1) := Nat.lt_two_pow_self
    omega
  simp only [max_le_iff]
  omega

theorem two_le_scaleBound (P : Parameters.Input) : 2 ≤ Parameters.scaleBound P := by
  unfold Parameters.scaleBound
  simp only [le_max_iff]
  omega

theorem scale_le (P : Parameters.Input) : Parameters.scale P ≤ 2 ^ 24 + Parameters.scaleBound P := by
  unfold Parameters.scale
  have := clog_le_self (Parameters.scaleBound P)
  simp only [max_le_iff]
  omega

theorem bins_le (P : Parameters.Input) :
    Parameters.bins P ≤ binsConst + 2 * Parameters.scaleBound P := by
  unfold Parameters.bins Parameters.binExponent Parameters.auxiliaryLog Parameters.scale
  by_cases h : Nat.clog 2 (Parameters.scaleBound P) ≤ 2 ^ 24
  · rw [max_eq_left h, Nat.clog_pow 2 24 (by norm_num), ← binsConst_eq]
    omega
  · rw [not_le] at h
    rw [max_eq_right h.le]
    set u := Nat.clog 2 (Parameters.scaleBound P) with hu
    have h1 := clog_sq_lt u h
    have h2 : 2 ^ (10000 * Nat.clog 2 u ^ 2) ≤ 2 ^ u := Nat.pow_le_pow_right (by norm_num) h1.le
    have hsb := two_le_scaleBound P
    have h3 := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) (show 1 < Parameters.scaleBound P by omega)
    have hu1 : 1 ≤ u := by
      have : 1 < 2 ^ 24 := by norm_num
      omega
    have h4 : 2 ^ u = 2 * 2 ^ (u - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [← hu] at h3
    simp only [Nat.pred_eq_sub_one] at h3
    omega

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The scale bound of the physical level-`j` parameters (`j ≤ k`) is polynomial. -/
theorem level_scaleBound (G : EndpointGraph V E) (c A d Δ n : ℕ) (γ : ℚ)
    (hcommon : G.SourceCommon γ Δ) (hlower : n ≤ Fintype.card E)
    (hupper : Fintype.card E ≤ A * n * EffectiveIteration.sourceDepth n ^ d)
    (hrep : 1 ≤ ETHTailGrowth.repetitions c A d n) (j : ℕ)
    (hj : j ≤ ETHTailGrowth.repetitions c A d n) :
    Parameters.scaleBound (PhysicalLevelRun.physParameters G c (EffectiveIteration.sourceDepth n)
        (Iteration.seedState (EffectiveIteration.sourceDepth n)) j) ≤
      c + 2 * n + 8 * FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n +
        A * ((SourceOriginalBranchPackets.packet n
          (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ (d + 1) + 3 := by
  have hf := level_facts G c A d Δ n γ hcommon hlower hupper hrep j hj
  have hE := hupper
  have hpl := SourceOriginalBranchPackets.packet_length n
    (EncodedGraph.encode (EncodedETHSource.serializeGraph G))
  have hb := WeightedRawWordsClock.sourceDepth_le_succ n
  have hs := scaleBound_le (PhysicalLevelRun.physParameters G c (EffectiveIteration.sourceDepth n)
        (Iteration.seedState (EffectiveIteration.sourceDepth n)) j)
  refine hs.trans ?_
  set k := ETHTailGrowth.repetitions c A d n with hkdef
  set b := EffectiveIteration.sourceDepth n with hbdef
  set st := PhysicalLevelRun.physRun G c b (Iteration.seedState b) j with hst
  set w := (SourceOriginalBranchPackets.packet n
    (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length with hw
  change c + b + (st.budget + j) + st.matrix.rows + st.matrix.columns + Fintype.card E + 2 ≤ _
  have hr := rows_le_prod st.matrix
  have hcl := cols_le_prod st.matrix
  have hcost : st.budget + j ≤ n := by
    have h1 : st.budget + j + j ≤ 2 * k * (st.budget + j + j) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hbY : b ^ d ≤ (w + 1) ^ d := Nat.pow_le_pow_left (by omega) d
  have hEY : Fintype.card E ≤ A * (w + 1) ^ (d + 1) := by
    calc Fintype.card E ≤ A * n * b ^ d := hE
      _ ≤ A * (w + 1) * (w + 1) ^ d :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hbY
      _ = A * (w + 1) ^ (d + 1) := by rw [pow_succ]; ring
  omega

#print axioms sq_le_two_pow
#print axioms clog_sq_lt
#print axioms scaleBound_le
#print axioms scale_le
#print axioms bins_le
#print axioms level_scaleBound

end
end EthInapproximability.CurrentPaper.ClockC
