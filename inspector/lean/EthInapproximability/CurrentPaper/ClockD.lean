import EthInapproximability.CurrentPaper.ClockC

/-! Lane owner:b-weighted-level-10, unit 2, segment 4b-ii (second piece): owner-6's cost-update
clock `CostUpdateMachine.costBound` is polynomial, and at every physical level `j ≤ k` it is
bounded by `(2000000 Kc + 1000000) (2^24 + binsConst + 8 (c + 2n + 8T + A (|w|+1)^(d+1) + 3) + 1)^6`
(`Kc`, `binsConst` fixed constants). Note: `unfold Kcost` on a goal of this size exhausted memory
(guard kill), so the constant is written out.

`logStageBound_le`: `logStageBound m ≤ Kc (m+1)^2`, `Kc = (logCard+1)(logPer+1)(coefficient+20)`.
`costBound_le`: `costBound lam b c s e y ≤ (2000000 Kc + 1000000) N^6`, `N = lam+b+c+s+e+y+1`.
`level_costBound`: the instance of `costBound` inside
`roundBoundP` / `level0BoundP` (`lam = scale P`, `s = bins P`, `e = |E|`, `y = P.cost`, `P` the
physical level-`j` parameters). -/

namespace EthInapproximability.CurrentPaper.ClockD

open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open CostUpdateStages CostUpdateMachine
open ClockA ClockC

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

def Kc : ℕ := (logCard + 1) * (logPer + 1) * (UnaryBinaryEncoding.coefficient + 20)

theorem logStageBound_le (m : ℕ) : logStageBound m ≤ Kc * (m + 1) ^ 2 := by
  unfold logStageBound logBound Kc
  generalize logCard = lc
  generalize logPer = lp
  generalize UnaryBinaryEncoding.coefficient = co
  set q := (m + 1) ^ 2 with hq
  have hmq : m + 1 ≤ q := by
    rw [hq]; nlinarith
  have hcl : Nat.clog 2 m ≤ m := clog_le_self m
  have hLB : 2 * m + 2 + (co + 6) * q ≤ (co + 8) * q := by
    have : (co + 8) * q = (co + 6) * q + 2 * q := by ring
    omega
  have h1 : lc * (m + lp * (2 * m + 2 + (co + 6) * q)) ≤ lc * q + lc * lp * ((co + 8) * q) := by
    have h := Nat.mul_le_mul_left lp hLB
    calc lc * (m + lp * (2 * m + 2 + (co + 6) * q))
        ≤ lc * (q + lp * ((co + 8) * q)) := Nat.mul_le_mul_left _ (by omega)
      _ = lc * q + lc * lp * ((co + 8) * q) := by ring
  have h2 : lc ≤ lc * q := Nat.le_mul_of_pos_right _ (by omega)
  have h3 : 0 ≤ lc * lp * q := Nat.zero_le _
  have h4 : 0 ≤ lp * co * q := Nat.zero_le _
  have h5 : 0 ≤ lc * co * q := Nat.zero_le _
  have h6 : 0 ≤ lp * q := Nat.zero_le _
  have h7 : 0 ≤ co * q := Nat.zero_le _
  have h8 : 0 ≤ lc * lp * co * q := Nat.zero_le _
  have h9 : 0 ≤ lc * q := Nat.zero_le _
  linarith

theorem st_sum (lam b c s e Y K1 K2 K3 K4 T1 L T2 T3 T4 T5 T6 T7 : ℕ) :
    (∑ i : Fin 12, st lam b c s e Y K1 K2 K3 K4 T1 L T2 T3 T4 T5 T6 T7 ⟨i.val + 6, by omega⟩) =
      K1 + K2 + K3 + K4 + T1 + L + T2 + T3 + T4 + T5 + T6 + T7 := by
  simp [Fin.sum_univ_succ, st]
  ring

theorem costBound_le' (lam b c s e y N X : ℕ) (hN1 : 1 ≤ N) (hlam : lam + 1 ≤ N) (hs : s ≤ N)
    (he : e ≤ N) (hb : b ≤ N) (hc : c ≤ N) (hXdef : N ^ 6 = X) :
    costBound lam b c s e y ≤ (2000000 * Kc + 1000000) * X := by
  unfold costBound
  rw [st_sum]
  simp only [MatrixAddressMachine.exactTime, Nat.add_zero, Nat.mul_zero]
  have hp : ∀ d, d ≤ 6 → N ^ d ≤ X := fun d hd => by
    rw [← hXdef]; exact Nat.pow_le_pow_right hN1 hd
  have hN2 : N * N ≤ X := by rw [← pow_two]; exact hp 2 (by norm_num)
  have hN3 : N * N * N ≤ X := by
    rw [show N * N * N = N ^ 3 by ring]; exact hp 3 (by norm_num)
  have hX1 : 1 ≤ X := by
    rw [← hXdef]; exact Nat.one_le_pow 6 N hN1
  have hlam1 : lam + 1 ≤ N := hlam
  have hL : Nat.clog 2 lam ≤ N := (clog_le_self lam).trans (by omega)
  replace hlam : lam ≤ N := by omega
  have hNX : N ≤ X := by simpa using hp 1 (by norm_num)
  have m1 : lam * lam ≤ X := (Nat.mul_le_mul hlam hlam).trans hN2
  have m2 : Nat.clog 2 lam * Nat.clog 2 lam ≤ X := (Nat.mul_le_mul hL hL).trans hN2
  have m3 : s * e ≤ X := (Nat.mul_le_mul hs he).trans hN2
  have m4 : b * c ≤ X := (Nat.mul_le_mul hb hc).trans hN2
  have m5 : b * c * s ≤ X := (Nat.mul_le_mul (Nat.mul_le_mul hb hc) hs).trans hN3
  have hKc : 0 ≤ Kc := Nat.zero_le _
  have l1 : logStageBound lam ≤ Kc * X := by
    refine (logStageBound_le lam).trans (Nat.mul_le_mul_left _ ?_)
    exact (Nat.pow_le_pow_left (show lam + 1 ≤ N by omega) 2).trans (hp 2 (by norm_num))
  have l2 : logStageBound (s * e * 12) ≤ 169 * (Kc * X) := by
    refine (logStageBound_le _).trans ?_
    have h1 : s * e * 12 + 1 ≤ 13 * (N * N) := by
      have := Nat.mul_le_mul hs he
      have h0 : 1 ≤ N * N := by
        have := Nat.mul_le_mul hN1 hN1
        simpa using this
      linarith
    have h2 : (s * e * 12 + 1) ^ 2 ≤ 169 * (N * N * (N * N)) := by
      calc (s * e * 12 + 1) ^ 2 ≤ (13 * (N * N)) ^ 2 := Nat.pow_le_pow_left h1 2
        _ = 169 * (N * N * (N * N)) := by ring
    have h3 : N * N * (N * N) ≤ X := by
      rw [show N * N * (N * N) = N ^ 4 by ring]; exact hp 4 (by norm_num)
    calc Kc * (s * e * 12 + 1) ^ 2 ≤ Kc * (169 * (N * N * (N * N))) := Nat.mul_le_mul_left _ h2
      _ ≤ Kc * (169 * X) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)
      _ = 169 * (Kc * X) := by ring
  have l3 : logStageBound (b * c * s * 1280) ≤ 1640961 * (Kc * X) := by
    refine (logStageBound_le _).trans ?_
    have h1 : b * c * s * 1280 + 1 ≤ 1281 * (N * N * N) := by
      have := Nat.mul_le_mul (Nat.mul_le_mul hb hc) hs
      have h0 : 1 ≤ N * N * N := by
        have := Nat.mul_le_mul (Nat.mul_le_mul hN1 hN1) hN1
        simpa using this
      linarith
    have h2 : (b * c * s * 1280 + 1) ^ 2 ≤ 1640961 * X := by
      calc (b * c * s * 1280 + 1) ^ 2 ≤ (1281 * (N * N * N)) ^ 2 := Nat.pow_le_pow_left h1 2
        _ = 1640961 * N ^ 6 := by ring
        _ = 1640961 * X := by rw [hXdef]
    calc Kc * (b * c * s * 1280 + 1) ^ 2 ≤ Kc * (1640961 * X) := Nat.mul_le_mul_left _ h2
      _ = 1640961 * (Kc * X) := by ring
  have hKX : 0 ≤ Kc * X := Nat.zero_le _
  calc _ ≤ 2000000 * (Kc * X) + 1000000 * X := by linarith
    _ = (2000000 * Kc + 1000000) * X := by ring

theorem costBound_le (lam b c s e y : ℕ) :
    costBound lam b c s e y ≤ (2000000 * Kc + 1000000) * (lam + b + c + s + e + y + 1) ^ 6 :=
  costBound_le' lam b c s e y _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) rfl

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The cost-update clock at the physical level `j ≤ k`. -/
theorem level_costBound (G : EndpointGraph V E) (c A d Δ n : ℕ) (γ : ℚ)
    (hcommon : G.SourceCommon γ Δ) (hlower : n ≤ Fintype.card E)
    (hupper : Fintype.card E ≤ A * n * EffectiveIteration.sourceDepth n ^ d)
    (hrep : 1 ≤ ETHTailGrowth.repetitions c A d n) (j : ℕ)
    (hj : j ≤ ETHTailGrowth.repetitions c A d n) :
    costBound (Parameters.scale (PhysicalLevelRun.physParameters G c (EffectiveIteration.sourceDepth n)
          (Iteration.seedState (EffectiveIteration.sourceDepth n)) j))
        (EffectiveIteration.sourceDepth n) c
        (Parameters.bins (PhysicalLevelRun.physParameters G c (EffectiveIteration.sourceDepth n)
          (Iteration.seedState (EffectiveIteration.sourceDepth n)) j))
        (Fintype.card E)
        (PhysicalLevelRun.physParameters G c (EffectiveIteration.sourceDepth n)
          (Iteration.seedState (EffectiveIteration.sourceDepth n)) j).cost ≤
      (2000000 * Kc + 1000000) * (2 ^ 24 + binsConst + 8 * (c + 2 * n + 8 * FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n +
        A * ((SourceOriginalBranchPackets.packet n
          (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ (d + 1) + 3) + 1) ^ 6 := by
  refine (costBound_le _ _ _ _ _ _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ 6))
  set P := PhysicalLevelRun.physParameters G c (EffectiveIteration.sourceDepth n)
    (Iteration.seedState (EffectiveIteration.sourceDepth n)) j with hP
  have hsb := level_scaleBound G c A d Δ n γ hcommon hlower hupper hrep j hj
  rw [← hP] at hsb
  have hsc := scale_le P
  have hbi := bins_le P
  have hnd : P.nextDepth ≤ Parameters.scaleBound P := by
    unfold Parameters.scaleBound; simp only [le_max_iff]; omega
  have hsc0 : P.sourceConstant ≤ Parameters.scaleBound P := by
    unfold Parameters.scaleBound; simp only [le_max_iff]; omega
  have hco : P.cost ≤ Parameters.scaleBound P := by
    unfold Parameters.scaleBound; simp only [le_max_iff]; omega
  have hE : Fintype.card E ≤ Parameters.scaleBound P + A * ((SourceOriginalBranchPackets.packet n
          (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ (d + 1) := by
    have hpl := SourceOriginalBranchPackets.packet_length n
      (EncodedGraph.encode (EncodedETHSource.serializeGraph G))
    have hb := WeightedRawWordsClock.sourceDepth_le_succ n
    set w := (SourceOriginalBranchPackets.packet n
      (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length with hw
    have hbY : EffectiveIteration.sourceDepth n ^ d ≤ (w + 1) ^ d := Nat.pow_le_pow_left (by omega) d
    have : Fintype.card E ≤ A * (w + 1) ^ (d + 1) := by
      calc Fintype.card E ≤ A * n * EffectiveIteration.sourceDepth n ^ d := hupper
        _ ≤ A * (w + 1) * (w + 1) ^ d := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hbY
        _ = A * (w + 1) ^ (d + 1) := by rw [pow_succ]; ring
    omega
  change Parameters.scale P + P.nextDepth + P.sourceConstant + Parameters.bins P + Fintype.card E + P.cost + 1 ≤ _
  omega

#print axioms logStageBound_le
#print axioms st_sum
#print axioms costBound_le
#print axioms level_costBound

end
end EthInapproximability.CurrentPaper.ClockD
