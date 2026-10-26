import Paper2.FallbackUniformRun
import Paper2.SamplerFallbackJoin

/-! Unit 3, map item 6 (private), no-preloaded-`B/R` form. The fixed program
`SamplerFallbackJoin.program` (private predecessor, `a-success-table-owner`,
read-back ACCEPT at exact scope) first produces `B = clog₂ M` and
`R = rejectionAttemptCap N` physically from the raw public unary counts, then
runs the admitted `CodeFallbackFullJoin.program`. Here its whole clock is
bounded at the exact checked schedule of frozen v12 Appendix D by
`2^(noPreloadExponent*(k+1)*L)`; every tape is covered. The only initial data
are the public unary counts and the written tape word. -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

namespace Paper2.FallbackNoPreloadClock

open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.SourceRecursiveNoSampling Paper2.ParameterizedCanonicalSource

noncomputable abbrev cf : Nat := EthInapproximability.CurrentPaper.UnaryBinaryEncoding.coefficient

/-! ### Generic arithmetic -/

theorem loopCap_le (A B C D V : Nat) :
    ∀ (k r c u v : Nat),
      (∀ j, j ≤ k → (SamplerAffineLoop.values A B C D j r c).1 ≤ V ∧
        (SamplerAffineLoop.values A B C D j r c).2 ≤ V) →
      u ≤ V → v ≤ V →
      SamplerAffineLoop.loopCap A B C D k r c u v ≤
        1 + k * (V * (10 + 2 * B + 2 * D) + 2 * A + 2 * C + 14)
  | 0, r, c, u, v, _, _, _ => by simp [SamplerAffineLoop.loopCap]
  | k + 1, r, c, u, v, hV, hu, hv => by
      have h0 := hV 0 (by omega)
      obtain ⟨hr, hc⟩ := h0
      change r ≤ V at hr
      change c ≤ V at hc
      have ih := loopCap_le A B C D V k (A + B * c) (C + D * r) r c
        (fun j hj => hV (j + 1) (by omega)) hr hc
      have hround : SamplerAffineLoop.roundCap A B C D r c u v ≤
          V * (10 + 2 * B + 2 * D) + 2 * A + 2 * C + 13 := by
        unfold SamplerAffineLoop.roundCap
          EthInapproximability.CurrentPaper.MatrixAddressMachine.exactTime
        have h1 : c * B ≤ V * B := Nat.mul_le_mul_right B hc
        have h2 : r * D ≤ V * D := Nat.mul_le_mul_right D hr
        nlinarith [h1, h2]
      show 1 + SamplerAffineLoop.roundCap A B C D r c u v +
          SamplerAffineLoop.loopCap A B C D k (A + B * c) (C + D * r) r c ≤ _
      generalize V * (10 + 2 * B + 2 * D) + 2 * A + 2 * C = K at hround ih ⊢
      have hk : (k + 1) * (K + 14) = k * (K + 14) + (K + 14) := by ring
      rw [hk]
      omega

/-- Bit-width producer clock of `SamplerParameterJoin`, in one bound `Z`. -/
theorem bw_le (n p s q₁ q₂ w Q Z : Nat) (hZ : 1 ≤ Z)
    (hn : n ≤ Z) (hp : p ≤ Z) (hs : s ≤ Z) (hq₁ : q₁ ≤ Z) (hq₂ : q₂ ≤ Z)
    (hw : w ≤ Z) (hQ : Q ≤ Z)
    (hM : SamplerParameterJoin.M n p s q₁ q₂ w Q ≤ Z) :
    SamplerParameterJoin.bwClock n p s q₁ q₂ w Q ≤ (4 * cf + 700) * Z ^ 2 := by
  unfold SamplerParameterJoin.bwClock
  generalize SamplerParameterJoin.M n p s q₁ q₂ w Q = M at hM ⊢
  have hsq : (M + 1) ^ 2 ≤ 4 * Z ^ 2 := by
    have h := Nat.pow_le_pow_left (show M + 1 ≤ 2 * Z by omega) 2
    nlinarith [h]
  have hc := Nat.mul_le_mul_left (cf + 6) hsq
  have hZ2 : Z ≤ Z ^ 2 := by nlinarith
  have hcf : cf * Z ^ 2 = cf * Z ^ 2 := rfl
  generalize (cf + 6) * (M + 1) ^ 2 = E at hc ⊢
  have hexp : (4 * cf + 700) * Z ^ 2 = 4 * (cf * Z ^ 2) + 700 * Z ^ 2 := by ring
  have hexp2 : (cf + 6) * (4 * Z ^ 2) = 4 * (cf * Z ^ 2) + 24 * Z ^ 2 := by ring
  rw [hexp]
  rw [hexp2] at hc
  generalize cf * Z ^ 2 = F at hc ⊢
  generalize Z ^ 2 = Z2 at hZ2 hc ⊢
  omega

/-- The number-producer clock of `SamplerNRProducer`, in one bound `Z`. -/
theorem nr_le (s q₁ q₂ w Q p k mX mY Z : Nat) (hZ : 1 ≤ Z)
    (hs : s ≤ Z) (hq₁ : q₁ ≤ Z) (hq₂ : q₂ ≤ Z) (hw : w ≤ Z) (hQ : Q ≤ Z)
    (hp : p ≤ Z) (hk : k ≤ Z) (hx : mX ≤ Z) (hy : mY ≤ Z)
    (hN : SamplerNRProducer.N s q₁ q₂ w Q p k mX mY ≤ Z)
    (hA : SamplerNRProducer.A s q₁ q₂ w Q ≤ Z)
    (hB : SamplerNRProducer.B s q₁ q₂ w Q ≤ Z)
    (hC : SamplerNRProducer.C s q₁ q₂ w Q ≤ Z)
    (hD : SamplerNRProducer.D s q₁ q₂ w Q ≤ Z)
    (hV : ∀ j, j ≤ k →
      (SamplerAffineLoop.values (SamplerNRProducer.A s q₁ q₂ w Q)
        (SamplerNRProducer.B s q₁ q₂ w Q) (SamplerNRProducer.C s q₁ q₂ w Q)
        (SamplerNRProducer.D s q₁ q₂ w Q) j p 1).1 ≤ Z ∧
      (SamplerAffineLoop.values (SamplerNRProducer.A s q₁ q₂ w Q)
        (SamplerNRProducer.B s q₁ q₂ w Q) (SamplerNRProducer.C s q₁ q₂ w Q)
        (SamplerNRProducer.D s q₁ q₂ w Q) j p 1).2 ≤ Z) :
    SamplerNRProducer.clock s q₁ q₂ w Q p k mX mY ≤
      (4 * cf + 26300) * Z ^ 3 := by
  have hZ2 : Z ≤ Z ^ 2 := by nlinarith
  have hZ3 : Z ^ 2 ≤ Z ^ 3 := by nlinarith
  -- draw coefficients
  have hdc := DrawCoefficients.clock_le s q₁ q₂ w Q
  have hdc' : 120 * (s + q₁ + q₂ + w + Q + 1) ^ 3 ≤ 120 * (6 * Z) ^ 3 := by
    apply Nat.mul_le_mul_left
    exact Nat.pow_le_pow_left (by omega) 3
  -- affine loop
  have hloop := loopCap_le (SamplerNRProducer.A s q₁ q₂ w Q)
    (SamplerNRProducer.B s q₁ q₂ w Q) (SamplerNRProducer.C s q₁ q₂ w Q)
    (SamplerNRProducer.D s q₁ q₂ w Q) Z k p 1 0 0 hV (by omega) (by omega)
  have hK : Z * (10 + 2 * SamplerNRProducer.B s q₁ q₂ w Q +
      2 * SamplerNRProducer.D s q₁ q₂ w Q) +
      2 * SamplerNRProducer.A s q₁ q₂ w Q + 2 * SamplerNRProducer.C s q₁ q₂ w Q + 14 ≤
      32 * Z ^ 2 := by
    have h1 : Z * (10 + 2 * SamplerNRProducer.B s q₁ q₂ w Q +
        2 * SamplerNRProducer.D s q₁ q₂ w Q) ≤ Z * (10 + 4 * Z) :=
      Nat.mul_le_mul_left Z (by omega)
    nlinarith [h1]
  have hloop' : SamplerAffineLoop.loopCap (SamplerNRProducer.A s q₁ q₂ w Q)
      (SamplerNRProducer.B s q₁ q₂ w Q) (SamplerNRProducer.C s q₁ q₂ w Q)
      (SamplerNRProducer.D s q₁ q₂ w Q) k p 1 0 0 ≤ 1 + 32 * Z ^ 3 := by
    have hm := Nat.mul_le_mul hk hK
    have he : Z * (32 * Z ^ 2) = 32 * Z ^ 3 := by ring
    omega
  -- draw count machine
  obtain ⟨hr, hc⟩ := hV k le_rfl
  have hdraw : SamplerLoopDraw.drawTime (SamplerNRProducer.pair s q₁ q₂ w Q p k).1
      (SamplerNRProducer.pair s q₁ q₂ w Q p k).2 mX mY ≤ 26 * Z ^ 2 := by
    unfold SamplerLoopDraw.drawTime
      EthInapproximability.CurrentPaper.MatrixAddressMachine.exactTime
    have hr' : (SamplerNRProducer.pair s q₁ q₂ w Q p k).1 ≤ Z := hr
    have hc' : (SamplerNRProducer.pair s q₁ q₂ w Q p k).2 ≤ Z := hc
    generalize (SamplerNRProducer.pair s q₁ q₂ w Q p k).1 = a at hr' ⊢
    generalize (SamplerNRProducer.pair s q₁ q₂ w Q p k).2 = b at hc' ⊢
    have h1 : b * mY ≤ Z * Z := Nat.mul_le_mul hc' hy
    have h2 : a * mX ≤ Z * Z := Nat.mul_le_mul hr' hx
    nlinarith [h1, h2]
  -- logarithm machine
  have hlog : SamplerNRProducer.logClock (SamplerNRProducer.N s q₁ q₂ w Q p k mX mY) ≤
      (4 * cf + 30) * Z ^ 2 := by
    unfold SamplerNRProducer.logClock
    generalize SamplerNRProducer.N s q₁ q₂ w Q p k mX mY = N at hN ⊢
    have hsq : (N + 1) ^ 2 ≤ 4 * Z ^ 2 := by
      have h := Nat.pow_le_pow_left (show N + 1 ≤ 2 * Z by omega) 2
      nlinarith [h]
    have hc := Nat.mul_le_mul_left (cf + 6) hsq
    have hexp : (4 * cf + 30) * Z ^ 2 = 4 * (cf * Z ^ 2) + 30 * Z ^ 2 := by ring
    have hexp2 : (cf + 6) * (4 * Z ^ 2) = 4 * (cf * Z ^ 2) + 24 * Z ^ 2 := by ring
    rw [hexp]
    rw [hexp2] at hc
    generalize (cf + 6) * (N + 1) ^ 2 = E at hc ⊢
    generalize cf * Z ^ 2 = F at hc ⊢
    generalize Z ^ 2 = Z2 at hZ2 hc ⊢
    omega
  have hclog : Nat.clog 2 (SamplerNRProducer.N s q₁ q₂ w Q p k mX mY) ≤ Z := by
    have h : Nat.clog 2 (SamplerNRProducer.N s q₁ q₂ w Q p k mX mY) ≤ SamplerNRProducer.N s q₁ q₂ w Q p k mX mY := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
    omega
  unfold SamplerNRProducer.clock SamplerNRProducer.loopClock
  have hexp : (4 * cf + 26300) * Z ^ 3 =
      4 * (cf * Z ^ 3) + 26300 * Z ^ 3 := by ring
  have hlog' : (4 * cf + 30) * Z ^ 2 ≤ 4 * (cf * Z ^ 3) + 30 * Z ^ 3 := by
    have h1 : cf * Z ^ 2 ≤ cf * Z ^ 3 := Nat.mul_le_mul_left cf hZ3
    nlinarith [h1]
  have h6 : 120 * (6 * Z) ^ 3 = 25920 * Z ^ 3 := by ring
  rw [hexp]
  generalize cf * Z ^ 3 = F at hlog' ⊢
  generalize (4 * cf + 30) * Z ^ 2 = G at hlog hlog' ⊢
  rw [h6] at hdc'
  generalize Z ^ 3 = Z3 at hZ3 hloop' hdc' hlog' ⊢
  generalize Z ^ 2 = Z2 at hZ2 hZ3 hdraw ⊢
  omega

#print axioms loopCap_le
#print axioms bw_le
#print axioms nr_le

end Paper2.FallbackNoPreloadClock
