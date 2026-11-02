import Paper2.FallbackNoPreloadClock

/-! Unit 3, map item 6 (private), no-preloaded-`B/R` all-tape run with one
public clock at the exact checked schedule of frozen v12 Appendix D. -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

namespace Paper2.FallbackNoPreloadRun

open Turing
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.SourceRecursiveNoSampling Paper2.ParameterizedCanonicalSource
open Paper2.FallbackNoPreloadClock

/-- Whole parameter-producer clock of `SamplerParameterJoin` in one bound `Z`. -/
theorem spj_le (n p s q₁ q₂ w Q k mX mY Z : Nat) (hZ : 1 ≤ Z)
    (hn : n ≤ Z) (hp : p ≤ Z) (hs : s ≤ Z) (hq₁ : q₁ ≤ Z) (hq₂ : q₂ ≤ Z)
    (hw : w ≤ Z) (hQ : Q ≤ Z) (hk : k ≤ Z) (hx : mX ≤ Z) (hy : mY ≤ Z)
    (hM : SamplerParameterJoin.M n p s q₁ q₂ w Q ≤ Z)
    (hB : SamplerParameterJoin.B n p s q₁ q₂ w Q ≤ Z)
    (hR : SamplerParameterJoin.R p s q₁ q₂ w Q k mX mY ≤ Z)
    (hN : SamplerNRProducer.N s q₁ q₂ w Q p k mX mY ≤ Z)
    (hA' : SamplerNRProducer.A s q₁ q₂ w Q ≤ Z)
    (hB' : SamplerNRProducer.B s q₁ q₂ w Q ≤ Z)
    (hC' : SamplerNRProducer.C s q₁ q₂ w Q ≤ Z)
    (hD' : SamplerNRProducer.D s q₁ q₂ w Q ≤ Z)
    (hV : ∀ j, j ≤ k →
      (SamplerAffineLoop.values (SamplerNRProducer.A s q₁ q₂ w Q)
        (SamplerNRProducer.B s q₁ q₂ w Q) (SamplerNRProducer.C s q₁ q₂ w Q)
        (SamplerNRProducer.D s q₁ q₂ w Q) j p 1).1 ≤ Z ∧
      (SamplerAffineLoop.values (SamplerNRProducer.A s q₁ q₂ w Q)
        (SamplerNRProducer.B s q₁ q₂ w Q) (SamplerNRProducer.C s q₁ q₂ w Q)
        (SamplerNRProducer.D s q₁ q₂ w Q) j p 1).2 ≤ Z) :
    SamplerParameterJoin.clock n p s q₁ q₂ w Q k mX mY ≤
      (8 * cf + 27100) * Z ^ 3 := by
  have hZ2 : Z ≤ Z ^ 2 := by nlinarith
  have hZ3 : Z ^ 2 ≤ Z ^ 3 := by nlinarith
  have hbw := bw_le n p s q₁ q₂ w Q Z hZ hn hp hs hq₁ hq₂ hw hQ hM
  have hnr := nr_le s q₁ q₂ w Q p k mX mY Z hZ hs hq₁ hq₂ hw hQ hp hk hx hy
    hN hA' hB' hC' hD' hV
  have hbw' : (4 * cf + 700) * Z ^ 2 ≤ 4 * (cf * Z ^ 3) + 700 * Z ^ 3 := by
    have h1 : cf * Z ^ 2 ≤ cf * Z ^ 3 := Nat.mul_le_mul_left cf hZ3
    nlinarith [h1]
  have hexp1 : (4 * cf + 26300) * Z ^ 3 = 4 * (cf * Z ^ 3) + 26300 * Z ^ 3 := by ring
  have hexp2 : (8 * cf + 27100) * Z ^ 3 = 8 * (cf * Z ^ 3) + 27100 * Z ^ 3 := by ring
  unfold SamplerParameterJoin.clock
  rw [hexp2]
  rw [hexp1] at hnr
  generalize (4 * cf + 700) * Z ^ 2 = G at hbw hbw' ⊢
  generalize cf * Z ^ 3 = F at hbw' hnr ⊢
  generalize Z ^ 3 = Z3 at hZ3 hbw' hnr ⊢
  generalize Z ^ 2 = Z2 at hZ2 hZ3 ⊢
  omega

/-- Absorption of the producer bound and the admitted-machine bound. -/
theorem absorb2 (a U T Z3 : Nat) (hT : 1 ≤ T) (hZ : Z3 ≤ 2 ^ (180 * T)) :
    a * Z3 + 1 + 2 ^ (U * T) ≤ 2 ^ ((U + a + 182) * T) := by
  let K := U + a + 180
  have ha : a ≤ 2 ^ (a * T) := by
    have h1 : a < 2 ^ a := Nat.lt_two_pow_self
    have h2 : 2 ^ a ≤ 2 ^ (a * T) :=
      pow_le_pow_right₀ (by decide : 1 ≤ (2:Nat)) (by nlinarith)
    omega
  have h1 : a * Z3 ≤ 2 ^ (K * T) := by
    calc
      a * Z3 ≤ 2 ^ (a * T) * 2 ^ (180 * T) := Nat.mul_le_mul ha hZ
      _ = 2 ^ ((a + 180) * T) := by rw [← pow_add]; congr 1; ring
      _ ≤ 2 ^ (K * T) := pow_le_pow_right₀ (by decide : 1 ≤ (2:Nat))
          (Nat.mul_le_mul_right T (by dsimp [K]; omega))
  have h2 : 2 ^ (U * T) ≤ 2 ^ (K * T) :=
    pow_le_pow_right₀ (by decide : 1 ≤ (2:Nat))
      (Nat.mul_le_mul_right T (by dsimp [K]; omega))
  have h3 : 1 ≤ 2 ^ (K * T) := Nat.one_le_two_pow
  have h4 : 4 * 2 ^ (K * T) ≤ 2 ^ ((U + a + 182) * T) := by
    calc
      4 * 2 ^ (K * T) = 2 ^ (2 + K * T) := by rw [pow_add]; norm_num
      _ ≤ _ := pow_le_pow_right₀ (by decide : 1 ≤ (2:Nat)) (by dsimp [K]; nlinarith)
  omega

/-- The fixed no-preload exponent. -/
noncomputable def noPreloadExponent : Nat :=
  FallbackUniformClock.uniformExponent + 8 * cf + 27282

/-- Scheduled atom bounds, all by `Z = 2^(60(k+1)L)`. -/
theorem scheduled_atoms {n m : Nat} [NeZero n]
    (L Δ : Nat) (γ : ℚ)
    (hc : Paper2.CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) L Δ γ) (k : Nat) :
    let p := LookupSeed.width L
    let s := SourceProfileParameters.width L
    let q₁ := SourceProfileParameters.width L - 2
    let q₂ := SourceProfileParameters.outerWidth L
    let w := restorationWidth L
    let Q := coverWidth n m L Δ γ
    let mX := sourceRows L (restorationDepth L) (coverDepth n m L Δ γ) k
    let mY := sourceCols L (restorationDepth L) (coverDepth n m L Δ γ) k
    let Z := 2 ^ (60 * ((k + 1) * L))
    SamplerParameterJoin.clock n p s q₁ q₂ w Q k mX mY ≤
      (8 * cf + 27100) * Z ^ 3 := by
  intro p s q₁ q₂ w Q mX mY Z
  let T := (k + 1) * L
  have hL : 16 ≤ L := by
    rcases hc with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hL, _⟩
    exact hL
  have hT : 1 ≤ T := by
    have hp : 0 < (k + 1) * L := Nat.mul_pos (by omega) (by omega)
    dsimp [T]; omega
  have hLT : L ≤ T := by dsimp [T]; nlinarith
  have hkT : k ≤ T := by dsimp [T]; nlinarith
  have hZ1 : 1 ≤ Z := Nat.one_le_two_pow
  have mono : ∀ e, e ≤ 60 * T → 2 ^ e ≤ Z := fun e he =>
    pow_le_pow_right₀ (by decide : 1 ≤ (2:Nat)) he
  -- alphabet cap and the seven public counts
  have hM : SamplerParameterJoin.M n p s q₁ q₂ w Q ≤ 2 ^ (8 * L) :=
    FairBitCap.scheduled_alphabetCap_le L Δ γ hc
  have hMZ : SamplerParameterJoin.M n p s q₁ q₂ w Q ≤ Z :=
    hM.trans (mono _ (by omega))
  have hcnt : n ≤ 2 ^ (8 * L) ∧ p ≤ 2 ^ (8 * L) ∧ s ≤ 2 ^ (8 * L) ∧
      q₁ ≤ 2 ^ (8 * L) ∧ q₂ ≤ 2 ^ (8 * L) ∧ w ≤ 2 ^ (8 * L) ∧
      Q ≤ 2 ^ (8 * L) := by
    have h := hM
    unfold SamplerParameterJoin.M RecursiveSamplingExecution.alphabetCap at h
    omega
  obtain ⟨hn, hp, hs, hq₁, hq₂, hw, hQ⟩ := hcnt
  let Y := 2 ^ (8 * L)
  have hY1 : 1 ≤ Y := Nat.one_le_two_pow
  have hYZ : Y ≤ Z := mono _ (by omega)
  -- depth and dimensions
  have hk : k ≤ Z := by
    have h1 : k < 2 ^ k := Nat.lt_two_pow_self
    have h2 : 2 ^ k ≤ Z := mono _ (by omega)
    omega
  obtain ⟨hx, hy⟩ := FairBitCap.scheduled_each_dimension_le L Δ γ hc k
  have hxZ : mX ≤ Z := hx.trans (mono _ (by dsimp [T] at *; nlinarith))
  have hyZ : mY ≤ Z := hy.trans (mono _ (by dsimp [T] at *; nlinarith))
  -- draw count, bit width and attempt cap
  have hN : SamplerNRProducer.N s q₁ q₂ w Q p k mX mY ≤ Z := by
    have h := FairBitCap.scheduled_drawCap_le L Δ γ hc k
    exact h.trans (mono _ (by dsimp [T]; nlinarith))
  have hB : SamplerParameterJoin.B n p s q₁ q₂ w Q ≤ Z := by
    have h : SamplerParameterJoin.B n p s q₁ q₂ w Q ≤ 8 * L :=
      FairBitCap.scheduled_alphabet_bitWidth_le L Δ γ hc
    have h2 : 8 * L < 2 ^ (8 * L) := Nat.lt_two_pow_self
    omega
  have hR : SamplerParameterJoin.R p s q₁ q₂ w Q k mX mY ≤ Z := by
    have hN60 : SamplerNRProducer.N s q₁ q₂ w Q p k mX mY ≤ 2 ^ (60 * T) := by
      have h := FairBitCap.scheduled_drawCap_le L Δ γ hc k
      exact h.trans (le_of_eq (by dsimp [T]; ring_nf))
    have h := FairBitCap.rejectionAttemptCap_le_of_pow _ _ hN60
    have hlin := CodeSamplerScheduledBounds.linear_le_pow T hT
    have h8 : 2 ^ (8 * T) ≤ Z := mono _ (by omega)
    change Paper2.rejectionAttemptCap (SamplerNRProducer.N s q₁ q₂ w Q p k mX mY) ≤ Z
    omega
  -- affine coefficients
  have hsq : ∀ a b : Nat, a ≤ Y → b ≤ Y → a * b ≤ Y ^ 2 := fun a b ha hb => by
    have := Nat.mul_le_mul ha hb; nlinarith
  have hY2 : Y ≤ Y ^ 2 := by nlinarith
  have hY3 : Y ^ 2 ≤ Y ^ 3 := by nlinarith
  have hY3Z : 5 * Y ^ 3 ≤ Z := by
    have h : 5 * Y ^ 3 ≤ 2 ^ (27 * L) := by
      have hc3 : Y ^ 3 = 2 ^ (24 * L) := by dsimp [Y]; rw [← pow_mul]; congr 1; ring
      have h5 : 5 ≤ 2 ^ (3 * L) := by
        have : 2 ^ 3 ≤ 2 ^ (3 * L) := pow_le_pow_right₀ (by decide) (by omega)
        norm_num at this ⊢; omega
      calc
        5 * Y ^ 3 ≤ 2 ^ (3 * L) * 2 ^ (24 * L) := by rw [hc3]; exact Nat.mul_le_mul_right _ h5
        _ = 2 ^ (27 * L) := by rw [← pow_add]; congr 1; ring
    exact h.trans (mono _ (by omega))
  have hA' : SamplerNRProducer.A s q₁ q₂ w Q ≤ Z := by
    show Q * (s + 2) ≤ Z
    have h1 : Q * (s + 2) ≤ Y * (Y + 2) := Nat.mul_le_mul hQ (by omega)
    nlinarith
  have hB' : SamplerNRProducer.B s q₁ q₂ w Q ≤ Z := by
    show Q * (s + 1 + s * (q₁ + s + 1)) ≤ Z
    have h0 : s * (q₁ + s + 1) ≤ Y * (2 * Y + 1) := Nat.mul_le_mul hs (by omega)
    have h1 : Q * (s + 1 + s * (q₁ + s + 1)) ≤ Y * (Y + 1 + Y * (2 * Y + 1)) :=
      Nat.mul_le_mul hQ (by omega)
    nlinarith
  have hC' : SamplerNRProducer.C s q₁ q₂ w Q ≤ Z := by
    show 1 + 3 * w + w * q₂ ≤ Z
    have h1 := hsq w q₂ hw hq₂
    have hw' : w ≤ Y := hw
    linarith [h1, hw', hY2, hY3, hY3Z, hY1]
  have hD' : SamplerNRProducer.D s q₁ q₂ w Q ≤ Z := by
    show w * q₂ ≤ Z
    have h1 := hsq w q₂ hw hq₂
    nlinarith
  -- every loop stage is a recursive draw bound
  have hstep := FairBitCap.scheduled_stepCap_le L Δ γ hc
  have hV : ∀ j, j ≤ k →
      (SamplerAffineLoop.values (SamplerNRProducer.A s q₁ q₂ w Q)
        (SamplerNRProducer.B s q₁ q₂ w Q) (SamplerNRProducer.C s q₁ q₂ w Q)
        (SamplerNRProducer.D s q₁ q₂ w Q) j p 1).1 ≤ Z ∧
      (SamplerAffineLoop.values (SamplerNRProducer.A s q₁ q₂ w Q)
        (SamplerNRProducer.B s q₁ q₂ w Q) (SamplerNRProducer.C s q₁ q₂ w Q)
        (SamplerNRProducer.D s q₁ q₂ w Q) j p 1).2 ≤ Z := by
    intro j hj
    rw [SamplerAffineSource.values_eq_drawBounds]
    have hb := FairBitCap.drawBounds_le_stepCap_pow s q₁ q₂ w Q p 1 j
      (by omega)
    have hmax : max p 1 ≤ Y := max_le hp hY1
    have hpow : FairBitCap.stepCap s q₁ q₂ w Q ^ j ≤ (2 ^ (25 * L)) ^ k := by
      calc
        FairBitCap.stepCap s q₁ q₂ w Q ^ j ≤ (2 ^ (25 * L)) ^ j :=
          Nat.pow_le_pow_left hstep j
        _ ≤ (2 ^ (25 * L)) ^ k :=
          pow_le_pow_right₀ Nat.one_le_two_pow hj
    have hprod : max p 1 * FairBitCap.stepCap s q₁ q₂ w Q ^ j ≤ Z := by
      calc
        max p 1 * FairBitCap.stepCap s q₁ q₂ w Q ^ j ≤ Y * (2 ^ (25 * L)) ^ k :=
          Nat.mul_le_mul hmax hpow
        _ = 2 ^ (8 * L + 25 * L * k) := by
          dsimp [Y]; rw [← pow_mul, ← pow_add]
        _ ≤ Z := mono _ (by dsimp [T]; nlinarith)
    exact ⟨hb.1.trans hprod, hb.2.trans hprod⟩
  exact spj_le n p s q₁ q₂ w Q k mX mY Z hZ1
    (hn.trans hYZ) (hp.trans hYZ) (hs.trans hYZ) (hq₁.trans hYZ) (hq₂.trans hYZ)
    (hw.trans hYZ) (hQ.trans hYZ) hk hxZ hyZ hMZ hB hR hN hA' hB' hC' hD' hV

#print axioms spj_le
#print axioms absorb2
#print axioms scheduled_atoms

end Paper2.FallbackNoPreloadRun
