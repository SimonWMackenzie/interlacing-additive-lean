import Paper2.FallbackNoPreloadEndpoint

/-! Unit 3, map item 6 (private): composition of the checked all-tape clock
(segment 2c) with the successful table-writing cost, which is left as ONE
named premise in the exact shape of frozen v12 Appendix D
(`eq:generator-bound`: the time `J_k` of one entry evaluation is
`2^(O((k+1)L))`). The row-major writer cost itself is not a premise: it is the
admitted `MatrixTableWriter.writerBound` at the exact scheduled dimensions,
bounded here for every per-entry clock `Tent`. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

namespace Paper2.SuccessPremiseComposition

open Paper2.SourceRecursiveNoSampling Paper2.ParameterizedCanonicalSource

/-- Writer cost for an `EntryRuns` instance with per-entry clock `Tent`
at the exact scheduled dimensions. -/
theorem scheduled_writerBound_entry_le {n m : Nat} [NeZero n]
    (L Δ : Nat) (γ : ℚ)
    (hc : Paper2.CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) L Δ γ) (k Tent cE : Nat)
    (hent : Tent ≤ 2 ^ (cE * (k + 1) * L)) :
    EthInapproximability.CurrentPaper.MatrixTableWriter.writerBound
      (sourceRows L (restorationDepth L) (coverDepth n m L Δ γ) k)
      (sourceCols L (restorationDepth L) (coverDepth n m L Δ γ) k) Tent ≤
      2 ^ ((cE + 63) * (k + 1) * L) := by
  let T := (k + 1) * L
  have hL : 16 ≤ L := by
    rcases hc with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hL, _⟩
    exact hL
  have hT : 1 ≤ T := by
    have hp : 0 < (k + 1) * L := Nat.mul_pos (by omega) (by omega)
    dsimp [T]; omega
  obtain ⟨hx, hy⟩ := FairBitCap.scheduled_each_dimension_le L Δ γ hc k
  have e29 : 29 * (k + 1) * L = 29 * T := by dsimp [T]; ring
  have eE : cE * (k + 1) * L = cE * T := by dsimp [T]; ring
  rw [e29] at hx hy
  rw [eE] at hent
  have e63 : (cE + 63) * (k + 1) * L = (cE + 63) * T := by dsimp [T]; ring
  rw [e63]
  generalize sourceRows L (restorationDepth L) (coverDepth n m L Δ γ) k = r at hx ⊢
  generalize sourceCols L (restorationDepth L) (coverDepth n m L Δ γ) k = c at hy ⊢
  let E := 2 ^ (29 * T)
  let X := 2 ^ (cE * T)
  have hE : 1 ≤ E := Nat.one_le_two_pow
  have hX : 1 ≤ X := Nat.one_le_two_pow
  have hr : r ≤ E := hx
  have hc' : c ≤ E := hy
  have ht : Tent ≤ X := hent
  have hinner : c * (Tent + 2) + 4 * c + 8 ≤ 15 * (E * X) := by
    have h1 : c * (Tent + 2) ≤ E * (X + 2) := Nat.mul_le_mul hc' (by omega)
    have h2 : E ≤ E * X := by nlinarith
    have h3 : 1 ≤ E * X := by nlinarith
    nlinarith
  have hwb : EthInapproximability.CurrentPaper.MatrixTableWriter.writerBound r c Tent ≤
      20 * (E * (E * X)) := by
    unfold EthInapproximability.CurrentPaper.MatrixTableWriter.writerBound
    have h1 : r * (c * (Tent + 2) + 4 * c + 8) ≤ E * (15 * (E * X)) :=
      Nat.mul_le_mul hr hinner
    have h3 : 1 ≤ E * (E * X) := by
      have := Nat.mul_le_mul hE (show 1 ≤ E * X by nlinarith)
      simpa using this
    nlinarith
  have hpow : 20 * (E * (E * X)) ≤ 2 ^ ((cE + 63) * T) := by
    have h5 : 20 ≤ 2 ^ (5 * T) := by
      have : 2 ^ 5 ≤ 2 ^ (5 * T) := pow_le_pow_right₀ (by decide) (by omega)
      norm_num at this ⊢; omega
    calc
      20 * (E * (E * X)) ≤ 2 ^ (5 * T) * (E * (E * X)) := Nat.mul_le_mul_right _ h5
      _ = 2 ^ (5 * T + (29 * T + (29 * T + cE * T))) := by
        dsimp [E, X]; rw [← pow_add, ← pow_add, ← pow_add]
      _ ≤ 2 ^ ((cE + 63) * T) :=
        pow_le_pow_right₀ (by decide : 1 ≤ (2:Nat)) (by nlinarith)
  exact hwb.trans hpow

/-- One all-tape clock for the whole capped generator with ONE named premise:
the successful branch's charged handoff/prelude (`pre`) and the per-entry
evaluation clock (`Tent`) of its `EntryRuns` instance, each bounded by
`2^(c*(k+1)*L)` for fixed constants `cP`, `cE`. Failure tapes are covered by
the checked clock of segment 2c alone. -/
theorem composed_all_tape_clock_le {n m : Nat} [NeZero n]
    (L Δ : Nat) (γ : ℚ)
    (hc : Paper2.CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) L Δ γ) (k pre Tent cP cE : Nat)
    (hpre : pre ≤ 2 ^ (cP * (k + 1) * L))
    (hent : Tent ≤ 2 ^ (cE * (k + 1) * L)) :
    let p := LookupSeed.width L
    let s := SourceProfileParameters.width L
    let q₁ := SourceProfileParameters.width L - 2
    let q₂ := SourceProfileParameters.outerWidth L
    let w := restorationWidth L
    let Q := coverWidth n m L Δ γ
    let mX := sourceRows L (restorationDepth L) (coverDepth n m L Δ γ) k
    let mY := sourceCols L (restorationDepth L) (coverDepth n m L Δ γ) k
    SamplerFallbackJoin.clock n p s q₁ q₂ w Q k mX mY + pre +
        EthInapproximability.CurrentPaper.MatrixTableWriter.writerBound mX mY Tent ≤
      2 ^ ((FallbackNoPreloadRun.noPreloadExponent + cP + cE + 65) * (k + 1) * L) := by
  intro p s q₁ q₂ w Q mX mY
  let T := (k + 1) * L
  have hL : 16 ≤ L := by
    rcases hc with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hL, _⟩
    exact hL
  have hT : 1 ≤ T := by
    have hp : 0 < (k + 1) * L := Nat.mul_pos (by omega) (by omega)
    dsimp [T]; omega
  have h1 := FallbackNoPreloadEndpoint.scheduled_no_preload_clock_le L Δ γ hc k
  have h3 := scheduled_writerBound_entry_le L Δ γ hc k Tent cE hent
  let K := FallbackNoPreloadRun.noPreloadExponent + cP + cE + 63
  have mono : ∀ e, e ≤ K → 2 ^ (e * (k + 1) * L) ≤ 2 ^ (K * T) := fun e he =>
    pow_le_pow_right₀ (by decide : 1 ≤ (2:Nat))
      (by dsimp [T]; rw [Nat.mul_assoc]; exact Nat.mul_le_mul_right _ he)
  have g1 := h1.trans (mono _ (by dsimp [K]; omega))
  have g2 := hpre.trans (mono _ (by dsimp [K]; omega))
  have g3 := h3.trans (mono _ (by dsimp [K]; omega))
  have h4 : 4 * 2 ^ (K * T) ≤
      2 ^ ((FallbackNoPreloadRun.noPreloadExponent + cP + cE + 65) * (k + 1) * L) := by
    calc
      4 * 2 ^ (K * T) = 2 ^ (2 + K * T) := by rw [pow_add]; norm_num
      _ ≤ _ := pow_le_pow_right₀ (by decide : 1 ≤ (2:Nat)) (by dsimp [K, T]; nlinarith)
  have g1' : SamplerFallbackJoin.clock n p s q₁ q₂ w Q k mX mY ≤ 2 ^ (K * T) := g1
  have g3' : EthInapproximability.CurrentPaper.MatrixTableWriter.writerBound mX mY Tent ≤
      2 ^ (K * T) := g3
  omega

#print axioms scheduled_writerBound_entry_le
#print axioms composed_all_tape_clock_le

end Paper2.SuccessPremiseComposition
