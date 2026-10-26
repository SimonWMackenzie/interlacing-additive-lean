import Paper2.FallbackNoPreloadRun

/-! Unit 3, map item 6 (private): the no-preloaded-`B/R` fixed program
`SamplerFallbackJoin.program` at the exact checked schedule of frozen v12
Appendix D halts on EVERY capped random tape within the one public clock
`2^(noPreloadExponent*(k+1)*L)`, with the admitted outcome predicate for the
actual `GeneratorCode.run` on the same tape. Initial data: the raw public
unary counts and the written tape word only (both interpreter cap cells
start empty and are produced physically). -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 2048

namespace Paper2.FallbackNoPreloadEndpoint

open Turing
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.SourceRecursiveNoSampling Paper2.ParameterizedCanonicalSource
open Paper2.FallbackNoPreloadClock Paper2.FallbackNoPreloadRun

theorem scheduled_no_preload_clock_le {n m : Nat} [NeZero n]
    (L Δ : Nat) (γ : ℚ)
    (hc : Paper2.CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) L Δ γ) (k : Nat) :
    SamplerFallbackJoin.clock n (LookupSeed.width L)
      (SourceProfileParameters.width L) (SourceProfileParameters.width L - 2)
      (SourceProfileParameters.outerWidth L) (restorationWidth L)
      (coverWidth n m L Δ γ) k
      (sourceRows L (restorationDepth L) (coverDepth n m L Δ γ) k)
      (sourceCols L (restorationDepth L) (coverDepth n m L Δ γ) k) ≤
      2 ^ (noPreloadExponent * (k + 1) * L) := by
  let T := (k + 1) * L
  have hL : 16 ≤ L := by
    rcases hc with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hL, _⟩
    exact hL
  have hT : 1 ≤ T := by
    have hp : 0 < (k + 1) * L := Nat.mul_pos (by omega) (by omega)
    dsimp [T]; omega
  have hspj := scheduled_atoms L Δ γ hc k
  dsimp only at hspj
  have hfb := FallbackUniformClock.scheduled_outcome_clock_le L Δ γ hc k
  dsimp only at hfb
  have hZ3 : (2 ^ (60 * ((k + 1) * L))) ^ 3 ≤ 2 ^ (180 * T) := by
    rw [← pow_mul]; dsimp [T]; apply le_of_eq; congr 1; ring
  have hab := absorb2 (8 * cf + 27100) FallbackUniformClock.uniformExponent T
    ((2 ^ (60 * ((k + 1) * L))) ^ 3) hT hZ3
  have e1 : FallbackUniformClock.uniformExponent * (k + 1) * L =
      FallbackUniformClock.uniformExponent * T := by dsimp [T]; ring
  have e2 : noPreloadExponent * (k + 1) * L =
      (FallbackUniformClock.uniformExponent + (8 * cf + 27100) + 182) * T := by
    dsimp [T, noPreloadExponent]; ring
  rw [e1] at hfb
  rw [e2]
  have hfb' : SamplerFallbackJoin.fallbackCap n (LookupSeed.width L)
      (SourceProfileParameters.width L) (SourceProfileParameters.width L - 2)
      (SourceProfileParameters.outerWidth L) (restorationWidth L)
      (coverWidth n m L Δ γ) k
      (sourceRows L (restorationDepth L) (coverDepth n m L Δ γ) k)
      (sourceCols L (restorationDepth L) (coverDepth n m L Δ γ) k) ≤
      2 ^ (FallbackUniformClock.uniformExponent * T) := hfb
  unfold SamplerFallbackJoin.clock
  exact (Nat.add_le_add (Nat.add_le_add hspj le_rfl) hfb').trans hab

/-- Every capped random tape: the no-preload fixed program halts within the
public clock, with the admitted outcome predicate on the same tape. -/
theorem scheduled_every_tape_halts_no_preload {n m : Nat} [NeZero n]
    (L Δ : Nat) (γ : ℚ)
    (hc : Paper2.CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) L Δ γ) (k : Nat)
    (tape : CappedSampler.Adaptive.Tape
      (SamplerFallbackJoin.Bv n (LookupSeed.width L)
        (SourceProfileParameters.width L) (SourceProfileParameters.width L - 2)
        (SourceProfileParameters.outerWidth L) (restorationWidth L)
        (coverWidth n m L Δ γ))
      (SamplerFallbackJoin.Rv (LookupSeed.width L)
        (SourceProfileParameters.width L) (SourceProfileParameters.width L - 2)
        (SourceProfileParameters.outerWidth L) (restorationWidth L)
        (coverWidth n m L Δ γ) k
        (sourceRows L (restorationDepth L) (coverDepth n m L Δ γ) k)
        (sourceCols L (restorationDepth L) (coverDepth n m L Δ γ) k))
      (SamplerFallbackJoin.Nv (LookupSeed.width L)
        (SourceProfileParameters.width L) (SourceProfileParameters.width L - 2)
        (SourceProfileParameters.outerWidth L) (restorationWidth L)
        (coverWidth n m L Δ γ) k
        (sourceRows L (restorationDepth L) (coverDepth n m L Δ γ) k)
        (sourceCols L (restorationDepth L) (coverDepth n m L Δ γ) k))) :
    let p := LookupSeed.width L
    let s := SourceProfileParameters.width L
    let q₁ := SourceProfileParameters.width L - 2
    let q₂ := SourceProfileParameters.outerWidth L
    let w := restorationWidth L
    let Q := coverWidth n m L Δ γ
    let mX := sourceRows L (restorationDepth L) (coverDepth n m L Δ γ) k
    let mY := sourceCols L (restorationDepth L) (coverDepth n m L Δ γ) k
    let B := SamplerFallbackJoin.Bv n p s q₁ q₂ w Q
    let R := SamplerFallbackJoin.Rv p s q₁ q₂ w Q k mX mY
    let N := SamplerFallbackJoin.Nv p s q₁ q₂ w Q k mX mY
    let word := (RecursiveSamplingTape.writeTape B R N tape).val
    ∃ t ≤ 2 ^ (noPreloadExponent * (k + 1) * L),
      ∃ (d : CodeTableFallback.Config)
        (G : SamplerParameterBank.Private → List Bool),
        d.l = none ∧ G (.inr (.inr 0)) = [] ∧
        ((EthInapproximability.CurrentPaper.BitMachineEncoding.advance
            SamplerFallbackJoin.program)^[t])
          (⟨some SamplerFallbackJoin.startLabel, SamplerFallbackJoin.startControl,
            SamplerParameterJoin.startBank n p s q₁ q₂ w Q k mX mY word⟩ :
            TM2.Cfg (fun _ : SamplerParameterBank.Stack => Bool) _ _) =
          ⟨none, (SamplerParameterJoin.startControl,
              (CodeFallbackFullJoin.prepControl, d.var)),
            Sum.elim (CodeFallbackSourceResult.finalBank n p s q₁ q₂ w Q k mX mY
              word B R d) G⟩ ∧
        CodeFallbackAllOutcomes.Outcome mX mY
          (GeneratorCode.run B R (le_refl _) N
            (GeneratorStateSize.initialBounded
              (SamplerFallbackJoin.root n p s q₁ q₂ w Q k mX mY)
              (FallbackUniformClock.scheduled_alphabet_bound L Δ γ k))
            tape) d := by
  intro p s q₁ q₂ w Q mX mY B R N word
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hp : 0 < p := by dsimp [p]; unfold LookupSeed.width; positivity
  have hs : 4 ≤ s := SourceProfiles.width_ge_four L
  have hq₁ : 0 < q₁ := by
    have h := SourceProfileParameters.width_admissible L
    dsimp [q₁]; omega
  have hq₂ : 0 < q₂ := by
    dsimp [q₂]; unfold SourceProfileParameters.outerWidth; positivity
  have hw : 0 < w := by
    dsimp [w]
    unfold ParameterizedCanonicalSource.restorationWidth
      RestorationWidthScheduleScratch.width
    positivity
  have hQ : 0 < Q := by
    dsimp [Q]
    rw [show ParameterizedCanonicalSource.coverWidth n m L Δ γ =
      2 ^ ParameterizedCanonicalSource.coverDepth n m L Δ γ from
      SourceOverheadBounds.actualQ_pow (V := Fin n) (E := Fin m) L γ Δ]
    positivity
  obtain ⟨t, ht, d, G, hd, hG, hr, hout⟩ :=
    SamplerFallbackJoin.every_tape_halts_no_preload n p s q₁ q₂ w Q k mX mY
      hn hp hs hq₁ hq₂ hw hQ tape
  exact ⟨t, ht.trans (scheduled_no_preload_clock_le L Δ γ hc k), d, G, hd, hG,
    hr, hout⟩

#print axioms scheduled_no_preload_clock_le
#print axioms scheduled_every_tape_halts_no_preload

end Paper2.FallbackNoPreloadEndpoint
