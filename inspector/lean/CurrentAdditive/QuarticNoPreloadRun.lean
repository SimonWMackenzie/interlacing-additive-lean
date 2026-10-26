import CurrentAdditive.QuarticNoPreloadClock
import Paper2.FallbackNoPreloadEndpoint

/-! The fixed, no-preload sampler at the literal v27 quartic dimensions. -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 2048

namespace Paper2.CurrentAdditive.QuarticNoPreloadRun

open Turing
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.SourceRecursiveNoSampling Paper2.ParameterizedCanonicalSource
open CurrentAdditive.RandomizedSchedule

theorem every_tape_halts27 {n m : Nat} [NeZero n]
    (L Δ : Nat) (γ : ℚ)
    [NeZero (SourceProfileParameters.width L - 2)]
    [NeZero (SourceProfileParameters.outerWidth L)]
    [NeZero (width27 L)]
    [NeZero (Q27 (V := Fin n) (E := Fin m) L γ Δ)]
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) L Δ γ) (k : Nat)
    (tape : CappedSampler.Adaptive.Tape
      (SamplerFallbackJoin.Bv n (LookupSeed.width L)
        (SourceProfileParameters.width L) (SourceProfileParameters.width L - 2)
        (SourceProfileParameters.outerWidth L) (width27 L)
        (Q27 (V := Fin n) (E := Fin m) L γ Δ))
      (SamplerFallbackJoin.Rv (LookupSeed.width L)
        (SourceProfileParameters.width L) (SourceProfileParameters.width L - 2)
        (SourceProfileParameters.outerWidth L) (width27 L)
        (Q27 (V := Fin n) (E := Fin m) L γ Δ) k
        (sourceRows L (4 * RestorationWidthScheduleScratch.ell L)
          (q27 (V := Fin n) (E := Fin m) L γ Δ) k)
        (sourceCols L (4 * RestorationWidthScheduleScratch.ell L)
          (q27 (V := Fin n) (E := Fin m) L γ Δ) k))
      (SamplerFallbackJoin.Nv (LookupSeed.width L)
        (SourceProfileParameters.width L) (SourceProfileParameters.width L - 2)
        (SourceProfileParameters.outerWidth L) (width27 L)
        (Q27 (V := Fin n) (E := Fin m) L γ Δ) k
        (sourceRows L (4 * RestorationWidthScheduleScratch.ell L)
          (q27 (V := Fin n) (E := Fin m) L γ Δ) k)
        (sourceCols L (4 * RestorationWidthScheduleScratch.ell L)
          (q27 (V := Fin n) (E := Fin m) L γ Δ) k))) :
    let p := LookupSeed.width L
    let s := SourceProfileParameters.width L
    let q₁ := SourceProfileParameters.width L - 2
    let q₂ := SourceProfileParameters.outerWidth L
    let w := width27 L
    let Q := Q27 (V := Fin n) (E := Fin m) L γ Δ
    let mX := sourceRows L (4 * RestorationWidthScheduleScratch.ell L)
      (q27 (V := Fin n) (E := Fin m) L γ Δ) k
    let mY := sourceCols L (4 * RestorationWidthScheduleScratch.ell L)
      (q27 (V := Fin n) (E := Fin m) L γ Δ) k
    let B := SamplerFallbackJoin.Bv n p s q₁ q₂ w Q
    let R := SamplerFallbackJoin.Rv p s q₁ q₂ w Q k mX mY
    let N := SamplerFallbackJoin.Nv p s q₁ q₂ w Q k mX mY
    let word := (RecursiveSamplingTape.writeTape B R N tape).val
    ∃ t ≤ 2 ^ (FallbackNoPreloadRun.noPreloadExponent * (k + 1) * L),
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
              (SamplerFallbackJoin.alphabet_bound n p s q₁ q₂ w Q k mX mY
                (NeZero.pos n)
                (by show 0 < LookupSeed.width L; unfold LookupSeed.width; positivity)
                (SourceProfiles.width_ge_four L) (NeZero.pos q₁) (NeZero.pos q₂)
                (NeZero.pos w) (NeZero.pos Q)))
            tape) d := by
  intro p s q₁ q₂ w Q mX mY B R N word
  have hn : 0 < n := NeZero.pos n
  have hp : 0 < p := by dsimp [p]; unfold LookupSeed.width; positivity
  have hs : 4 ≤ s := SourceProfiles.width_ge_four L
  have hq₁ : 0 < q₁ := NeZero.pos q₁
  have hq₂ : 0 < q₂ := NeZero.pos q₂
  have hw : 0 < w := NeZero.pos w
  have hQ : 0 < Q := NeZero.pos Q
  obtain ⟨t, ht, d, G, hd, hG, hr, hout⟩ :=
    SamplerFallbackJoin.every_tape_halts_no_preload n p s q₁ q₂ w Q k mX mY
      hn hp hs hq₁ hq₂ hw hQ tape
  exact ⟨t, ht.trans (QuarticNoPreloadClock.no_preload_clock27 L Δ γ hc k),
    d, G, hd, hG, hr, hout⟩

#print axioms every_tape_halts27

end Paper2.CurrentAdditive.QuarticNoPreloadRun
