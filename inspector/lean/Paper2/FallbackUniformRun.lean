import Paper2.FallbackUniformClock

/-! Unit 3, map item 6 (private): the actual all-tape run of the admitted
fixed program `CodeFallbackFullJoin.program` at the exact checked public
schedule of frozen v12 Appendix D, with ONE public clock
`2^(uniformExponent*(k+1)*L)` for every capped random tape, covering both
the exhausted-cap failure branch (physical zero table written by the fixed
fallback writer) and the success branch up to the interpreter's observed
sample word. Same run objects as the admitted
`CodeFallbackAllOutcomes.every_tape_halts_with_source_outcome`.

Initial-bank disclosure: the start bank is the admitted
`CodeFallbackEntryJoin.initial n p s q₁ q₂ w Q k mX mY word B R`; the public
unary counts, the written tape word and the two interpreter cap words `B,R`
are its initial contents (the admitted interface). The no-preloaded-`B/R`
producer is a separate private packet (`a-success-table-owner`
`SamplerFallbackJoin`), not used here. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

namespace Paper2.FallbackUniformRun

open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.SourceRecursiveNoSampling Paper2.ParameterizedCanonicalSource

/-- Every capped random tape: the fixed program halts within the one public
clock, and its halting bank satisfies the admitted outcome predicate for the
actual `GeneratorCode.run` on the same tape (`some bytes`: interpreter exit
with observed word and drained tape; `none`: the dimensioned all-false
row-major table written by the fixed fallback writer). -/
theorem scheduled_every_tape_halts {n m : Nat} [NeZero n]
    (L Δ : Nat) (γ : ℚ)
    (hc : Paper2.CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) L Δ γ) (k : Nat)
    (tape : CappedSampler.Adaptive.Tape
      (Nat.clog 2 (CodeFullRunConsumer.scheduledM n m L Δ γ))
      (Paper2.rejectionAttemptCap
        (CodeFullRunConsumer.scheduledN n m L Δ γ k
          (sourceRows L (restorationDepth L) (coverDepth n m L Δ γ) k)
          (sourceCols L (restorationDepth L) (coverDepth n m L Δ γ) k)))
      (CodeFullRunConsumer.scheduledN n m L Δ γ k
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
    let root := CodeFallbackSourceResult.sampleRoot n p s q₁ q₂ w Q k mX mY
    let B := Nat.clog 2 (CodeFullRunConsumer.scheduledM n m L Δ γ)
    let N := CodeFullRunConsumer.scheduledN n m L Δ γ k mX mY
    let R := Paper2.rejectionAttemptCap N
    ∃ clock ≤ 2 ^ (FallbackUniformClock.uniformExponent * (k + 1) * L),
      ∃ d : CodeTableFallback.Config,
        d.l = none ∧
        CodeFallbackAllOutcomes.Runs clock n p s q₁ q₂ w Q k mX mY
          (RecursiveSamplingTape.writeTape B R N tape).val B R d ∧
        CodeFallbackAllOutcomes.Outcome mX mY
          (GeneratorCode.run B R le_rfl N
            (GeneratorStateSize.initialBounded root
              (FallbackUniformClock.scheduled_alphabet_bound L Δ γ k))
            tape) d := by
  intro p s q₁ q₂ w Q mX mY root B N R
  have hs : 3 ≤ s := by
    have := SourceProfiles.width_ge_four L
    dsimp [s]; omega
  have hpos : GeneratorPositive.Positive root :=
    GeneratorPositive.positive_scheduledSampleCode L Δ γ k mX mY
  have hN : (meaning root).maxDraws ≤ N :=
    CodeFullRunConsumer.scheduled_sample_code_draw_cap L Δ γ k mX mY
  obtain ⟨clock, hclock, d, hd, hruns, hout⟩ :=
    CodeFallbackAllOutcomes.every_tape_halts_with_source_outcome
      n p s q₁ q₂ w Q k mX mY (CodeFullRunConsumer.scheduledM n m L Δ γ) B R N
      hs (FallbackUniformClock.scheduled_alphabet_bound L Δ γ k) le_rfl
      (CodeFullRun.scheduled_attempts_pos N) hpos hN tape
  have hbound := FallbackUniformClock.scheduled_outcome_clock_le L Δ γ hc k
  exact ⟨clock, hclock.trans hbound, d, hd, hruns, hout⟩

/-- The same clock in elementary polynomial form at the actual graph-size
exponent `L = ⌈log₂ n⌉` (explicit size cutoff, no promise), for `n ≥ 2`. -/
theorem at_size_clock_le_poly {n : Nat} (hn : 2 ≤ n) (C k : Nat) :
    2 ^ (C * (k + 1) * Nat.clog 2 n) ≤ n ^ (2 * C * (k + 1)) := by
  have hceil : 2 ^ Nat.clog 2 n ≤ n ^ 2 := by
    have h := CappedSampler.ticketSize_le_twice n (by omega)
    change 2 ^ Nat.clog 2 n ≤ 2 * n at h
    have htwice : 2 * n ≤ n ^ 2 := by nlinarith
    exact h.trans htwice
  calc
    2 ^ (C * (k + 1) * Nat.clog 2 n) = (2 ^ Nat.clog 2 n) ^ (C * (k + 1)) := by
      rw [← pow_mul]; congr 1; ring
    _ ≤ (n ^ 2) ^ (C * (k + 1)) := Nat.pow_le_pow_left hceil _
    _ = n ^ (2 * C * (k + 1)) := by rw [← pow_mul]; congr 1; ring

theorem at_size_every_tape_halts {n m : Nat} [NeZero n]
    (Δ : Nat) (γ : ℚ) (edge : Fin m → Bool → Fin n)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hsize : CompletePublicScheduleScratch.sizeThreshold Δ γ ≤ n)
    (hn : 2 ≤ n) (k : Nat)
    (tape : CappedSampler.Adaptive.Tape
      (Nat.clog 2 (CodeFullRunConsumer.scheduledM n m (Nat.clog 2 n) Δ γ))
      (Paper2.rejectionAttemptCap
        (CodeFullRunConsumer.scheduledN n m (Nat.clog 2 n) Δ γ k
          (sourceRows (Nat.clog 2 n) (restorationDepth (Nat.clog 2 n))
            (coverDepth n m (Nat.clog 2 n) Δ γ) k)
          (sourceCols (Nat.clog 2 n) (restorationDepth (Nat.clog 2 n))
            (coverDepth n m (Nat.clog 2 n) Δ γ) k)))
      (CodeFullRunConsumer.scheduledN n m (Nat.clog 2 n) Δ γ k
        (sourceRows (Nat.clog 2 n) (restorationDepth (Nat.clog 2 n))
          (coverDepth n m (Nat.clog 2 n) Δ γ) k)
        (sourceCols (Nat.clog 2 n) (restorationDepth (Nat.clog 2 n))
          (coverDepth n m (Nat.clog 2 n) Δ γ) k))) :
    let L := Nat.clog 2 n
    let p := LookupSeed.width L
    let s := SourceProfileParameters.width L
    let q₁ := SourceProfileParameters.width L - 2
    let q₂ := SourceProfileParameters.outerWidth L
    let w := restorationWidth L
    let Q := coverWidth n m L Δ γ
    let mX := sourceRows L (restorationDepth L) (coverDepth n m L Δ γ) k
    let mY := sourceCols L (restorationDepth L) (coverDepth n m L Δ γ) k
    let root := CodeFallbackSourceResult.sampleRoot n p s q₁ q₂ w Q k mX mY
    let B := Nat.clog 2 (CodeFullRunConsumer.scheduledM n m L Δ γ)
    let N := CodeFullRunConsumer.scheduledN n m L Δ γ k mX mY
    let R := Paper2.rejectionAttemptCap N
    ∃ clock ≤ n ^ (2 * FallbackUniformClock.uniformExponent * (k + 1)),
      ∃ d : CodeTableFallback.Config,
        d.l = none ∧
        CodeFallbackAllOutcomes.Runs clock n p s q₁ q₂ w Q k mX mY
          (RecursiveSamplingTape.writeTape B R N tape).val B R d ∧
        CodeFallbackAllOutcomes.Outcome mX mY
          (GeneratorCode.run B R le_rfl N
            (GeneratorStateSize.initialBounded root
              (FallbackUniformClock.scheduled_alphabet_bound L Δ γ k))
            tape) d := by
  intro L p s q₁ q₂ w Q mX mY root B N R
  obtain ⟨clock, hclock, d, hd, hruns, hout⟩ :=
    scheduled_every_tape_halts L Δ γ
      (checksAtSize Δ γ edge hγ hΔ hincident hdegree hsize) k tape
  exact ⟨clock, hclock.trans
    (at_size_clock_le_poly hn FallbackUniformClock.uniformExponent k),
    d, hd, hruns, hout⟩

#print axioms scheduled_every_tape_halts
#print axioms at_size_clock_le_poly
#print axioms at_size_every_tape_halts

end Paper2.FallbackUniformRun
