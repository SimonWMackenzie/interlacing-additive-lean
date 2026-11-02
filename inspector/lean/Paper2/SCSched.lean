import Paper2.SCBody
import Paper2.SuccessPremiseComposition

/-! Unit 3, clock bounds, segments (2) and (4) at the public schedule: owner-8's per-entry
clock `WEntry.Tent`, at the literal schedule widths and every sample of the scheduled
dimensions, is at most `2^(cE*(K+1)*L)` with the absolute constant
`cE = a + 2*(RLoop.NX + RLoop.N1 + StepXGrowth.pushBound) + 316 + 360`, where `a` is the exponent of
FOUR named component bounds that are NOT discharged here (see `CHECKPOINT.md`):
the level step clock `RLoop.stepClock`, the admitted `NavJoin.joinBound`, the master-region
length and the step-entry bank length. Every other ingredient is discharged from the admitted
schedule caps (`SCCaps`). The result is then fed, unchanged, to the admitted consumer
`SuccessPremiseComposition.composed_all_tape_clock_le`. -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

namespace Paper2.SuccessClock

open EthInapproximability.CurrentPaper
open Paper2.GeneratorCode Paper2.GeneratorSerialization Paper2.GeneratorSource
  Paper2.RecursiveLabelCodecScratch Paper2.RecursiveEntries Paper2.ParameterizedCanonicalSource
  Paper2.SourceProfileParameters

/-- The absolute exponent constant of the success-branch per-entry clock (given the
component exponent `a`). -/
noncomputable def entryExponent (a : ℕ) : ℕ :=
  a + 2 * (RLoop.NX + RLoop.N1 + StepXGrowth.pushBound) + 316 + 360

theorem Tent_sched (L Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) (hg : g.Valid)
    [NeZero g.vertices] [NeZero (width L)] [NeZero (width L - 2)] [NeZero (outerWidth L)]
    [NeZero (restorationWidth L)] [NeZero (coverWidth g.vertices g.edges.length L Δ γ)]
    (hc : Paper2.CompletePublicScheduleScratch.Checks
      (V := Fin g.vertices) (E := Fin g.edges.length) L Δ γ)
    (r : ℕ) (hq : outerWidth L = SourceItems.sourceQ0 (Fin (4 * width L)) (Fin g.edges.length) * r)
    (ξ : Tails (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
      (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
      (outerWidth L) (restorationWidth L) (coverWidth g.vertices g.edges.length L Δ γ))
    (K : ℕ)
    (xs : Fin (SourceRecursiveNoSampling.sourceRows L (restorationDepth L)
        (coverDepth g.vertices g.edges.length L Δ γ) K) →
      Row (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
        (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
        (outerWidth L) (restorationWidth L) (coverWidth g.vertices g.edges.length L Δ γ) K)
    (ys : Fin (SourceRecursiveNoSampling.sourceCols L (restorationDepth L)
        (coverDepth g.vertices g.edges.length L Δ γ) K) →
      Column (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
        (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
        (outerWidth L) (restorationWidth L) (coverWidth g.vertices g.edges.length L Δ γ) K)
    (a : ℕ)
    (Hstep : ∀ k, k + 1 ≤ K →
      ∀ (x : Row (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
          (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
          (outerWidth L) (restorationWidth L) (coverWidth g.vertices g.edges.length L Δ γ) (k + 1))
        (y : Column (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
          (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
          (outerWidth L) (restorationWidth L) (coverWidth g.vertices g.edges.length L Δ γ) (k + 1)),
        RLoop.stepClock g hg (SourceProfiles.width_ge_four L) r hq ξ k x y ≤ 2 ^ (a * ((K + 1) * L)))
    (Hjoin : ∀ k, k + 1 ≤ K →
      NavJoin.joinBound g.vertices (LookupSeed.width L) (width L) (width L - 2) (outerWidth L)
        (restorationWidth L) (coverWidth g.vertices g.edges.length L Δ γ) k ≤
        2 ^ (a * ((K + 1) * L)))
    (Hmaster : (∑ z : SrcX.JX, (RLoop.master (p := LookupSeed.width L) (s := width L)
      (q₁ := width L - 2) (q₂ := outerWidth L) (w := restorationWidth L)
      (Q := coverWidth g.vertices g.edges.length L Δ γ) g r z).length) ≤ 2 ^ (a * ((K + 1) * L)))
    (Hbank : ∀ k, k + 1 ≤ K →
      ∀ (x : Row (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
          (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
          (outerWidth L) (restorationWidth L) (coverWidth g.vertices g.edges.length L Δ γ) (k + 1))
        (y : Column (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
          (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
          (outerWidth L) (restorationWidth L) (coverWidth g.vertices g.edges.length L Δ γ) (k + 1)),
        (∑ b : TemplateStepX.JT, ((Sum.elim (TemplateStepX.W0f k x y)
          (RLoop.E0k (p := LookupSeed.width L) (s := width L) (q₁ := width L - 2)
            (q₂ := outerWidth L) (w := restorationWidth L)
            (Q := coverWidth g.vertices g.edges.length L Δ γ) g r k)) b).length) ≤
          2 ^ (a * ((K + 1) * L))) :
    WEntry.Tent g hg (SourceProfiles.width_ge_four L) r hq ξ K _ _ xs ys ≤
      2 ^ (entryExponent a * (K + 1) * L) := by
  obtain ⟨_, hp, _, hq₁, _, _, _, _, hL⟩ := scalar_caps L Δ γ hc
  have hT : 1 ≤ (K + 1) * L := by nlinarith
  have hKT : K ≤ (K + 1) * L := by nlinarith
  have h7 : 2 ^ (7 * L) ≤ 2 ^ (7 * ((K + 1) * L)) :=
    pow_le_pow_right₀ (by norm_num) (by nlinarith)
  obtain ⟨hmX, hmY⟩ := dims_cap L Δ γ hc K
  have hbody : ∀ k, k + 1 ≤ K → ∀ x y,
      RLoop.bodyClock g hg (SourceProfiles.width_ge_four L) r hq ξ k x y ≤
        2 ^ ((a + 2 * (RLoop.NX + RLoop.N1 + StepXGrowth.pushBound) + 316) * ((K + 1) * L)) := by
    intro k hk x y
    exact bodyClock_le g hg (SourceProfiles.width_ge_four L) r hq ξ k x y ((K + 1) * L) a hT
      (by nlinarith) (hq₁.trans h7) (code_cap L Δ γ hc K (k + 1) (by omega))
      (code_cap L Δ γ hc K k (by omega)) (label_cap L Δ γ hc K k (by omega))
      (Hstep k hk x y) (Hjoin k hk) Hmaster (Hbank k hk x y)
  have hloop : ∀ i j, RLoop.loopBd g hg (SourceProfiles.width_ge_four L) r hq ξ K (xs i) (ys j) ≤
      2 ^ ((a + 2 * (RLoop.NX + RLoop.N1 + StepXGrowth.pushBound) + 316) * ((K + 1) * L)) :=
    fun i j => loopBd_le g hg (SourceProfiles.width_ge_four L) r hq ξ K (xs i) (ys j) _ hbody
  have h := Tent_le g hg (SourceProfiles.width_ge_four L) r hq ξ K _ _ xs ys ((K + 1) * L)
    (a + 2 * (RLoop.NX + RLoop.N1 + StepXGrowth.pushBound) + 316) hT hKT (hp.trans h7)
    (code_cap L Δ γ hc K K (by omega)) (code_cap L Δ γ hc K 0 (by omega))
    (label_cap L Δ γ hc K K le_rfl) (label_cap L Δ γ hc K 0 (by omega)) hmX hmY hloop
  rw [Nat.mul_assoc]
  exact h

/-- Segment (4): the success-branch per-entry clock in exactly the shape consumed by the
admitted `SuccessPremiseComposition.composed_all_tape_clock_le`, composed with it. The
prelude clock `pre` stays the consumer's own named premise `hpre`. -/
theorem success_clock_composed (L Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) (hg : g.Valid)
    [NeZero g.vertices] [NeZero (width L)] [NeZero (width L - 2)] [NeZero (outerWidth L)]
    [NeZero (restorationWidth L)] [NeZero (coverWidth g.vertices g.edges.length L Δ γ)]
    (hc : Paper2.CompletePublicScheduleScratch.Checks
      (V := Fin g.vertices) (E := Fin g.edges.length) L Δ γ)
    (r : ℕ) (hq : outerWidth L = SourceItems.sourceQ0 (Fin (4 * width L)) (Fin g.edges.length) * r)
    (ξ : Tails (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
      (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
      (outerWidth L) (restorationWidth L) (coverWidth g.vertices g.edges.length L Δ γ))
    (K : ℕ)
    (xs : Fin (SourceRecursiveNoSampling.sourceRows L (restorationDepth L)
        (coverDepth g.vertices g.edges.length L Δ γ) K) →
      Row (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
        (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
        (outerWidth L) (restorationWidth L) (coverWidth g.vertices g.edges.length L Δ γ) K)
    (ys : Fin (SourceRecursiveNoSampling.sourceCols L (restorationDepth L)
        (coverDepth g.vertices g.edges.length L Δ γ) K) →
      Column (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
        (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
        (outerWidth L) (restorationWidth L) (coverWidth g.vertices g.edges.length L Δ γ) K)
    (a pre cP : ℕ) (hpre : pre ≤ 2 ^ (cP * (K + 1) * L))
    (Hstep : ∀ k, k + 1 ≤ K →
      ∀ (x : Row (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
          (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
          (outerWidth L) (restorationWidth L) (coverWidth g.vertices g.edges.length L Δ γ) (k + 1))
        (y : Column (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
          (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
          (outerWidth L) (restorationWidth L) (coverWidth g.vertices g.edges.length L Δ γ) (k + 1)),
        RLoop.stepClock g hg (SourceProfiles.width_ge_four L) r hq ξ k x y ≤ 2 ^ (a * ((K + 1) * L)))
    (Hjoin : ∀ k, k + 1 ≤ K →
      NavJoin.joinBound g.vertices (LookupSeed.width L) (width L) (width L - 2) (outerWidth L)
        (restorationWidth L) (coverWidth g.vertices g.edges.length L Δ γ) k ≤
        2 ^ (a * ((K + 1) * L)))
    (Hmaster : (∑ z : SrcX.JX, (RLoop.master (p := LookupSeed.width L) (s := width L)
      (q₁ := width L - 2) (q₂ := outerWidth L) (w := restorationWidth L)
      (Q := coverWidth g.vertices g.edges.length L Δ γ) g r z).length) ≤ 2 ^ (a * ((K + 1) * L)))
    (Hbank : ∀ k, k + 1 ≤ K →
      ∀ (x : Row (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
          (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
          (outerWidth L) (restorationWidth L) (coverWidth g.vertices g.edges.length L Δ γ) (k + 1))
        (y : Column (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
          (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
          (outerWidth L) (restorationWidth L) (coverWidth g.vertices g.edges.length L Δ γ) (k + 1)),
        (∑ b : TemplateStepX.JT, ((Sum.elim (TemplateStepX.W0f k x y)
          (RLoop.E0k (p := LookupSeed.width L) (s := width L) (q₁ := width L - 2)
            (q₂ := outerWidth L) (w := restorationWidth L)
            (Q := coverWidth g.vertices g.edges.length L Δ γ) g r k)) b).length) ≤
          2 ^ (a * ((K + 1) * L))) :
    SamplerFallbackJoin.clock g.vertices (LookupSeed.width L) (width L) (width L - 2)
        (outerWidth L) (restorationWidth L) (coverWidth g.vertices g.edges.length L Δ γ) K
        (SourceRecursiveNoSampling.sourceRows L (restorationDepth L)
          (coverDepth g.vertices g.edges.length L Δ γ) K)
        (SourceRecursiveNoSampling.sourceCols L (restorationDepth L)
          (coverDepth g.vertices g.edges.length L Δ γ) K) + pre +
      MatrixTableWriter.writerBound
        (SourceRecursiveNoSampling.sourceRows L (restorationDepth L)
          (coverDepth g.vertices g.edges.length L Δ γ) K)
        (SourceRecursiveNoSampling.sourceCols L (restorationDepth L)
          (coverDepth g.vertices g.edges.length L Δ γ) K)
        (WEntry.Tent g hg (SourceProfiles.width_ge_four L) r hq ξ K _ _ xs ys) ≤
      2 ^ ((FallbackNoPreloadRun.noPreloadExponent + cP + entryExponent a + 65) * (K + 1) * L) :=
  SuccessPremiseComposition.composed_all_tape_clock_le L Δ γ hc K pre _ cP (entryExponent a) hpre
    (Tent_sched L Δ γ g hg hc r hq ξ K xs ys a Hstep Hjoin Hmaster Hbank)

end Paper2.SuccessClock

#print axioms Paper2.SuccessClock.Tent_sched
#print axioms Paper2.SuccessClock.success_clock_composed
