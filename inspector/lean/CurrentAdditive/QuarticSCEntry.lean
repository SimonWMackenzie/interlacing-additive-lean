import CurrentAdditive.QuarticSC2Bank
import Paper2.SCSched

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

namespace Paper2.CurrentAdditive.QuarticSCEntry

open EthInapproximability.CurrentPaper
open Paper2.GeneratorCode Paper2.GeneratorSerialization Paper2.GeneratorSource
  Paper2.RecursiveLabelCodecScratch Paper2.RecursiveEntries Paper2.ParameterizedCanonicalSource
  Paper2.SourceProfileParameters Paper2.SuccessClock Paper2.CurrentAdditive.QuarticClockCaps
open CurrentAdditive.RandomizedSchedule

theorem Tent_sched27 (L Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) (hg : g.Valid)
    [NeZero g.vertices] [NeZero (width L)] [NeZero (width L - 2)] [NeZero (outerWidth L)]
    [NeZero (width27 L)] [NeZero (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ)]
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin g.vertices) (Edges := Fin g.edges.length) L Δ γ)
    (r : ℕ) (hq : outerWidth L = SourceItems.sourceQ0 (Fin (4 * width L)) (Fin g.edges.length) * r)
    (ξ : Tails (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
      (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
      (outerWidth L) (width27 L) (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ))
    (K : ℕ)
    (xs : Fin (SourceRecursiveNoSampling.sourceRows L (4 * RestorationWidthScheduleScratch.ell L)
        (q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) K) →
      Row (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
        (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
        (outerWidth L) (width27 L) (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) K)
    (ys : Fin (SourceRecursiveNoSampling.sourceCols L (4 * RestorationWidthScheduleScratch.ell L)
        (q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) K) →
      Column (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
        (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
        (outerWidth L) (width27 L) (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) K)
    (a : ℕ)
    (Hstep : ∀ k, k + 1 ≤ K →
      ∀ (x : Row (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
          (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
          (outerWidth L) (width27 L) (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) (k + 1))
        (y : Column (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
          (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
          (outerWidth L) (width27 L) (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) (k + 1)),
        RLoop.stepClock g hg (SourceProfiles.width_ge_four L) r hq ξ k x y ≤ 2 ^ (a * ((K + 1) * L)))
    (Hjoin : ∀ k, k + 1 ≤ K →
      NavJoin.joinBound g.vertices (LookupSeed.width L) (width L) (width L - 2) (outerWidth L)
        (width27 L) (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) k ≤
        2 ^ (a * ((K + 1) * L)))
    (Hmaster : (∑ z : SrcX.JX, (RLoop.master (p := LookupSeed.width L) (s := width L)
      (q₁ := width L - 2) (q₂ := outerWidth L) (w := width27 L)
      (Q := Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) g r z).length) ≤ 2 ^ (a * ((K + 1) * L)))
    (Hbank : ∀ k, k + 1 ≤ K →
      ∀ (x : Row (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
          (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
          (outerWidth L) (width27 L) (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) (k + 1))
        (y : Column (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
          (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
          (outerWidth L) (width27 L) (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) (k + 1)),
        (∑ b : TemplateStepX.JT, ((Sum.elim (TemplateStepX.W0f k x y)
          (RLoop.E0k (p := LookupSeed.width L) (s := width L) (q₁ := width L - 2)
            (q₂ := outerWidth L) (w := width27 L)
            (Q := Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) g r k)) b).length) ≤
          2 ^ (a * ((K + 1) * L))) :
    WEntry.Tent g hg (SourceProfiles.width_ge_four L) r hq ξ K _ _ xs ys ≤
      2 ^ (entryExponent a * (K + 1) * L) := by
  obtain ⟨_, _, hp, _, hq₁, _, _, _, _, hL⟩ := scalar_caps27 L Δ γ hc
  have hT : 1 ≤ (K + 1) * L := by nlinarith
  have hKT : K ≤ (K + 1) * L := by nlinarith
  have h7 : 2 ^ (7 * L) ≤ 2 ^ (7 * ((K + 1) * L)) :=
    pow_le_pow_right₀ (by norm_num) (by nlinarith)
  obtain ⟨hmX, hmY⟩ := dims_cap27 L Δ γ hc K
  rw [Nat.mul_assoc] at hmX hmY
  have hbody : ∀ k, k + 1 ≤ K → ∀ x y,
      RLoop.bodyClock g hg (SourceProfiles.width_ge_four L) r hq ξ k x y ≤
        2 ^ ((a + 2 * (RLoop.NX + RLoop.N1 + StepXGrowth.pushBound) + 316) * ((K + 1) * L)) := by
    intro k hk x y
    exact bodyClock_le g hg (SourceProfiles.width_ge_four L) r hq ξ k x y ((K + 1) * L) a hT
      (by nlinarith) (hq₁.trans h7) (code_cap27 L Δ γ hc K (k + 1) (by omega))
      (code_cap27 L Δ γ hc K k (by omega)) (label_cap27 L Δ γ hc K k (by omega))
      (Hstep k hk x y) (Hjoin k hk) Hmaster (Hbank k hk x y)
  have hloop : ∀ i j, RLoop.loopBd g hg (SourceProfiles.width_ge_four L) r hq ξ K (xs i) (ys j) ≤
      2 ^ ((a + 2 * (RLoop.NX + RLoop.N1 + StepXGrowth.pushBound) + 316) * ((K + 1) * L)) :=
    fun i j => loopBd_le g hg (SourceProfiles.width_ge_four L) r hq ξ K (xs i) (ys j) _ hbody
  have h := Tent_le g hg (SourceProfiles.width_ge_four L) r hq ξ K _ _ xs ys ((K + 1) * L)
    (a + 2 * (RLoop.NX + RLoop.N1 + StepXGrowth.pushBound) + 316) hT hKT (hp.trans h7)
    (code_cap27 L Δ γ hc K K (by omega)) (code_cap27 L Δ γ hc K 0 (by omega))
    (label_cap27 L Δ γ hc K K le_rfl) (label_cap27 L Δ γ hc K 0 (by omega)) hmX hmY hloop
  rw [Nat.mul_assoc]
  exact h

end Paper2.CurrentAdditive.QuarticSCEntry

#print axioms Paper2.CurrentAdditive.QuarticSCEntry.Tent_sched27
