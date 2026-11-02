import CurrentAdditive.QuarticSC2Sched
import Paper2.SC2Bank

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

namespace Paper2.CurrentAdditive.QuarticSC2Bank

open EthInapproximability.CurrentPaper
open Paper2.GeneratorCode Paper2.GeneratorSerialization Paper2.GeneratorSource
  Paper2.RecursiveLabelCodecScratch Paper2.RecursiveEntries Paper2.ParameterizedCanonicalSource
  Paper2.SourceProfileParameters Paper2.SuccessClock2 Paper2.CurrentAdditive.QuarticSC2Sched
open CurrentAdditive.RandomizedSchedule Paper2.CurrentAdditive.QuarticClockCaps

theorem master_sched_le (L Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) (hg : g.Valid)
    [NeZero g.vertices] [NeZero (width L)] [NeZero (width L - 2)] [NeZero (outerWidth L)]
    [NeZero (width27 L)] [NeZero (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ)]
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin g.vertices) (Edges := Fin g.edges.length) L Δ γ)
    (r : ℕ) (hq : outerWidth L = SourceItems.sourceQ0 (Fin (4 * width L)) (Fin g.edges.length) * r)
    (K : ℕ) :
    (∑ z : SrcX.JX, (RLoop.master (p := LookupSeed.width L) (s := width L)
      (q₁ := width L - 2) (q₂ := outerWidth L) (w := width27 L)
      (Q := Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) g r z).length) ≤
      4 * 2 ^ (289 * ((K + 1) * L)) := by
  have hM := master_sum_le (p := LookupSeed.width L) (s := width L)
      (q₁ := width L - 2) (q₂ := outerWidth L) (w := width27 L)
      (Q := Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) g r
  have hW := WXb_sum_le (p := LookupSeed.width L) (s := width L)
      (q₁ := width L - 2) (q₂ := outerWidth L) (w := width27 L)
      (Q := Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) g r
  obtain ⟨_, hn, hp, hs, hq₁, hq₂, hw, hQ, hm, hL⟩ :=
    scalar_caps27 (n := g.vertices) (m := g.edges.length) L Δ γ hc
  dsimp [Paper2.GeneratorPublicCap.publicCap] at hn hp hs hq₁ hq₂ hw hQ hm
  have hLT : L ≤ (K + 1) * L := by nlinarith
  have hr : r ≤ outerWidth L := Paper2.SuccessClock.rep_le_outer (NeZero.pos (outerWidth L)) hq
  have hc0 := code_cap27 (n := g.vertices) (m := g.edges.length) L Δ γ hc K 0
    (by omega)
  have hc1 := code_cap27 (n := g.vertices) (m := g.edges.length) L Δ γ hc K 1
    (by omega)
  obtain ⟨-, -, hO, -, -, -, -⟩ := Paper2.SuccessClock.derived_le (n := g.vertices) (s := width L)
    (q₁ := width L - 2) (q₂ := outerWidth L) (NeZero.pos (width27 L))
    (NeZero.pos (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ))
    (copies (LookupSeed.width L) .bit) (.ticket (LookupSeed.width L)) 0
  change codeSize (outerCode (width L - 2) (outerWidth L) (width L)
      (seedRecursiveCodes g.vertices (LookupSeed.width L) (width L) (width L - 2) (outerWidth L)
        (width27 L) (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) 0).2) ≤
    codeSize (seedRecursiveCodes g.vertices (LookupSeed.width L) (width L) (width L - 2)
      (outerWidth L) (width27 L) (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) 1).1 at hO
  have hZ : 2 * 2 ^ (288 * ((K + 1) * L)) ≤ 2 ^ (289 * ((K + 1) * L)) := by
    have : 2 ^ (288 * ((K + 1) * L) + 1) ≤ 2 ^ (289 * ((K + 1) * L)) := QuarticSC2Sched.two_pow_le (by omega)
    rw [pow_add] at this; omega
  have hY1 : 1 ≤ 2 ^ (7 * L) := Nat.one_le_two_pow
  have hYX : 32 * 2 ^ (7 * L) ≤ 2 ^ (289 * ((K + 1) * L)) := by
    have : 2 ^ (7 * L + 5) ≤ 2 ^ (289 * ((K + 1) * L)) := QuarticSC2Sched.two_pow_le (by omega)
    rw [pow_add] at this; omega
  have hG0 := EncodedGraph.encode_length_upper g hg
  have hmul : g.edges.length * (4 * g.vertices + 4) ≤ 2 ^ (7 * L) * (4 * 2 ^ (7 * L) + 4) :=
    Nat.mul_le_mul hm (by omega)
  have hY2 : 2 ^ (7 * L) * (4 * 2 ^ (7 * L) + 4) =
      4 * (2 ^ (7 * L) * 2 ^ (7 * L)) + 4 * 2 ^ (7 * L) := by ring
  have hYYX : 32 * (2 ^ (7 * L) * 2 ^ (7 * L)) ≤ 2 ^ (289 * ((K + 1) * L)) := by
    have : 2 ^ (7 * L + 7 * L + 5) ≤ 2 ^ (289 * ((K + 1) * L)) := QuarticSC2Sched.two_pow_le (by omega)
    rw [pow_add, pow_add] at this
    omega
  omega

/-- `Hmaster` of `SuccessClock.Tent_sched`, discharged: exponent `2601`. -/
theorem Hmaster_sched (L Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) (hg : g.Valid)
    [NeZero g.vertices] [NeZero (width L)] [NeZero (width L - 2)] [NeZero (outerWidth L)]
    [NeZero (width27 L)] [NeZero (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ)]
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin g.vertices) (Edges := Fin g.edges.length) L Δ γ)
    (r : ℕ) (hq : outerWidth L = SourceItems.sourceQ0 (Fin (4 * width L)) (Fin g.edges.length) * r)
    (K : ℕ) :
    (∑ z : SrcX.JX, (RLoop.master (p := LookupSeed.width L) (s := width L)
      (q₁ := width L - 2) (q₂ := outerWidth L) (w := width27 L)
      (Q := Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) g r z).length) ≤
      2 ^ (2601 * ((K + 1) * L)) := by
  have h := master_sched_le L Δ γ g hg hc r hq K
  obtain ⟨-, -, -, -, -, -, -, -, -, hL⟩ :=
    scalar_caps27 (n := g.vertices) (m := g.edges.length) L Δ γ hc
  have h2 : 4 * 2 ^ (289 * ((K + 1) * L)) ≤ 2 ^ (2601 * ((K + 1) * L)) := by
    have : 2 ^ (289 * ((K + 1) * L) + 2) ≤ 2 ^ (2601 * ((K + 1) * L)) := QuarticSC2Sched.two_pow_le (by nlinarith)
    rw [pow_add] at this; omega
  omega

/-- `Hbank` of `SuccessClock.Tent_sched`, discharged: exponent `2601`. -/
theorem Hbank_sched (L Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) (hg : g.Valid)
    [NeZero g.vertices] [NeZero (width L)] [NeZero (width L - 2)] [NeZero (outerWidth L)]
    [NeZero (width27 L)] [NeZero (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ)]
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin g.vertices) (Edges := Fin g.edges.length) L Δ γ)
    (r : ℕ) (hq : outerWidth L = SourceItems.sourceQ0 (Fin (4 * width L)) (Fin g.edges.length) * r)
    (K : ℕ) :
    ∀ k, k + 1 ≤ K →
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
          2 ^ (2601 * ((K + 1) * L)) := by
  intro k hk x y
  obtain ⟨hX, hS, hcd, hl, hG, hmn, hW⟩ := sched_scale L Δ γ g hg hc r hq K k hk
  have hM := master_sched_le L Δ γ g hg hc r hq K
  have hE := E0k_sum_le (p := LookupSeed.width L) (s := width L) (q₁ := width L - 2)
    (q₂ := outerWidth L) (w := width27 L)
    (Q := Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) g r k
  have hJ := W0f_sum_le (n := g.vertices) k x y
  obtain ⟨-, -, -, -, -, -, -, -, -, hL⟩ :=
    scalar_caps27 (n := g.vertices) (m := g.edges.length) L Δ γ hc
  have h2 : 16 * 2 ^ (289 * ((K + 1) * L)) ≤ 2 ^ (2601 * ((K + 1) * L)) := by
    have : 2 ^ (289 * ((K + 1) * L) + 4) ≤ 2 ^ (2601 * ((K + 1) * L)) := QuarticSC2Sched.two_pow_le (by nlinarith)
    rw [pow_add] at this; omega
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  omega


end Paper2.CurrentAdditive.QuarticSC2Bank

#print axioms Paper2.CurrentAdditive.QuarticSC2Bank.master_sched_le
#print axioms Paper2.CurrentAdditive.QuarticSC2Bank.Hmaster_sched
#print axioms Paper2.CurrentAdditive.QuarticSC2Bank.Hbank_sched
