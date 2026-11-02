import CurrentAdditive.QuarticLabelCap
import Paper2.SC2Sched

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

namespace Paper2.CurrentAdditive.QuarticSC2Sched

open EthInapproximability.CurrentPaper
open Paper2.GeneratorCode Paper2.GeneratorSerialization Paper2.GeneratorSource
  Paper2.RecursiveLabelCodecScratch Paper2.RecursiveEntries Paper2.ParameterizedCanonicalSource
  Paper2.SourceProfileParameters Paper2.SuccessClock2
open CurrentAdditive.RandomizedSchedule Paper2.CurrentAdditive.QuarticClockCaps

theorem two_pow_le {a b : ℕ} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) h

/-- The scale hypotheses of `stepClock_X` at the public schedule, `X = 2^(289(K+1)L)`, every
level `k + 1 ≤ K`. -/
theorem sched_scale (L Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) (hg : g.Valid)
    [NeZero g.vertices] [NeZero (width L)] [NeZero (width L - 2)] [NeZero (outerWidth L)]
    [NeZero (width27 L)] [NeZero (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ)]
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin g.vertices) (Edges := Fin g.edges.length) L Δ γ)
    (r : ℕ) (hq : outerWidth L = SourceItems.sourceQ0 (Fin (4 * width L)) (Fin g.edges.length) * r)
    (K k : ℕ) (hk : k + 1 ≤ K) :
    let X := 2 ^ (289 * ((K + 1) * L))
    let n := g.vertices
    let p := LookupSeed.width L
    let s := width L
    let q₁ := width L - 2
    let q₂ := outerWidth L
    let w := width27 L
    let Q := Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ
    1048576 ≤ X ∧
    n + p + 4 * s + q₁ + q₂ + w + Q + g.edges.length + r + k + 16 ≤ X ∧
    codeSize (seedRecursiveCodes n p s q₁ q₂ w Q (k + 1)).1 +
      codeSize (seedRecursiveCodes n p s q₁ q₂ w Q (k + 1)).2 + q₁ + 8 ≤ X ∧
    (defaultCarrierCodecs n p s q₁ q₂ w Q (k + 1)).1.maxLen +
      (defaultCarrierCodecs n p s q₁ q₂ w Q (k + 1)).2.maxLen ≤ X ∧
    (EncodedGraph.encode g).length + 1 ≤ X ∧
    2 * g.edges.length * g.vertices ≤ X ∧
    (∀ i ≤ k, (CanonicalDefaultWordScratch.words p s q₁ q₂ w Q i).1.length ≤ X ∧
      (CanonicalDefaultWordScratch.words p s q₁ q₂ w Q i).2.length ≤ X) := by
  intro X n p s q₁ q₂ w Q
  have hsc := scalar_caps27 (n := g.vertices) (m := g.edges.length) L Δ γ hc
  dsimp [Paper2.GeneratorPublicCap.publicCap] at hsc
  obtain ⟨_, hn, hp, hs, hq₁, hq₂, hw, hQ, hm, hL⟩ := hsc
  have hLT : L ≤ (K + 1) * L := by nlinarith
  have hKT : K + 1 ≤ (K + 1) * L := by nlinarith
  have hr : r ≤ q₂ := Paper2.SuccessClock.rep_le_outer (NeZero.pos (outerWidth L)) hq
  have hY1 : 1 ≤ 2 ^ (7 * L) := Nat.one_le_two_pow
  have hYX : 32 * 2 ^ (7 * L) ≤ X := by
    have : 2 ^ (7 * L + 5) ≤ X := two_pow_le (by omega)
    rw [pow_add] at this; omega
  have hTX : 32 * ((K + 1) * L + 16) ≤ X := by
    have h1 : (K + 1) * L + 16 ≤ 2 ^ ((K + 1) * L + 5) := by
      have := Nat.lt_two_pow_self (n := (K + 1) * L)
      rw [pow_add]; omega
    have h2 : 2 ^ ((K + 1) * L + 5 + 5) ≤ X := two_pow_le (by omega)
    rw [pow_add] at h2; omega
  have hX20 : 1048576 ≤ X := by
    have : 2 ^ 20 ≤ X := two_pow_le (by omega)
    simpa using this
  -- codes
  have hcode : codeSize (seedRecursiveCodes n p s q₁ q₂ w Q (k + 1)).1 +
      codeSize (seedRecursiveCodes n p s q₁ q₂ w Q (k + 1)).2 + 1 ≤ 2 ^ (288 * ((K + 1) * L)) :=
    code_cap27 (n := g.vertices) (m := g.edges.length) L Δ γ hc K
      (k + 1) (by omega)
  have hZ : 2 * 2 ^ (288 * ((K + 1) * L)) ≤ X := by
    have : 2 ^ (288 * ((K + 1) * L) + 1) ≤ X := two_pow_le (by omega)
    rw [pow_add] at this; omega
  have hYZ : 2 ^ (7 * L) + 8 ≤ 2 ^ (288 * ((K + 1) * L)) := by
    have : 2 ^ (7 * L + 4) ≤ 2 ^ (288 * ((K + 1) * L)) := two_pow_le (by omega)
    rw [pow_add] at this; omega
  -- labels
  have hlab : (defaultCarrierCodecs n p s q₁ q₂ w Q (k + 1)).1.maxLen ≤ 2 ^ (26 * ((K + 1) * L)) ∧
      (defaultCarrierCodecs n p s q₁ q₂ w Q (k + 1)).2.maxLen ≤ 2 ^ (26 * ((K + 1) * L)) :=
    label_cap27 (n := g.vertices) (m := g.edges.length) L Δ γ hc K (k + 1) hk
  have hV : 2 * 2 ^ (26 * ((K + 1) * L)) ≤ X := by
    have : 2 ^ (26 * ((K + 1) * L) + 1) ≤ X := two_pow_le (by omega)
    rw [pow_add] at this; omega
  -- graph bytes
  have hG0 := EncodedGraph.encode_length_upper g hg
  have hmul : g.edges.length * (4 * g.vertices + 4) ≤ 2 ^ (7 * L) * (4 * 2 ^ (7 * L) + 4) :=
    Nat.mul_le_mul hm (by omega)
  have hY2 : 2 ^ (7 * L) * (4 * 2 ^ (7 * L) + 4) =
      4 * (2 ^ (7 * L) * 2 ^ (7 * L)) + 4 * 2 ^ (7 * L) := by ring
  have hYY : 2 ^ (7 * L) ≤ 2 ^ (7 * L) * 2 ^ (7 * L) := Nat.le_mul_of_pos_left _ (by omega)
  have hYYX : 32 * (2 ^ (7 * L) * 2 ^ (7 * L)) ≤ X := by
    have : 2 ^ (7 * L + 7 * L + 5) ≤ X := two_pow_le (by omega)
    rw [pow_add, pow_add] at this
    omega
  have hmn : 2 * g.edges.length * g.vertices ≤ 2 * 2 ^ (7 * L) * 2 ^ (7 * L) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 2 hm) hn
  have hmn' : 2 * 2 ^ (7 * L) * 2 ^ (7 * L) = 2 * (2 ^ (7 * L) * 2 ^ (7 * L)) := by ring
  -- default words
  have hW : ∀ i ≤ k, (CanonicalDefaultWordScratch.words p s q₁ q₂ w Q i).1.length ≤ X ∧
      (CanonicalDefaultWordScratch.words p s q₁ q₂ w Q i).2.length ≤ X := by
    intro i hi
    have hp0 : 0 < p := by
      show 0 < LookupSeed.width L
      unfold LookupSeed.width; exact Nat.two_pow_pos _
    have hs4 : 0 < 4 * s := by have := NeZero.pos (width L); omega
    have he := CanonicalDefaultWordScratch.defaultLabels_encoded n p s q₁ q₂ w Q
      (NeZero.pos g.vertices) hp0 hs4
      (NeZero.pos (outerWidth L)) (NeZero.pos (width27 L))
      (NeZero.pos (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ)) i
    dsimp only at he
    rw [← he]
    dsimp only
    have hli : (defaultCarrierCodecs n p s q₁ q₂ w Q i).1.maxLen ≤ 2 ^ (26 * ((K + 1) * L)) ∧
        (defaultCarrierCodecs n p s q₁ q₂ w Q i).2.maxLen ≤ 2 ^ (26 * ((K + 1) * L)) :=
      label_cap27 (n := g.vertices) (m := g.edges.length) L Δ γ hc K i
        (by omega)
    have l1 := (defaultCarrierCodecs n p s q₁ q₂ w Q i).1.length_le
      (RecursiveEntries.defaultLabels (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
        (fun _ : Fin p => false) (⟨0, hp0⟩ : Fin p)
        ((⟨0, hs4⟩, .inl ⟨0, NeZero.pos g.vertices⟩) : SourceConstruction.Items s (Fin n))
        (NeZero.pos (outerWidth L)) (NeZero.pos (width27 L))
        (NeZero.pos (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ)) i).1
    have l2 := (defaultCarrierCodecs n p s q₁ q₂ w Q i).2.length_le
      (RecursiveEntries.defaultLabels (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
        (fun _ : Fin p => false) (⟨0, hp0⟩ : Fin p)
        ((⟨0, hs4⟩, .inl ⟨0, NeZero.pos g.vertices⟩) : SourceConstruction.Items s (Fin n))
        (NeZero.pos (outerWidth L)) (NeZero.pos (width27 L))
        (NeZero.pos (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ)) i).2
    exact ⟨by omega, by omega⟩
  exact ⟨hX20, by omega, by omega, by omega, by omega, by omega, hW⟩

/-- `Hstep` of `SuccessClock.Tent_sched`, discharged: exponent `2601`. -/
theorem Hstep_sched (L Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) (hg : g.Valid)
    [NeZero g.vertices] [NeZero (width L)] [NeZero (width L - 2)] [NeZero (outerWidth L)]
    [NeZero (width27 L)] [NeZero (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ)]
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin g.vertices) (Edges := Fin g.edges.length) L Δ γ)
    (r : ℕ) (hq : outerWidth L = SourceItems.sourceQ0 (Fin (4 * width L)) (Fin g.edges.length) * r)
    (ξ : Tails (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
      (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
      (outerWidth L) (width27 L) (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ))
    (K : ℕ) :
    ∀ k, k + 1 ≤ K →
      ∀ (x : Row (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
          (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
          (outerWidth L) (width27 L) (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) (k + 1))
        (y : Column (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
          (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
          (outerWidth L) (width27 L) (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) (k + 1)),
        RLoop.stepClock g hg (SourceProfiles.width_ge_four L) r hq ξ k x y ≤
          2 ^ (2601 * ((K + 1) * L)) := by
  intro k hk x y
  obtain ⟨hX, hS, hcd, hl, hG, hmn, hW⟩ := sched_scale L Δ γ g hg hc r hq K k hk
  have h := stepClock_X g hg (SourceProfiles.width_ge_four L) r hq ξ k x y hX hS hcd hl hG hmn hW
  have e : (2 ^ (289 * ((K + 1) * L))) ^ 9 = 2 ^ (2601 * ((K + 1) * L)) := by
    rw [← pow_mul]; ring_nf
  rw [e] at h
  exact h

/-- `Hjoin` of `SuccessClock.Tent_sched`, discharged: exponent `2601`. -/
theorem Hjoin_sched (L Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) (hg : g.Valid)
    [NeZero g.vertices] [NeZero (width L)] [NeZero (width L - 2)] [NeZero (outerWidth L)]
    [NeZero (width27 L)] [NeZero (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ)]
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin g.vertices) (Edges := Fin g.edges.length) L Δ γ)
    (r : ℕ) (hq : outerWidth L = SourceItems.sourceQ0 (Fin (4 * width L)) (Fin g.edges.length) * r)
    (K : ℕ) :
    ∀ k, k + 1 ≤ K →
      NavJoin.joinBound g.vertices (LookupSeed.width L) (width L) (width L - 2) (outerWidth L)
        (width27 L) (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) k ≤
        2 ^ (2601 * ((K + 1) * L)) := by
  intro k hk
  obtain ⟨hX, hS, hcd, hl, hG, hmn, hW⟩ := sched_scale L Δ γ g hg hc r hq K k hk
  have hJ := joinBound_le g.vertices (LookupSeed.width L) (width L) (width L - 2) (outerWidth L)
    (width27 L) (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) k
    (NeZero.pos (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ)) (NeZero.pos (width27 L))
    (NeZero.pos (width L)) (NeZero.pos (outerWidth L))
  have hx : 2 ^ (289 * ((K + 1) * L)) ≤ 2 ^ (2601 * ((K + 1) * L)) := two_pow_le (by nlinarith)
  have h2 := x1 hX
  have hsq : (2 ^ (289 * ((K + 1) * L))) ^ 2 ≤ 2 ^ (2601 * ((K + 1) * L)) := by
    rw [← pow_mul]; exact two_pow_le (by nlinarith)
  omega


end Paper2.CurrentAdditive.QuarticSC2Sched

#print axioms Paper2.CurrentAdditive.QuarticSC2Sched.sched_scale
#print axioms Paper2.CurrentAdditive.QuarticSC2Sched.Hstep_sched
#print axioms Paper2.CurrentAdditive.QuarticSC2Sched.Hjoin_sched
