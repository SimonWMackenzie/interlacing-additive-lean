import CurrentAdditive.V39RequestStepK
import Paper2.SC2Step

/-! Polynomial majorant for the actual current request-step clock, derived
from the physical edge-only scanner and the admitted parser arithmetic.
Source: v39 main.tex, lem:sample-access and its implementation proof.
No source-execution, callback, fixed-tail or clock-cap premise is supplied. -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

namespace CurrentAdditive.V39StepClock
noncomputable section
open Paper2
open EthInapproximability.CurrentPaper
open Paper2.GeneratorCode Paper2.GeneratorSerialization Paper2.GeneratorSource
  Paper2.RecursiveLabelCodecScratch Paper2.RecursiveEntries
open Paper2.SuccessClock2
open V39EdgeSourceFront (edgeActivity)

/-- The scan-and-position clock of the source arms. -/
theorem scanPosBound_X (g : EncodedGraph.Graph) (hg : g.Valid) (a r ig xv : ℕ) (kb : Bool)
    {X : ℕ} (hX : 1048576 ≤ X) (ha : a ≤ X) (hr : r ≤ X) (hig : ig ≤ X) (hxv : xv ≤ X)
    (hn : g.vertices ≤ X) (hm : g.edges.length ≤ X)
    (hG : (EncodedGraph.encode g).length + 1 ≤ X) (hmn : 2 * g.edges.length * g.vertices ≤ X) :
    V39EdgeSourceFront.scanPosBound g hg a r ig xv kb ≤ X ^ 4 := by
  obtain ⟨h2, h3, h4, h5, -⟩ := xchain hX
  have hd := LiteralEdgeDecodeMachine.clock_le a r g.edges.length
  have d1 : a / r ≤ a := Nat.div_le_self _ _
  have d3 : a / r / g.edges.length ≤ a / r := Nat.div_le_self _ _
  unfold V39EdgeSourceFront.scanPosBound
  by_cases hsp : 0 < g.edges.length ∧ a / r / g.edges.length = ig
  · rw [dif_pos hsp]
    dsimp only
    generalize CanonicalEdgeTape.graphEdge g hg = edge
    have hmod := Nat.mod_lt (a / r) hsp.1
    have hw := CanonicalEdgeTape.word_length_le edge
    have hu := (edge ⟨a / r % g.edges.length, hmod⟩ true).isLt
    have hv := (edge ⟨a / r % g.edges.length, hmod⟩ false).isLt
    have hsr := semanticRank_le (RankRun.kindOfNat 0) (RankRun.itemOfBool kb)
      (edge ⟨a / r % g.edges.length, hmod⟩ false).val
      (edge ⟨a / r % g.edges.length, hmod⟩ true).val xv
    have hc : ((EncodedGraph.encode g).length + 1) ^ 3 ≤ X ^ 3 := Nat.pow_le_pow_left hG 3
    have mx : max (edge ⟨a / r % g.edges.length, hmod⟩ false).val
        (max (edge ⟨a / r % g.edges.length, hmod⟩ true).val xv) ≤ X := by
      simp only [max_le_iff]; omega
    have hmod' : a / r % g.edges.length ≤ a / r := Nat.mod_le _ _
    simp only [UnaryFieldListParserScratch.fuel]
    omega
  · rw [dif_neg hsp]
    omega

variable {p s q₁ q₂ w Q : ℕ} [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q] [NeZero s]

/-- The unrestricted-tag source arm. -/
theorem srcU_X (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices] (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂ = LiteralEdgeEncoder.Width s g.edges.length r) (k : ℕ)
    (i : SourceConstruction.Items s (Fin g.vertices))
    (Z : SourceMatrix.RawColumn q₁ q₂ s (Column (Fin p → Bool) (Fin p)
      (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q k)) {X : ℕ}
    (hX : 1048576 ≤ X)
    (hS : g.vertices + p + 4 * s + q₁ + q₂ + w + Q + g.edges.length + r + k + 16 ≤ X)
    (hc : codeSize (seedRecursiveCodes g.vertices p s q₁ q₂ w Q (k + 1)).1 +
      codeSize (seedRecursiveCodes g.vertices p s q₁ q₂ w Q (k + 1)).2 + q₁ + 8 ≤ X)
    (hl : (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q (k + 1)).1.maxLen +
      (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q (k + 1)).2.maxLen ≤ X)
    (hG : (EncodedGraph.encode g).length + 1 ≤ X)
    (hmn : 2 * g.edges.length * g.vertices ≤ X) :
    V39EdgeSourceTail.srcUBound g hg hs r hq k i Z [] ≤ 2 * X ^ 7 := by
  obtain ⟨h2, h3, h4, h5, h6, h7, h8⟩ := xchain hX
  obtain ⟨⟨d1, d3, d4, d5, d6, d7⟩, ⟨m1, m2, m3, m4, m5, m7, m8, m9, m10⟩⟩ :=
    level_facts g.vertices p s q₁ q₂ w Q k (by omega) (NeZero.pos q₂) (NeZero.pos w)
      (NeZero.pos Q)
  unfold V39EdgeSourceTail.srcUBound
  extract_lets C col xv activity
  simp only [C, col, xv]
  have hxv : (CanonicalEndpointRankBridge.itemValue i.2) ≤ X := by
    have := itemValue_le i.2; omega
  have hi1 := i.1.isLt
  have hTf : ∀ j < s, OTTags.TfU k Z [] j ≤ X ^ 4 := by
    intro j hj
    unfold OTTags.TfU
    obtain ⟨f1, f2⟩ := ofFn_X (X := X) (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k).2 (s + 1) Z.1 (by omega) (by omega)
    obtain ⟨g1, g2⟩ := ofFn_X (X := X) (outerColumnCodec q₁ q₂ s (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k).2) s Z.2 (by omega) (by omega)
    exact rowBound_X _ _ _ _ j [] hX (by omega) (by omega) f1 g1 f2 g2 (by omega) (by simp)
  have htok : ∀ j, OTLoop.tokF k Z.2 j ≤ X := by
    intro j
    unfold OTLoop.tokF
    split
    · have := (Z.2 ⟨j, by assumption⟩).1.isLt; omega
    · omega
  have hrest : ∀ j, (OTTags.restF k Z.2 j).length ≤ X := by
    intro j
    unfold OTTags.restF
    split
    · have := (piCodec (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k).2 (q₁ + s + 1)).length_le
        (Z.2 ⟨j, by assumption⟩).2
      omega
    · simp
  have hF := fullGBound_X s (OTTags.TfU k Z []) (OTLoop.tokF k Z.2) (OTTags.restF k Z.2) hX
    (NeZero.pos s) (by omega) hTf htok hrest
  have ha := (Z.2 0).1.isLt
  have hsp := scanPosBound_X g hg (Z.2 0).1.val r i.1.val (CanonicalEndpointRankBridge.itemValue i.2) i.2.isRight hX (by omega) (by omega)
    (by omega) hxv (by omega) (by omega) hG hmn
  have hpos := (SourceMatrix.sourcePosition activity i Z).isLt
  have hO := (piCodec (outerColumnCodec q₁ q₂ s (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k).2) s).length_le Z.2
  obtain ⟨f1, f2⟩ := ofFn_X (X := X) (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k).2 (s + 1) Z.1 (by omega) (by omega)
  have hcol := colBound_X (seedRecursiveCodes g.vertices p s q₁ q₂ w Q k).2 (List.ofFn (fun a : Fin (s + 1) => (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k).2.encode (Z.1 a)))
    (SourceMatrix.sourcePosition activity i Z).val
    ((piCodec (outerColumnCodec q₁ q₂ s (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k).2) s).encode Z.2 ++ []) hX (by omega)
    f1 f2 (by omega) (by simp; omega)
  omega

/-- The diagonal-tag source arm. -/
theorem srcD_X (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices] (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂ = LiteralEdgeEncoder.Width s g.edges.length r) (k : ℕ)
    (i : SourceConstruction.Items s (Fin g.vertices))
    (ξ₀ : SourceMatrix.Tail s (Column (Fin p → Bool) (Fin p)
      (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q k))
    (j : SourceMatrix.OuterColumn q₁ q₂ s (Column (Fin p → Bool) (Fin p)
      (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q k)) {X : ℕ}
    (hX : 1048576 ≤ X)
    (hS : g.vertices + p + 4 * s + q₁ + q₂ + w + Q + g.edges.length + r + k + 16 ≤ X)
    (hc : codeSize (seedRecursiveCodes g.vertices p s q₁ q₂ w Q (k + 1)).1 +
      codeSize (seedRecursiveCodes g.vertices p s q₁ q₂ w Q (k + 1)).2 + q₁ + 8 ≤ X)
    (hl : (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q (k + 1)).1.maxLen +
      (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q (k + 1)).2.maxLen ≤ X)
    (hG : (EncodedGraph.encode g).length + 1 ≤ X)
    (hmn : 2 * g.edges.length * g.vertices ≤ X) :
    V39EdgeSourceDiagonal.srcDBound g hg hs r hq k i ξ₀ j [] ≤ X ^ 5 := by
  obtain ⟨h2, h3, h4, h5, h6, h7, h8⟩ := xchain hX
  obtain ⟨⟨d1, d3, d4, d5, d6, d7⟩, ⟨m1, m2, m3, m4, m5, m7, m8, m9, m10⟩⟩ :=
    level_facts g.vertices p s q₁ q₂ w Q k (by omega) (NeZero.pos q₂) (NeZero.pos w)
      (NeZero.pos Q)
  unfold V39EdgeSourceDiagonal.srcDBound
  extract_lets C col xv activity
  simp only [C, col, xv]
  have hxv : (CanonicalEndpointRankBridge.itemValue i.2) ≤ X := by
    have := itemValue_le i.2; omega
  have hi1 := i.1.isLt
  have ha := j.1.isLt
  have hsp := scanPosBound_X g hg j.1.val r i.1.val (CanonicalEndpointRankBridge.itemValue i.2) i.2.isRight hX (by omega) (by omega)
    (by omega) hxv (by omega) (by omega) hG hmn
  have hpos := (SourceMatrix.sourcePosition activity i
    (SourceMatrix.forgetTag ξ₀ (.diagonal j))).isLt
  obtain ⟨f1, f2⟩ := ofFn_X (X := X) (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k).2 (q₁ + s + 1) j.2 (by omega) (by omega)
  have hcol := colBound_X (seedRecursiveCodes g.vertices p s q₁ q₂ w Q k).2 (List.ofFn (fun a : Fin (q₁ + s + 1) => (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k).2.encode (j.2 a)))
    (q₁ + (SourceMatrix.sourcePosition activity i
      (SourceMatrix.forgetTag ξ₀ (.diagonal j))).val) [] hX (by omega)
    f1 f2 (by omega) (by simp)
  omega

/-- Both actual current tag families have a uniform source-dispatch clock. -/
theorem dispatchClock_X (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
    (hs : 4 ≤ s) (r : ℕ) (hq : q₂ = LiteralEdgeEncoder.Width s g.edges.length r)
    (k : ℕ) (i : EdgeSourceMatrix.Items s (Fin g.vertices))
    (z : V38Matrix.TaggedColumn q₁ q₂ s
      (V39RecursiveGenerator.Column g.vertices p q₁ q₂ s w Q k)) {X : ℕ}
    (hX : 1048576 ≤ X)
    (hS : g.vertices + p + 4 * s + q₁ + q₂ + w + Q + g.edges.length + r + k + 16 ≤ X)
    (hc : codeSize (seedRecursiveCodes g.vertices p s q₁ q₂ w Q (k + 1)).1 +
      codeSize (seedRecursiveCodes g.vertices p s q₁ q₂ w Q (k + 1)).2 + q₁ + 8 ≤ X)
    (hl : (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q (k + 1)).1.maxLen +
      (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q (k + 1)).2.maxLen ≤ X)
    (hG : (EncodedGraph.encode g).length + 1 ≤ X)
    (hmn : 2 * g.edges.length * g.vertices ≤ X) :
    V39EdgeSourceDispatch.clock g hg hs r hq k i [] z ≤ X ^ 8 := by
  obtain ⟨h2,h3,h4,h5,h6,h7,h8⟩ := xchain hX
  cases z with
  | inl Z =>
      have h := srcU_X g hg hs r hq k i
        (V39PhysicalSelect.rawColumnMap
          (V39PhysicalSelect.embedding g.vertices p q₁ q₂ s w Q k).2 Z) hX hS hc hl hG hmn
      simp only [V39EdgeSourceDispatch.clock]
      omega
  | inr j =>
      let j' := V39PhysicalSelect.outerMap
        (V39PhysicalSelect.embedding g.vertices p q₁ q₂ s w Q k).2 j
      have h := srcD_X g hg hs r hq k i (SourceMatrix.tail j'.2) j' hX hS hc hl hG hmn
      dsimp only [j'] at h
      simp only [V39EdgeSourceDispatch.clock]
      omega

end
end CurrentAdditive.V39StepClock
#print axioms CurrentAdditive.V39StepClock.scanPosBound_X
#print axioms CurrentAdditive.V39StepClock.srcU_X
#print axioms CurrentAdditive.V39StepClock.srcD_X
#print axioms CurrentAdditive.V39StepClock.dispatchClock_X
