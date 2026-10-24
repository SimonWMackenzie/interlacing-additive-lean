import Paper2.SC2Arms

/-! Lane a-success-clock-owner-2, segment (1), generic form: the literal
production one-level clock `RLoop.stepClock` (both raw-row cases, every tag)
is at most `X^9` for every level-`k+1` pair, for any scale `X ≥ 2^20` that
dominates the public scalars, the level-`k+1` code sizes and label lengths,
the literal graph bytes and the default words of the levels `≤ k`. -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

namespace Paper2.SuccessClock2

open EthInapproximability.CurrentPaper
open Paper2.GeneratorCode Paper2.GeneratorSerialization Paper2.GeneratorSource
  Paper2.RecursiveLabelCodecScratch Paper2.RecursiveEntries

variable {p s q₁ q₂ w Q : ℕ} [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q] [NeZero s]

/-- The prefix selection clock of one level. -/
theorem selClock_X {n : ℕ} [NeZero n] (k : ℕ)
    (x : Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q (k + 1))
    (y : Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q (k + 1))
    {X : ℕ} (hX : 1048576 ≤ X) (hS : Q + w ≤ X)
    (hc : codeSize (seedRecursiveCodes n p s q₁ q₂ w Q (k + 1)).1 +
      codeSize (seedRecursiveCodes n p s q₁ q₂ w Q (k + 1)).2 ≤ X)
    (hl : (defaultCarrierCodecs n p s q₁ q₂ w Q (k + 1)).1.maxLen +
      (defaultCarrierCodecs n p s q₁ q₂ w Q (k + 1)).2.maxLen ≤ X) :
    TemplateStepX.selClock k x y ≤ X ^ 5 := by
  obtain ⟨⟨d1, d3, d4, d5, d6, d7⟩, ⟨m1, m2, m3, m4, m5, m7, m8, m9, m10⟩⟩ :=
    level_facts n p s q₁ q₂ w Q k (NeZero.pos s) (NeZero.pos q₂) (NeZero.pos w) (NeZero.pos Q)
  have hY := (defaultCarrierCodecs n p s q₁ q₂ w Q (k + 1)).2.length_le y
  have hj := y.1.isLt
  have hi := (x y.1).1.isLt
  obtain ⟨f1, f2⟩ := ofFn_X (X := X)
    (prodCodec (finCodec w) (taggedColumnCodec q₁ q₂ s (defaultCarrierCodecs n p s q₁ q₂ w Q k).2))
    Q x (by omega) (by omega)
  obtain ⟨g1, g2⟩ := ofFn_X (X := X)
    (rawRowCodec q₁ q₂ s (defaultCarrierCodecs n p s q₁ q₂ w Q k).1 (defaultItemCodec n s))
    w y.2 (by omega) (by omega)
  unfold TemplateStepX.selClock
  exact reqClock_X _ _ _ _ _ _ _ hX (by omega) (by omega) (by omega) (by omega) (by omega)
    f1 f2 g1 g2

/-- Segment (1), generic: the one-level clock, every pair of the level. -/
theorem stepClock_X (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices] (hs : 4 ≤ s)
    (r : ℕ) (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin g.edges.length) * r)
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q)
    (k : ℕ)
    (x : Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q (k + 1))
    (y : Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q (k + 1)) {X : ℕ}
    (hX : 1048576 ≤ X)
    (hS : g.vertices + p + 4 * s + q₁ + q₂ + w + Q + g.edges.length + r + k + 16 ≤ X)
    (hc : codeSize (seedRecursiveCodes g.vertices p s q₁ q₂ w Q (k + 1)).1 +
      codeSize (seedRecursiveCodes g.vertices p s q₁ q₂ w Q (k + 1)).2 + q₁ + 8 ≤ X)
    (hl : (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q (k + 1)).1.maxLen +
      (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q (k + 1)).2.maxLen ≤ X)
    (hG : (EncodedGraph.encode g).length + 1 ≤ X)
    (hmn : 2 * g.edges.length * g.vertices ≤ X)
    (hW : ∀ i ≤ k, (CanonicalDefaultWordScratch.words p s q₁ q₂ w Q i).1.length ≤ X ∧
      (CanonicalDefaultWordScratch.words p s q₁ q₂ w Q i).2.length ≤ X) :
    RLoop.stepClock g hg hs r hq ξ k x y ≤ X ^ 9 := by
  obtain ⟨h2, h3, h4, h5, h6, h7, h8⟩ := xchain hX
  have h9 : 1048576 * X ^ 8 ≤ X ^ 9 := xstep hX 8
  obtain ⟨⟨d1, d3, d4, d5, d6, d7⟩, ⟨m1, m2, m3, m4, m5, m7, m8, m9, m10⟩⟩ :=
    level_facts g.vertices p s q₁ q₂ w Q k (NeZero.pos s) (NeZero.pos q₂) (NeZero.pos w)
      (NeZero.pos Q)
  have hJ := joinBound_le g.vertices p s q₁ q₂ w Q k (NeZero.pos Q) (NeZero.pos w)
    (NeZero.pos s) (NeZero.pos q₂)
  have hsel := selClock_X (n := g.vertices) k x y hX (by omega) (by omega) hl
  unfold RLoop.stepClock
  extract_lets C c activity
  have e1 : (outerColumnCodec q₁ q₂ s C.2).maxLen ≤ X := by
    have : (outerColumnCodec q₁ q₂ s C.2).maxLen ≤
        (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q (k + 1)).1.maxLen := m1
    omega
  have e3 : (piCodec C.2 (s + 1)).maxLen ≤ X := by
    have : (piCodec C.2 (s + 1)).maxLen ≤
        (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q (k + 1)).1.maxLen := m3
    omega
  have e7 : C.2.maxLen ≤ X := by
    have : C.2.maxLen ≤ (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q (k + 1)).1.maxLen := m7
    omega
  have e9 : (prodCodec (finCodec q₁) C.1).maxLen ≤ X := by
    have : (prodCodec (finCodec q₁) C.1).maxLen ≤
        (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q (k + 1)).2.maxLen := m9
    omega
  have e10 : C.1.maxLen ≤ X := by
    have : C.1.maxLen ≤ (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q (k + 1)).2.maxLen := m10
    omega
  have k3 : codeSize (outerCode q₁ q₂ s c.2) ≤ X := by
    have : codeSize (outerCode q₁ q₂ s c.2) ≤
        codeSize (seedRecursiveCodes g.vertices p s q₁ q₂ w Q (k + 1)).1 := d3
    omega
  have k4 : codeSize (copies (s + 1) c.2) ≤ X := by
    have : codeSize (copies (s + 1) c.2) ≤
        codeSize (seedRecursiveCodes g.vertices p s q₁ q₂ w Q (k + 1)).1 := d4
    omega
  have k5 : codeSize c.2 ≤ X := by
    have : codeSize c.2 ≤ codeSize (seedRecursiveCodes g.vertices p s q₁ q₂ w Q (k + 1)).1 := d5
    omega
  have k7 : codeSize (.append (.ticket q₁) c.1) ≤ X := by
    have : codeSize c.1 ≤ codeSize (seedRecursiveCodes g.vertices p s q₁ q₂ w Q (k + 1)).2 := d7
    have e : codeSize (.append (.ticket q₁) c.1) = 3 + (3 + (q₁ + 1)) + codeSize c.1 := rfl
    omega
  rcases hr : y.2 (x y.1).1 with pz | iu
  · simp only [Sum.elim_inl]
    have hp1 := pz.1.isLt
    have hloc := locBound_X q₁ q₂ s C.2 c.2 pz.1.val (x y.1).2 hX (by omega) (by omega) k3 k4
      e1 e3
    generalize (SourceMatrix.forgetTag (ξ k) (x y.1).2).2 pz.1 = oc
    have hY := (outerColumnCodec q₁ q₂ s C.2).length_le oc
    have hj := oc.1.isLt
    have hi := (pz.2 oc.1).1.isLt
    obtain ⟨f1, f2⟩ := ofFn_X (X := X) (prodCodec (finCodec q₁) C.1) q₂ pz.2 (by omega) e9
    obtain ⟨g1, g2⟩ := ofFn_X (X := X) C.2 (q₁ + s + 1) oc.2 (by omega) e7
    have hreq := reqClock_X ((outerColumnCodec q₁ q₂ s C.2).encode oc) oc.1.val
      (pz.2 oc.1).1.val (.append (.ticket q₁) c.1) c.2 _ _ hX (by omega) (by omega) (by omega)
      k7 k5 f1 f2 g1 g2
    omega
  · simp only [Sum.elim_inr]
    have hsrc := srcX_X g hg hs r hq k iu.1 (ξ k) (x y.1).2 hX hS hc hl hG hmn hW
    have hw1 := C.2.length_le (SourceMatrix.sourceColumn activity iu.1
      (SourceMatrix.forgetTag (ξ k) (x y.1).2))
    have hw2 := C.1.length_le iu.2
    omega

end Paper2.SuccessClock2

#print axioms Paper2.SuccessClock2.selClock_X
#print axioms Paper2.SuccessClock2.stepClock_X
