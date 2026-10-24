import CurrentAdditive.V39EdgeStepClock

/-! A uniform degree-nine clock for the actual current one-level request
program, for every pair of current labels. The public scale bounds only
scalars, parser-code sizes, label lengths and literal graph size. -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

namespace CurrentAdditive.V39StepClock
noncomputable section

open Paper2
open EthInapproximability.CurrentPaper
open Paper2.GeneratorCode Paper2.GeneratorSerialization Paper2.GeneratorSource
  Paper2.RecursiveLabelCodecScratch Paper2.RecursiveEntries
open Paper2.SuccessClock2

variable {p s q₁ q₂ w Q : ℕ} [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q] [NeZero s]

/-- The literal current request-step clock is polynomial in the public scale. -/
theorem stepClock_X (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices] (hs : 4 ≤ s)
    (r : ℕ) (hq : q₂ = LiteralEdgeEncoder.Width s g.edges.length r)
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q)
    (k : ℕ)
    (x0 : V39RecursiveGenerator.Row g.vertices p q₁ q₂ s w Q (k+1))
    (y0 : V39RecursiveGenerator.Column g.vertices p q₁ q₂ s w Q (k+1)) {X : ℕ}
    (hX : 1048576 ≤ X)
    (hS : g.vertices + p + 4 * s + q₁ + q₂ + w + Q + g.edges.length + r + k + 16 ≤ X)
    (hc : codeSize (seedRecursiveCodes g.vertices p s q₁ q₂ w Q (k + 1)).1 +
      codeSize (seedRecursiveCodes g.vertices p s q₁ q₂ w Q (k + 1)).2 + q₁ + 8 ≤ X)
    (hl : (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q (k + 1)).1.maxLen +
      (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q (k + 1)).2.maxLen ≤ X)
    (hG : (EncodedGraph.encode g).length + 1 ≤ X)
    (hmn : 2 * g.edges.length * g.vertices ≤ X) :
    V39RequestStep.stepClock g hg hs r hq ξ k x0 y0 ≤ X ^ 9 := by
  obtain ⟨h2, h3, h4, h5, h6, h7, h8⟩ := xchain hX
  have h9 : 1048576 * X ^ 8 ≤ X ^ 9 := xstep hX 8
  obtain ⟨⟨d1, d3, d4, d5, d6, d7⟩, ⟨m1, m2, m3, m4, m5, m7, m8, m9, m10⟩⟩ :=
    level_facts g.vertices p s q₁ q₂ w Q k (NeZero.pos s) (NeZero.pos q₂) (NeZero.pos w)
      (NeZero.pos Q)
  have hJ := joinBound_le g.vertices p s q₁ q₂ w Q k (NeZero.pos Q) (NeZero.pos w)
    (NeZero.pos s) (NeZero.pos q₂)
  unfold V39RequestStep.stepClock
  extract_lets x y C c activity
  have hsel := selClock_X (n := g.vertices) k x y hX (by omega) (by omega) hl
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
  rcases hr : y0.2 (x0 y0.1).1 with pz | iu
  · simp only [Sum.elim_inl]
    let z := fun a => ((pz.2 a).1,
      (V39PhysicalSelect.embedding g.vertices p q₁ q₂ s w Q k).1 (pz.2 a).2)
    have hp1 := pz.1.isLt
    have hloc := locBound_X q₁ q₂ s C.2 c.2 pz.1.val (x y.1).2 hX (by omega) (by omega) k3 k4
      e1 e3
    generalize (SourceMatrix.forgetTag (ξ k) (x y.1).2).2 pz.1 = oc
    have hY := (outerColumnCodec q₁ q₂ s C.2).length_le oc
    have hj := oc.1.isLt
    have hi := (z oc.1).1.isLt
    obtain ⟨f1, f2⟩ := ofFn_X (X := X) (prodCodec (finCodec q₁) C.1) q₂ z (by omega) e9
    obtain ⟨g1, g2⟩ := ofFn_X (X := X) C.2 (q₁ + s + 1) oc.2 (by omega) e7
    have hreq := reqClock_X ((outerColumnCodec q₁ q₂ s C.2).encode oc) oc.1.val
      (z oc.1).1.val (.append (.ticket q₁) c.1) c.2 _ _ hX (by omega) (by omega) (by omega)
      k7 k5 f1 f2 g1 g2
    dsimp only [z] at hreq
    omega
  · simp only [Sum.elim_inr]
    have hsrc := dispatchClock_X g hg hs r hq k iu.1 (x0 y0.1).2 hX hS hc hl hG hmn
    have hw1 := C.2.length_le (SourceMatrix.sourceColumn activity iu.1
      (SourceMatrix.forgetTag (ξ k) (x y.1).2))
    have hw2 : (V39PhysicalSelect.rowWord k iu.2).length ≤ C.1.maxLen :=
      C.1.length_le ((V39PhysicalSelect.embedding g.vertices p q₁ q₂ s w Q k).1 iu.2)
    omega

end
#print axioms stepClock_X
end CurrentAdditive.V39StepClock
