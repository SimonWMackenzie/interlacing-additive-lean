import Paper2.SC2Src
import Paper2.SC2Nav

/-! Lane a-success-clock-owner-2, segment (1): the checked one-level clock
`RLoop.stepClock` (both raw-row cases, every tag, the source arms included) is
at most `X^9` for any scale `X ≥ 2^20` that dominates the public scalars, the
two level-`k+1` code sizes and label lengths, the literal graph byte length
and the default words of the levels `≤ k`. Pure arithmetic over the literal
production clock expressions; no machine is defined here. -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

namespace Paper2.SuccessClock2

open EthInapproximability.CurrentPaper
open Paper2.GeneratorCode Paper2.GeneratorSerialization Paper2.GeneratorSource
  Paper2.RecursiveLabelCodecScratch Paper2.RecursiveEntries

theorem itemValue_le {n a : ℕ} (v : Fin n ⊕ Fin a) :
    CanonicalEndpointRankBridge.itemValue v ≤ n + a := by
  cases v with
  | inl v => simp only [CanonicalEndpointRankBridge.itemValue]; omega
  | inr v => simp only [CanonicalEndpointRankBridge.itemValue]; omega

/-- The level-`k` sizes read by one step, from the level-`k+1` sizes. -/
theorem level_facts (n p s q₁ q₂ w Q k : ℕ) (hs : 1 ≤ s) (hq₂ : 1 ≤ q₂) (hw : 1 ≤ w)
    (hQ : 1 ≤ Q) :
    let c := seedRecursiveCodes n p s q₁ q₂ w Q k
    let c' := seedRecursiveCodes n p s q₁ q₂ w Q (k + 1)
    let C := defaultCarrierCodecs n p s q₁ q₂ w Q k
    let C' := defaultCarrierCodecs n p s q₁ q₂ w Q (k + 1)
    (codeSize (.append (.ticket w) (taggedCode q₁ q₂ s c.2)) ≤ codeSize c'.1 ∧
      codeSize (outerCode q₁ q₂ s c.2) ≤ codeSize c'.1 ∧
      codeSize (copies (s + 1) c.2) ≤ codeSize c'.1 ∧ codeSize c.2 ≤ codeSize c'.1 ∧
      codeSize (graphRowsCode (V := Fin n) q₁ q₂ s c.1) ≤ codeSize c'.2 ∧
      codeSize c.1 ≤ codeSize c'.2) ∧
    ((outerColumnCodec q₁ q₂ s C.2).maxLen ≤ C'.1.maxLen ∧
      (piCodec (outerColumnCodec q₁ q₂ s C.2) s).maxLen ≤ C'.1.maxLen ∧
      (piCodec C.2 (s + 1)).maxLen ≤ C'.1.maxLen ∧
      (piCodec C.2 (q₁ + s + 1)).maxLen ≤ C'.1.maxLen ∧
      (prodCodec (finCodec w) (taggedColumnCodec q₁ q₂ s C.2)).maxLen ≤ C'.1.maxLen ∧
      C.2.maxLen ≤ C'.1.maxLen ∧
      (rawRowCodec q₁ q₂ s C.1 (defaultItemCodec n s)).maxLen ≤ C'.2.maxLen ∧
      (prodCodec (finCodec q₁) C.1).maxLen ≤ C'.2.maxLen ∧ C.1.maxLen ≤ C'.2.maxLen) := by
  intro c c' C C'
  obtain ⟨d1, -, d3, d4, d5, d6, d7⟩ :=
    Paper2.SuccessClock.derived_le (n := n) (s := s) (q₁ := q₁) (q₂ := q₂) hw hQ
      (copies p .bit) (.ticket p) k
  obtain ⟨m1, m2, m3, m4, m5, -, m7, m8, m9, m10⟩ :=
    maxLen_derived s q₁ q₂ w Q hs hq₂ hw hQ (piCodec boolCodec p) (finCodec p)
      (defaultItemCodec n s) k
  exact ⟨⟨d1, d3, d4, d5, d6, d7⟩, ⟨m1, m2, m3, m4, m5, m7, m8, m9, m10⟩⟩

variable {p s q₁ q₂ w Q : ℕ} [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q] [NeZero s]

/-- The unrestricted-tag source arm. -/
theorem srcU_X (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices] (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin g.edges.length) * r) (k : ℕ)
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
    SrcU.srcUBound g hg hs r hq k i Z [] ≤ 2 * X ^ 7 := by
  obtain ⟨h2, h3, h4, h5, h6, h7, h8⟩ := xchain hX
  obtain ⟨⟨d1, d3, d4, d5, d6, d7⟩, ⟨m1, m2, m3, m4, m5, m7, m8, m9, m10⟩⟩ :=
    level_facts g.vertices p s q₁ q₂ w Q k (by omega) (NeZero.pos q₂) (NeZero.pos w)
      (NeZero.pos Q)
  unfold SrcU.srcUBound
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
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin g.edges.length) * r) (k : ℕ)
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
    SrcD.srcDBound g hg hs r hq k i ξ₀ j [] ≤ X ^ 5 := by
  obtain ⟨h2, h3, h4, h5, h6, h7, h8⟩ := xchain hX
  obtain ⟨⟨d1, d3, d4, d5, d6, d7⟩, ⟨m1, m2, m3, m4, m5, m7, m8, m9, m10⟩⟩ :=
    level_facts g.vertices p s q₁ q₂ w Q k (by omega) (NeZero.pos q₂) (NeZero.pos w)
      (NeZero.pos Q)
  unfold SrcD.srcDBound
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

/-- The source arm for every tag (`O = []`, as in `RLoop.stepClock`). -/
theorem srcX_X (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices] (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin g.edges.length) * r) (k : ℕ)
    (i : SourceConstruction.Items s (Fin g.vertices))
    (ξ₀ : SourceMatrix.Tail s (Column (Fin p → Bool) (Fin p)
      (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q k))
    (z : SourceMatrix.TaggedColumn q₁ q₂ s (Column (Fin p → Bool) (Fin p)
      (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q k)) {X : ℕ}
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
    SrcX.srcXBound g hg hs r hq k i ξ₀ [] z ≤ X ^ 8 := by
  obtain ⟨h2, h3, h4, h5, h6, h7, h8⟩ := xchain hX
  have hi1 := i.1.isLt
  have hxv := itemValue_le i.2
  cases z with
  | unrestricted Z =>
      have := srcU_X g hg hs r hq k i Z hX hS hc hl hG hmn
      simp only [SrcX.srcXBound]
      omega
  | diagonal j =>
      have := srcD_X g hg hs r hq k i ξ₀ j hX hS hc hl hG hmn
      simp only [SrcX.srcXBound]
      omega
  | fixedTail js =>
      have hL := levelBound_X p s q₁ q₂ w Q k hX (by omega) (by omega) (by omega) (by omega)
        (fun i hi => hW i (by omega))
      have hm : k * (DefaultWordLoop.levelBound p s q₁ q₂ w Q k + 2) ≤ X * (2 * X ^ 6) :=
        Nat.mul_le_mul (by omega) (by omega)
      have he : X * (2 * X ^ 6) = 2 * X ^ 7 := by ring
      have hwk := (hW k le_rfl).2
      simp only [SrcX.srcXBound]
      omega

end Paper2.SuccessClock2

#print axioms Paper2.SuccessClock2.srcU_X
#print axioms Paper2.SuccessClock2.srcD_X
#print axioms Paper2.SuccessClock2.srcX_X
