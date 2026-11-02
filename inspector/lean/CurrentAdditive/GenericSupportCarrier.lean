import CurrentAdditive.GenericSupportPropagation

/-! The support code carries every indexed recursive label, independently of
the rational weights used by the actual sampler. The base labels are compact
binary frames; higher labels retain the manuscript's recursive codec. -/

namespace Paper2.GenericSupportCarrier

open Paper2.GeneratorCode Paper2.GeneratorSource
open Paper2.RecursiveRequestCodeShape
open Paper2.RecursiveLabelCodecScratch
open Paper2.CompactFinCodec Paper2.CompactSupportShape
open Paper2.GenericSupportPropagation
open Paper2.RecursiveEntries

def codecs (nr nc n s q₁ q₂ w Q : ℕ) (k : ℕ) :=
  carrierCodecs s q₁ q₂ w Q (codec nr) (codec nc)
    (defaultItemCodec n s) k

def supportCodes (nr nc n s q₁ q₂ w Q L : ℕ) (k : ℕ) :=
  recursiveCodes n s q₁ q₂ w Q (support L) (support L) k

theorem vertex_item (n s : ℕ) (g : Fin (4 * s)) (v : Fin n) :
    Produces (meaning (vertexLabelsCode (V := Fin n) s))
      ((defaultItemCodec n s).encode (g, .inl v)) := by
  simp only [vertexLabelsCode, Fintype.card_fin, defaultItemCodec,
    prodCodec, sumCodec]
  change Produces
    (meaning (.append (.ticket (4 * s))
      (.append (.emit [false]) (.ticket n))))
    ((finCodec (4 * s)).encode g ++ false :: (finCodec n).encode v)
  exact append_words _ _ _ _ (ticket_index (4 * s) g)
    (append_words _ _ _ _ ((produces_emit _ _).mpr rfl)
      (ticket_index n v))

theorem auxiliary_item (n s : ℕ) (g : Fin (4 * s))
    (a : Fin (s - 3)) :
    Produces (meaning (auxiliaryLabelsCode s))
      ((defaultItemCodec n s).encode (g, .inr a)) := by
  simp only [auxiliaryLabelsCode, defaultItemCodec, prodCodec, sumCodec]
  change Produces
    (meaning (.append (.ticket (4 * s))
      (.append (.emit [true]) (.ticket (s - 3)))))
    ((finCodec (4 * s)).encode g ++ true ::
      (finCodec (s - 3)).encode a)
  exact append_words _ _ _ _ (ticket_index (4 * s) g)
    (append_words _ _ _ _ ((produces_emit _ _).mpr rfl)
      (ticket_index (s - 3) a))

theorem graphRows_typed {X : Type} (n q₁ q₂ s : ℕ) (c : Code)
    (cx : PrefixCodec X)
    (h : ∀ x, Produces (meaning c) (cx.encode x))
    (r : Paper2.SourceMatrix.RawRow q₁ q₂ s X
      (Paper2.SourceConstruction.Items s (Fin n))) :
    Produces (meaning (graphRowsCode (V := Fin n) q₁ q₂ s c))
      ((rawRowCodec q₁ q₂ s cx (defaultItemCodec n s)).encode r) := by
  cases r with
  | inl z =>
      apply (produces_branch3 (n := 512) (a := 510) (b := 511)
        (by decide) _ _ _ _).mpr
      refine ⟨⟨0, by decide⟩, ?_⟩
      simpa [graphRowsCode, rowsCode, rawRowCodec] using
        append_words (.emit [false]) (templateRowCode q₁ q₂ s c)
          [false] ((prodCodec (finCodec s)
            (piCodec (prodCodec (finCodec q₁) cx) q₂)).encode z)
          ((produces_emit _ _).mpr rfl)
          (templateRow_typed q₁ q₂ s c cx h z)
  | inr z =>
      rcases z with ⟨item, x⟩
      rcases item with ⟨g, choice⟩
      cases choice with
      | inl v =>
          apply (produces_branch3 (n := 512) (a := 510) (b := 511)
            (by decide) _ _ _ _).mpr
          refine ⟨⟨510, by decide⟩, ?_⟩
          simpa [graphRowsCode, rowsCode, rawRowCodec] using
            append_words (.emit [true])
              (.append (vertexLabelsCode (V := Fin n) s) c)
              [true] ((defaultItemCodec n s).encode (g, .inl v) ++ cx.encode x)
              ((produces_emit _ _).mpr rfl)
              (append_words _ _ _ _ (vertex_item n s g v) (h x))
      | inr a =>
          apply (produces_branch3 (n := 512) (a := 510) (b := 511)
            (by decide) _ _ _ _).mpr
          refine ⟨⟨511, by decide⟩, ?_⟩
          simpa [graphRowsCode, rowsCode, rawRowCodec] using
            append_words (.emit [true])
              (.append (auxiliaryLabelsCode s) c)
              [true] ((defaultItemCodec n s).encode (g, .inr a) ++ cx.encode x)
              ((produces_emit _ _).mpr rfl)
              (append_words _ _ _ _ (auxiliary_item n s g a) (h x))

theorem carrier_support {nr nc n s q₁ q₂ w Q L : ℕ}
    (hr : nr ≤ 2 ^ L) (hc : nc ≤ 2 ^ L) (k : ℕ) :
    (∀ x : Row (Fin nr) (Fin nc) (Paper2.SourceConstruction.Items s (Fin n))
        s q₁ q₂ w Q k,
      Produces (meaning (supportCodes nr nc n s q₁ q₂ w Q L k).1)
        ((codecs nr nc n s q₁ q₂ w Q k).1.encode x)) ∧
    (∀ y : Column (Fin nr) (Fin nc) (Paper2.SourceConstruction.Items s (Fin n))
        s q₁ q₂ w Q k,
      Produces (meaning (supportCodes nr nc n s q₁ q₂ w Q L k).2)
        ((codecs nr nc n s q₁ q₂ w Q k).2.encode y)) := by
  induction k with
  | zero =>
      exact ⟨fun x => support_index hr x, fun y => support_index hc y⟩
  | succ k ih =>
      constructor
      · intro x
        change Produces
          (meaning (copies Q
            (.append (.ticket w)
              (taggedCode q₁ q₂ s (supportCodes nr nc n s q₁ q₂ w Q L k).2))))
          ((piCodec (prodCodec (finCodec w)
            (taggedColumnCodec q₁ q₂ s (codecs nr nc n s q₁ q₂ w Q k).2)) Q).encode x)
        exact copies_typed Q _ _
          (ticket_pair w _ _
            (tagged_typed q₁ q₂ s _ _ ih.2)) x
      · intro y
        change Produces
          (meaning (.append (.ticket Q)
            (copies w
              (graphRowsCode (V := Fin n) q₁ q₂ s
                (supportCodes nr nc n s q₁ q₂ w Q L k).1))))
          ((prodCodec (finCodec Q)
            (piCodec (rawRowCodec q₁ q₂ s
              (codecs nr nc n s q₁ q₂ w Q k).1
              (defaultItemCodec n s)) w)).encode y)
        exact ticket_pair Q _ _
          (copies_typed w _ _
            (GenericSupportCarrier.graphRows_typed n q₁ q₂ s _ _ ih.1)) y

theorem request_subcodes_support {nr nc n s q₁ q₂ w Q L : ℕ}
    (hr : nr ≤ 2 ^ L) (hc : nc ≤ 2 ^ L) (k : ℕ) :
    let C := codecs nr nc n s q₁ q₂ w Q k
    let c := supportCodes nr nc n s q₁ q₂ w Q L k
    (∀ e, Produces (meaning (.append (.ticket w) (taggedCode q₁ q₂ s c.2)))
      ((prodCodec (finCodec w) (taggedColumnCodec q₁ q₂ s C.2)).encode e)) ∧
    (∀ r, Produces (meaning (graphRowsCode (V := Fin n) q₁ q₂ s c.1))
      ((rawRowCodec q₁ q₂ s C.1 (defaultItemCodec n s)).encode r)) := by
  intro C c
  have h := carrier_support (n := n) (s := s) (q₁ := q₁) (q₂ := q₂)
    (w := w) (Q := Q) hr hc k
  exact ⟨ticket_pair w _ _ (tagged_typed q₁ q₂ s _ _ h.2),
    GenericSupportCarrier.graphRows_typed n q₁ q₂ s _ _ h.1⟩

#print axioms carrier_support
#print axioms graphRows_typed
#print axioms request_subcodes_support

end Paper2.GenericSupportCarrier
