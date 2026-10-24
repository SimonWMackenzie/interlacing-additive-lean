import Paper2.GeneratorCode
import Paper2.EncodedSamplerAlgebra
import Paper2.RecursiveSampling

/-! First-order encodings of the actual recursive source generators. -/

namespace Paper2.GeneratorSource

open RecursiveSamplingProgram RecursiveSamplingLaws RecursiveSampling
open RecursiveLabelCodecScratch EncodedSamplerAlgebra GeneratorCode

theorem meaning_copies (n : ℕ) (c : Code) :
    meaning (copies n c) = repeatedConcat (meaning c) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [copies, meaning, repeatedConcat, concat, ih]

theorem meaning_append (c d : Code) :
    meaning (.append c d) =
      Program.bind (meaning c)
        (fun xs => Program.map (fun ys => xs ++ ys) (meaning d)) := rfl

def outerCode (q₁ q₂ s : ℕ) (c : Code) : Code :=
  .append (.ticket q₂) (copies (q₁ + s + 1) c)

theorem outer_exact {Y : Type} {q₁ q₂ s : ℕ} [NeZero q₂]
    (cy : PrefixCodec Y) (p : Program Y) (c : Code)
    (hc : meaning c = Program.map cy.encode p) :
    meaning (outerCode q₁ q₂ s c) =
      Program.map (outerColumnCodec q₁ q₂ s cy).encode
        (outer (q₁ := q₁) (q₂ := q₂) (s := s) p) := by
  simp only [outerCode, meaning_append, meaning_copies, hc]
  simp only [outer, outerColumnCodec, uniform]
  rw [encoded_prod]
  rw [encoded_iid]
  rw [← meaning_ticket q₂ (Nat.pos_of_ne_zero (NeZero.ne q₂))]

def rawCode (q₁ q₂ s : ℕ) (c : Code) : Code :=
  .append (copies (s + 1) c) (copies s (outerCode q₁ q₂ s c))

theorem raw_exact {Y : Type} {q₁ q₂ s : ℕ} [NeZero q₂]
    (cy : PrefixCodec Y) (p : Program Y) (c : Code)
    (hc : meaning c = Program.map cy.encode p) :
    meaning (rawCode q₁ q₂ s c) =
      Program.map (rawColumnCodec q₁ q₂ s cy).encode
        (raw (q₁ := q₁) (q₂ := q₂) (s := s) p) := by
  simp only [rawCode, meaning_append, meaning_copies, hc]
  simp only [raw, rawColumnCodec]
  rw [encoded_prod, encoded_iid, encoded_iid]
  rw [outer_exact cy p c hc]

def fixedTailCode (q₁ q₂ s : ℕ) (c : Code) : Code :=
  copies s (outerCode q₁ q₂ s c)

theorem fixedTail_exact {Y : Type} {q₁ q₂ s : ℕ} [NeZero q₂]
    (cy : PrefixCodec Y) (p : Program Y) (c : Code)
    (hc : meaning c = Program.map cy.encode p) :
    meaning (fixedTailCode q₁ q₂ s c) =
      Program.map (piCodec (outerColumnCodec q₁ q₂ s cy) s).encode
        (fixedTail (q₁ := q₁) (q₂ := q₂) (s := s) p) := by
  simp only [fixedTailCode, meaning_copies, fixedTail]
  rw [encoded_iid]
  rw [outer_exact cy p c hc]

theorem meaning_prefix (bits : List Bool) (c : Code) :
    meaning (.append (.emit bits) c) =
      Program.map (fun xs => bits ++ xs) (meaning c) := rfl

def taggedCode (q₁ q₂ s : ℕ) (c : Code) : Code :=
  .branch3 256 254 255
    (.append (.emit [false]) (rawCode q₁ q₂ s c))
    (.append (.emit [true, false]) (fixedTailCode q₁ q₂ s c))
    (.append (.emit [true, true]) (outerCode q₁ q₂ s c))

theorem tagged_exact {Y : Type} {q₁ q₂ s : ℕ} [NeZero q₂]
    (cy : PrefixCodec Y) (p : Program Y) (c : Code)
    (hc : meaning c = Program.map cy.encode p) :
    meaning (taggedCode q₁ q₂ s c) =
      Program.map (taggedColumnCodec q₁ q₂ s cy).encode
        (tagged (q₁ := q₁) (q₂ := q₂) (s := s) p) := by
  change (Program.draw 256 (by decide) fun t =>
      if t.val < 254 then meaning (.append (.emit [false]) (rawCode q₁ q₂ s c))
      else if t.val < 255 then
        meaning (.append (.emit [true, false]) (fixedTailCode q₁ q₂ s c))
      else meaning (.append (.emit [true, true]) (outerCode q₁ q₂ s c))) = _
  simp only [tagged, Program.map_draw]
  congr 1
  funext t
  by_cases h₁ : t.val < 254
  · simp only [h₁, ↓reduceIte, Program.map_map]
    rw [meaning_prefix, raw_exact cy p c hc, Program.map_map]
    congr 1
  · by_cases h₂ : t.val = 254
    · have hlt : t.val < 255 := by omega
      simp only [h₂, show ¬ (254 : ℕ) < 254 by decide,
        show (254 : ℕ) < 255 by decide, ite_false, ite_true]
      rw [meaning_prefix, fixedTail_exact cy p c hc]
      simp only [Program.map_map]
      congr 1
    · have hlt : ¬ t.val < 255 := by omega
      simp only [h₁, h₂, hlt, ↓reduceIte, Program.map_map]
      rw [meaning_prefix, outer_exact cy p c hc, Program.map_map]
      congr 1

def templateCode (q₁ q₂ : ℕ) (c : Code) : Code :=
  copies q₂ (.append (.ticket q₁) c)

theorem template_exact {X : Type} {q₁ q₂ : ℕ} [NeZero q₁]
    (cx : PrefixCodec X) (p : Program X) (c : Code)
    (hc : meaning c = Program.map cx.encode p) :
    meaning (templateCode q₁ q₂ c) =
      Program.map (piCodec (prodCodec (finCodec q₁) cx) q₂).encode
        (template (q₁ := q₁) (q₂ := q₂) p) := by
  simp only [templateCode, meaning_copies, template]
  rw [encoded_iid, encoded_prod]
  simp only [meaning_append, hc, uniform]
  rw [← meaning_ticket q₁ (Nat.pos_of_ne_zero (NeZero.ne q₁))]

def templateRowCode (q₁ q₂ s : ℕ) (c : Code) : Code :=
  .append (.ticket s) (templateCode q₁ q₂ c)

theorem templateRow_exact {X : Type} {q₁ q₂ s : ℕ}
    [NeZero q₁] [NeZero s]
    (cx : PrefixCodec X) (p : Program X) (c : Code)
    (hc : meaning c = Program.map cx.encode p) :
    meaning (templateRowCode q₁ q₂ s c) =
      Program.map
        (prodCodec (finCodec s) (piCodec (prodCodec (finCodec q₁) cx) q₂)).encode
        (templateRow (q₁ := q₁) (q₂ := q₂) (s := s) p) := by
  simp only [templateRowCode, meaning_append, templateRow]
  rw [encoded_prod, template_exact cx p c hc]
  simp only [uniform]
  rw [← meaning_ticket s (Nat.pos_of_ne_zero (NeZero.ne s))]

theorem encoded_pair {A B : Type} (fa : A → List Bool) (fb : B → List Bool)
    (p : Program A) (q : Program B) :
    Program.map (fun z : A × B => fa z.1 ++ fb z.2)
      (RecursiveSamplingLaws.prod p q) =
    Program.bind (Program.map fa p)
      (fun xs => Program.map (fun ys => xs ++ ys) (Program.map fb q)) := by
  rw [RecursiveSamplingLaws.prod, Program.map_bind, Program.bind_map]
  congr 1
  funext a
  simp only [Program.map_map]
  congr 1

theorem pairCode_exact {A B : Type} (fa : A → List Bool) (fb : B → List Bool)
    (p : Program A) (q : Program B) (ca cb : Code)
    (ha : meaning ca = Program.map fa p)
    (hb : meaning cb = Program.map fb q) :
    meaning (.append ca cb) =
      Program.map (fun z : A × B => fa z.1 ++ fb z.2)
        (RecursiveSamplingLaws.prod p q) := by
  rw [meaning_append, ha, hb, encoded_pair]

def rowsCode (q₁ q₂ s : ℕ) (vertices auxiliaries c : Code) : Code :=
  .branch3 512 510 511
    (.append (.emit [false]) (templateRowCode q₁ q₂ s c))
    (.append (.emit [true]) (.append vertices c))
    (.append (.emit [true]) (.append auxiliaries c))

theorem rows_exact {X V A : Type} {q₁ q₂ s : ℕ}
    [NeZero q₁] [NeZero s]
    (cx : PrefixCodec X) (ci : PrefixCodec (V ⊕ A))
    (p : Program X) (vertices : Program V) (auxiliaries : Program A)
    (c cv ca : Code)
    (hc : meaning c = Program.map cx.encode p)
    (hv : meaning cv = Program.map (fun v => ci.encode (.inl v)) vertices)
    (ha : meaning ca = Program.map (fun a => ci.encode (.inr a)) auxiliaries) :
    meaning (rowsCode q₁ q₂ s cv ca c) =
      Program.map (rawRowCodec q₁ q₂ s cx ci).encode
        (rows (q₁ := q₁) (q₂ := q₂) (s := s) vertices auxiliaries p) := by
  change (Program.draw 512 (by decide) fun t =>
      if t.val < 510 then meaning (.append (.emit [false]) (templateRowCode q₁ q₂ s c))
      else if t.val < 511 then meaning (.append (.emit [true]) (.append cv c))
      else meaning (.append (.emit [true]) (.append ca c))) = _
  simp only [rows, Program.map_draw]
  congr 1
  funext t
  by_cases h₁ : t.val < 510
  · simp only [h₁, ↓reduceIte]
    rw [meaning_prefix, templateRow_exact cx p c hc]
    simp only [Program.map_map]
    congr 1
  · by_cases h₂ : t.val = 510
    · simp only [h₂, show ¬ (510 : ℕ) < 510 by decide,
        show (510 : ℕ) < 511 by decide, ite_false, ite_true]
      rw [meaning_prefix,
        pairCode_exact (fun v => ci.encode (.inl v)) cx.encode vertices p cv c hv hc]
      simp only [Program.map_map]
      congr 1
    · have hlt : ¬ t.val < 511 := by omega
      simp only [h₁, h₂, hlt, ↓reduceIte]
      rw [meaning_prefix,
        pairCode_exact (fun a => ci.encode (.inr a)) cx.encode auxiliaries p ca c ha hc]
      simp only [Program.map_map]
      congr 1

def vertexCodec {V : Type} [Fintype V] (order : Fin (Fintype.card V) ≃ V) :
    PrefixCodec V := transportCodec order (finCodec (Fintype.card V))

def splitItemCodec {V : Type} (s : ℕ) (cv : PrefixCodec V) :
    PrefixCodec ((Fin (4 * s) × V) ⊕ (Fin (4 * s) × Fin (s - 3))) :=
  transportCodec (SourceLawBinding.itemEquiv s V).symm
    (prodCodec (finCodec (4 * s)) (sumCodec cv (finCodec (s - 3))))

def vertexLabelsCode {V : Type} [Fintype V] (s : ℕ) : Code :=
  .append (.ticket (4 * s))
    (.append (.emit [false]) (.ticket (Fintype.card V)))

def auxiliaryLabelsCode (s : ℕ) : Code :=
  .append (.ticket (4 * s))
    (.append (.emit [true]) (.ticket (s - 3)))

theorem vertex_exact {V : Type} [Fintype V] [Nonempty V]
    (order : Fin (Fintype.card V) ≃ V) :
    meaning (.ticket (Fintype.card V)) =
      Program.map (vertexCodec order).encode (vertex order) := by
  rw [meaning_ticket (Fintype.card V) Fintype.card_pos]
  simp only [vertex, vertexCodec, Program.map_map]
  congr 1
  funext i
  simp [transportCodec]

theorem vertexLabels_exact {V : Type} [Fintype V] [Nonempty V]
    {s : ℕ} (hs : 4 ≤ s) (order : Fin (Fintype.card V) ≃ V) :
    meaning (vertexLabelsCode (V := V) s) =
      Program.map
        (fun z => (splitItemCodec s (vertexCodec order)).encode (.inl z))
        (vertexLabels order hs) := by
  simp only [vertexLabelsCode, vertexLabels]
  rw [meaning_append, meaning_prefix]
  rw [vertex_exact order]
  rw [meaning_ticket (4 * s) (by omega)]
  simp only [Program.map_map]
  rw [RecursiveSamplingLaws.prod, Program.map_bind]
  simp only [Program.bind_map, Program.map_map]
  congr 1

theorem auxiliaryLabels_exact {V : Type} [Fintype V]
    {s : ℕ} (hs : 4 ≤ s) (cv : PrefixCodec V) :
    meaning (auxiliaryLabelsCode s) =
      Program.map
        (fun z => (splitItemCodec s cv).encode (.inr z))
        (auxiliaryLabels s hs) := by
  simp only [auxiliaryLabelsCode, auxiliaryLabels]
  rw [meaning_append, meaning_prefix]
  rw [meaning_ticket (4 * s) (by omega)]
  rw [meaning_ticket (s - 3) (by omega)]
  simp only [Program.map_map]
  rw [RecursiveSamplingLaws.prod, Program.map_bind]
  simp only [Program.bind_map, Program.map_map]
  congr 1

def graphRowCodec {X V : Type} (q₁ q₂ s : ℕ)
    (cx : PrefixCodec X) (cv : PrefixCodec V) :
    PrefixCodec (SourceMatrix.RawRow q₁ q₂ s X (SourceConstruction.Items s V)) :=
  transportCodec (SourceLawBinding.rawRowEquiv q₁ q₂ s X V)
    (rawRowCodec q₁ q₂ s cx (splitItemCodec s cv))

def graphRowsCode {V : Type} [Fintype V] (q₁ q₂ s : ℕ) (c : Code) : Code :=
  rowsCode q₁ q₂ s (vertexLabelsCode (V := V) s) (auxiliaryLabelsCode s) c

theorem graphRows_exact {X V : Type} [Fintype V] [Nonempty V]
    {q₁ q₂ s : ℕ} [NeZero q₁]
    (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (cx : PrefixCodec X) (p : Program X) (c : Code)
    (hc : meaning c = Program.map cx.encode p) :
    meaning (graphRowsCode (V := V) q₁ q₂ s c) =
      Program.map (graphRowCodec q₁ q₂ s cx (vertexCodec order)).encode
        (graphRows (q₁ := q₁) (q₂ := q₂) order hs p) := by
  letI : NeZero s := ⟨by omega⟩
  calc
    meaning (graphRowsCode (V := V) q₁ q₂ s c) =
        Program.map
          (rawRowCodec q₁ q₂ s cx (splitItemCodec s (vertexCodec order))).encode
          (rows (vertexLabels order hs) (auxiliaryLabels s hs) p) := by
            exact rows_exact cx (splitItemCodec s (vertexCodec order)) p
              (vertexLabels order hs) (auxiliaryLabels s hs) c
              (vertexLabelsCode (V := V) s) (auxiliaryLabelsCode s)
              hc (vertexLabels_exact hs order)
              (auxiliaryLabels_exact hs (vertexCodec order))
    _ = _ := by
      simp only [graphRows, graphRowCodec, Program.map_map]
      congr 1
      funext z
      simp [transportCodec]

theorem graphRowCodec_encode_eq {X V : Type} (q₁ q₂ s : ℕ)
    (cx : PrefixCodec X) (cv : PrefixCodec V)
    (z : SourceMatrix.RawRow q₁ q₂ s X (SourceConstruction.Items s V)) :
    (graphRowCodec q₁ q₂ s cx cv).encode z =
      (rawRowCodec q₁ q₂ s cx
        (prodCodec (finCodec (4 * s)) (sumCodec cv (finCodec (s - 3))))).encode z := by
  cases z with
  | inl z => rfl
  | inr z =>
      rcases z with ⟨⟨g, v⟩, x⟩
      cases v <;> rfl

theorem graphRows_canonical_exact {X : Type} {n q₁ q₂ s : ℕ}
    [NeZero n] [NeZero q₁] (hs : 4 ≤ s)
    (cx : PrefixCodec X) (p : Program X) (c : Code)
    (hc : meaning c = Program.map cx.encode p) :
    meaning (graphRowsCode (V := Fin n) q₁ q₂ s c) =
      Program.map (rawRowCodec q₁ q₂ s cx (defaultItemCodec n s)).encode
        (graphRows (q₁ := q₁) (q₂ := q₂)
          (order := finCongr (Fintype.card_fin n)) hs p) := by
  rw [graphRows_exact (finCongr (Fintype.card_fin n)) hs cx p c hc]
  congr 1
  funext z
  rw [graphRowCodec_encode_eq]
  rfl

theorem seedRow_exact (p : ℕ) :
    meaning (copies p .bit) =
      Program.map (piCodec boolCodec p).encode (RecursiveSamplingSeed.seedRow p) := by
  rw [meaning_copies]
  change repeatedConcat (Program.map boolCodec.encode RecursiveSamplingSeed.bit) p = _
  rw [← encoded_iid]
  rfl

theorem seedColumn_exact (p : ℕ) (hp : 0 < p) :
    meaning (.ticket p) =
      Program.map (finCodec p).encode (RecursiveSamplingSeed.seedColumn p hp) := by
  rw [meaning_ticket p hp]
  rfl

theorem copies_exact {A : Type} (n : ℕ) (ca : PrefixCodec A)
    (p : Program A) (c : Code)
    (hc : meaning c = Program.map ca.encode p) :
    meaning (copies n c) = Program.map (piCodec ca n).encode (iid p n) := by
  rw [meaning_copies, hc, encoded_iid]

theorem ticketProd_exact {A : Type} (n : ℕ) [NeZero n]
    (ca : PrefixCodec A) (p : Program A) (c : Code)
    (hc : meaning c = Program.map ca.encode p) :
    meaning (.append (.ticket n) c) =
      Program.map (prodCodec (finCodec n) ca).encode
        (prod (uniform n) p) := by
  rw [meaning_append, encoded_prod]
  simp only [uniform]
  rw [← meaning_ticket n (Nat.pos_of_ne_zero (NeZero.ne n))]
  rw [hc]

def recursiveCodes (n s q₁ q₂ w Q : ℕ) (row₀ col₀ : Code) :
    ℕ → Code × Code
  | 0 => (row₀, col₀)
  | k + 1 =>
      let previous := recursiveCodes n s q₁ q₂ w Q row₀ col₀ k
      (copies Q (.append (.ticket w) (taggedCode q₁ q₂ s previous.2)),
        .append (.ticket Q)
          (copies w (graphRowsCode (V := Fin n) q₁ q₂ s previous.1)))

theorem recursiveCodes_exact {X₀ Y₀ : Type} {n s q₁ q₂ w Q : ℕ}
    [NeZero n] [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q]
    (hs : 4 ≤ s) (cx₀ : PrefixCodec X₀) (cy₀ : PrefixCodec Y₀)
    (row₀ : Program X₀) (col₀ : Program Y₀) (cr₀ cc₀ : Code)
    (hr₀ : meaning cr₀ = Program.map cx₀.encode row₀)
    (hc₀ : meaning cc₀ = Program.map cy₀.encode col₀) (k : ℕ) :
    let C := carrierCodecs s q₁ q₂ w Q cx₀ cy₀ (defaultItemCodec n s) k
    let P := programs (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
      (finCongr (Fintype.card_fin n)) hs row₀ col₀ k
    meaning (recursiveCodes n s q₁ q₂ w Q cr₀ cc₀ k).1 =
        Program.map C.1.encode P.1 ∧
      meaning (recursiveCodes n s q₁ q₂ w Q cr₀ cc₀ k).2 =
        Program.map C.2.encode P.2 := by
  induction k with
  | zero => exact ⟨hr₀, hc₀⟩
  | succ k ih =>
      let oldCode := recursiveCodes n s q₁ q₂ w Q cr₀ cc₀ k
      let oldCodec := carrierCodecs s q₁ q₂ w Q cx₀ cy₀ (defaultItemCodec n s) k
      let oldProgram := programs (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
        (finCongr (Fintype.card_fin n)) hs row₀ col₀ k
      have htag := tagged_exact (q₁ := q₁) (q₂ := q₂) (s := s)
        oldCodec.2 oldProgram.2 oldCode.2 ih.2
      have hrowUnit := ticketProd_exact w
        (taggedColumnCodec q₁ q₂ s oldCodec.2)
        (tagged (q₁ := q₁) (q₂ := q₂) (s := s) oldProgram.2)
        (taggedCode q₁ q₂ s oldCode.2) htag
      have hrow := copies_exact Q
        (prodCodec (finCodec w) (taggedColumnCodec q₁ q₂ s oldCodec.2))
        (prod (uniform w) (tagged oldProgram.2))
        (.append (.ticket w) (taggedCode q₁ q₂ s oldCode.2)) hrowUnit
      have hgraph := graphRows_canonical_exact (n := n) (q₁ := q₁) (q₂ := q₂)
        (s := s) hs oldCodec.1 oldProgram.1 oldCode.1 ih.1
      have hcolUnit := copies_exact w
        (rawRowCodec q₁ q₂ s oldCodec.1 (defaultItemCodec n s))
        (graphRows (q₁ := q₁) (q₂ := q₂)
          (finCongr (Fintype.card_fin n)) hs oldProgram.1)
        (graphRowsCode (V := Fin n) q₁ q₂ s oldCode.1) hgraph
      have hcol := ticketProd_exact Q
        (piCodec (rawRowCodec q₁ q₂ s oldCodec.1 (defaultItemCodec n s)) w)
        (iid (graphRows (q₁ := q₁) (q₂ := q₂)
          (finCongr (Fintype.card_fin n)) hs oldProgram.1) w)
        (copies w (graphRowsCode (V := Fin n) q₁ q₂ s oldCode.1)) hcolUnit
      exact ⟨hrow, hcol⟩

def seedRecursiveCodes (n p s q₁ q₂ w Q : ℕ) (k : ℕ) : Code × Code :=
  recursiveCodes n s q₁ q₂ w Q (copies p .bit) (.ticket p) k

theorem seedRecursiveCodes_exact {n p s q₁ q₂ w Q : ℕ}
    [NeZero n] [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q]
    (hp : 0 < p) (hs : 4 ≤ s) (k : ℕ) :
    let C := defaultCarrierCodecs n p s q₁ q₂ w Q k
    let P := programs (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
      (finCongr (Fintype.card_fin n)) hs
      (RecursiveSamplingSeed.seedRow p) (RecursiveSamplingSeed.seedColumn p hp) k
    meaning (seedRecursiveCodes n p s q₁ q₂ w Q k).1 =
        Program.map C.1.encode P.1 ∧
      meaning (seedRecursiveCodes n p s q₁ q₂ w Q k).2 =
        Program.map C.2.encode P.2 := by
  exact recursiveCodes_exact hs (piCodec boolCodec p) (finCodec p)
    (RecursiveSamplingSeed.seedRow p) (RecursiveSamplingSeed.seedColumn p hp)
    (copies p .bit) (.ticket p) (seedRow_exact p) (seedColumn_exact p hp) k

def scheduledCodes (n m L Δ : ℕ) (γ : ℚ) (k : ℕ) : Code × Code :=
  seedRecursiveCodes n (LookupSeed.width L)
    (SourceProfileParameters.width L)
    (SourceProfileParameters.width L - 2)
    (SourceProfileParameters.outerWidth L)
    (ParameterizedCanonicalSource.restorationWidth L)
    (ParameterizedCanonicalSource.coverWidth n m L Δ γ) k

def scheduledPrograms {n m : ℕ} [NeZero n] (L Δ : ℕ) (γ : ℚ) (k : ℕ) :=
  letI : NeZero (SourceProfileParameters.width L - 2) := ⟨by
    have h := SourceProfileParameters.width_admissible L
    omega⟩
  letI : NeZero (SourceProfileParameters.outerWidth L) := ⟨by
    unfold SourceProfileParameters.outerWidth
    positivity⟩
  letI : NeZero (ParameterizedCanonicalSource.restorationWidth L) := ⟨by
    unfold ParameterizedCanonicalSource.restorationWidth RestorationWidthScheduleScratch.width
    positivity⟩
  letI : NeZero (ParameterizedCanonicalSource.coverWidth n m L Δ γ) := ⟨by
    rw [show ParameterizedCanonicalSource.coverWidth n m L Δ γ =
      2 ^ ParameterizedCanonicalSource.coverDepth n m L Δ γ from
      SourceOverheadBounds.actualQ_pow (V := Fin n) (E := Fin m) L γ Δ]
    positivity⟩
  programs (q₁ := SourceProfileParameters.width L - 2)
    (q₂ := SourceProfileParameters.outerWidth L)
    (w := ParameterizedCanonicalSource.restorationWidth L)
    (Q := ParameterizedCanonicalSource.coverWidth n m L Δ γ)
    (finCongr (Fintype.card_fin n)) (SourceProfiles.width_ge_four L)
    (RecursiveSamplingSeed.seedRow (LookupSeed.width L))
    (RecursiveSamplingSeed.seedColumn (LookupSeed.width L)
      (by unfold LookupSeed.width; positivity)) k

theorem scheduledCodes_exact {n m : ℕ} [NeZero n]
    (L Δ : ℕ) (γ : ℚ) (k : ℕ) :
    let C := scheduledCarrierCodecs n m L Δ γ k
    let P := scheduledPrograms (n := n) (m := m) L Δ γ k
    meaning (scheduledCodes n m L Δ γ k).1 = Program.map C.1.encode P.1 ∧
      meaning (scheduledCodes n m L Δ γ k).2 = Program.map C.2.encode P.2 := by
  letI : NeZero (SourceProfileParameters.width L - 2) := ⟨by
    have h := SourceProfileParameters.width_admissible L
    omega⟩
  letI : NeZero (SourceProfileParameters.outerWidth L) := ⟨by
    unfold SourceProfileParameters.outerWidth
    positivity⟩
  letI : NeZero (ParameterizedCanonicalSource.restorationWidth L) := ⟨by
    unfold ParameterizedCanonicalSource.restorationWidth RestorationWidthScheduleScratch.width
    positivity⟩
  letI : NeZero (ParameterizedCanonicalSource.coverWidth n m L Δ γ) := ⟨by
    rw [show ParameterizedCanonicalSource.coverWidth n m L Δ γ =
      2 ^ ParameterizedCanonicalSource.coverDepth n m L Δ γ from
      SourceOverheadBounds.actualQ_pow (V := Fin n) (E := Fin m) L γ Δ]
    positivity⟩
  exact seedRecursiveCodes_exact (n := n) (p := LookupSeed.width L)
    (s := SourceProfileParameters.width L)
    (q₁ := SourceProfileParameters.width L - 2)
    (q₂ := SourceProfileParameters.outerWidth L)
    (w := ParameterizedCanonicalSource.restorationWidth L)
    (Q := ParameterizedCanonicalSource.coverWidth n m L Δ γ)
    (by unfold LookupSeed.width; positivity)
    (SourceProfiles.width_ge_four L) k

#print axioms meaning_copies
#print axioms outer_exact
#print axioms raw_exact
#print axioms fixedTail_exact
#print axioms tagged_exact
#print axioms template_exact
#print axioms templateRow_exact
#print axioms rows_exact
#print axioms vertexLabels_exact
#print axioms auxiliaryLabels_exact
#print axioms graphRows_exact
#print axioms graphRows_canonical_exact
#print axioms seedRow_exact
#print axioms recursiveCodes_exact
#print axioms seedRecursiveCodes_exact
#print axioms scheduledCodes_exact

end Paper2.GeneratorSource
