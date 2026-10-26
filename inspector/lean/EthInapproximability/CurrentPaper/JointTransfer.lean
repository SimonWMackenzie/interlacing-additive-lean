import EthInapproximability.CurrentPaper.Construction
import EthInapproximability.ParameterizedNP.TerminalStateRealization

/-!
# Physical quotient geometry for the current two-support construction

Source: v8 `A-stage4-details.tex`, `lem:paper-template-transfer`.
The reference reservoir maps regularly onto the WHOLE selector tuple. The
diagonal reservoir maps regularly only onto one chosen selector coordinate.
All reservoirs and entries below belong to `Construction.protectedMatrix`.
No communication lower bound, graph promise or sampler balancedness is assumed.

Only the generic finite regular-map and section geometry of the old route is
reused. Its three-support constructor and stronger two-stream threshold are
not used.
-/

noncomputable section
open scoped Classical

namespace EthInapproximability.CurrentPaper.JointTransfer

open Finset
open Construction
open EthInapproximability.ParameterizedNP.TerminalStateRealization

universe u v w

/-- An actual embedded product reservoir has uniform quotient fibers. -/
theorem regularOn_embedded_product {A : Type u} {B : Type v} {K : Type w}
    [Fintype B] [Fintype K] [DecidableEq A] [DecidableEq B]
    (e : B × K ↪ A) (f : A → B) (h : ∀ b k, f (e (b, k)) = b) :
    RegularOn (Finset.univ.image e) f (Fintype.card K) := by
  classical
  intro b
  have heq : (Finset.univ.image e).filter (fun a => f a = b) =
      (({b} : Finset B) ×ˢ (Finset.univ : Finset K)).image e := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_product, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨⟨b', k⟩, rfl⟩, hb⟩
      rw [h] at hb
      exact ⟨(b', k), ⟨hb, trivial⟩, rfl⟩
    · rintro ⟨⟨b', k⟩, ⟨hb, _⟩, rfl⟩
      exact ⟨⟨(b', k), rfl⟩, (h b' k).trans hb⟩
  rw [heq, Finset.card_image_of_injective _ e.injective]
  simp

section PhysicalRows

variable {Y : Type u} [Fintype Y]

abbrev ExtraInputs (s : ℕ) (Y : Type u) := Fin (s + 1) → Y

def referenceMultiplicity (a s q : ℕ) : ℕ :=
  WeightedDuplication.copies
    (WeightedDuplication.columnSupport (RawColumns a s q Y) (SecondRows a s q Y))
    WeightedDuplication.columnWeight 0

def diagonalMultiplicity (a s q : ℕ) : ℕ :=
  WeightedDuplication.copies
    (WeightedDuplication.columnSupport (RawColumns a s q Y) (SecondRows a s q Y))
    WeightedDuplication.columnWeight 1

abbrev ReferenceLabels (a s q : ℕ) (Y : Type u) [Fintype Y] :=
  ExtraInputs s Y ×
    (Fin (referenceMultiplicity (Y := Y) a s q) × Fin (uniformCopies (Y := Y) a s q))

abbrev DiagonalLabels (a s q : ℕ) (Y : Type u) [Fintype Y] :=
  Fin (diagonalMultiplicity (Y := Y) a s q) × Fin (uniformCopies (Y := Y) a s q)

/-- Physical reference row: tuple, unused graph input, and both copy indices. -/
def referenceEmbedding (a s q : ℕ) :
    ThirdColumns a s q Y × ReferenceLabels a s q Y ↪ ProtectedColumns a s q Y where
  toFun z := (⟨0, ((z.2.1, z.1), z.2.2.1)⟩, z.2.2.2)
  inj' := by
    rintro ⟨t, ξ, k, l⟩ ⟨t', ξ', k', l'⟩ h
    have hd : ((ξ, t), k) = ((ξ', t'), k') :=
      eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Prod.fst h)).2
    have ht : t = t' := congrArg (fun z => z.1.2) hd
    have hξ : ξ = ξ' := congrArg (fun z => z.1.1) hd
    have hk : k = k' := congrArg Prod.snd hd
    have hl : l = l' := congrArg (fun z : ProtectedColumns a s q Y => z.2) h
    cases ht; cases hξ; cases hk; cases hl; rfl

/-- Physical diagonal row: one shared `(alpha,gamma)` and both copy indices. -/
def diagonalEmbedding (a s q : ℕ) :
    SecondRows a s q Y × DiagonalLabels a s q Y ↪ ProtectedColumns a s q Y where
  toFun z := (⟨1, (z.1, z.2.1)⟩, z.2.2)
  inj' := by
    rintro ⟨t, k, l⟩ ⟨t', k', l'⟩ h
    have hd : (t, k) = (t', k') :=
      eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Prod.fst h)).2
    have ht : t = t' := congrArg Prod.fst hd
    have hk : k = k' := congrArg Prod.snd hd
    have hl : l = l' := congrArg (fun z : ProtectedColumns a s q Y => z.2) h
    cases ht; cases hk; cases hl; rfl

def referenceRows (a s q : ℕ) : Finset (ProtectedColumns a s q Y) :=
  Finset.univ.image (referenceEmbedding (Y := Y) a s q)

def diagonalRows (a s q : ℕ) : Finset (ProtectedColumns a s q Y) :=
  Finset.univ.image (diagonalEmbedding (Y := Y) a s q)

def selectorTuple {a s q : ℕ} (r : ProtectedColumns a s q Y) :
    ThirdColumns a s q Y :=
  (WeightedDuplication.columnForget (diagonal (a := a) (s := s) (q := q)) r).2

@[simp] theorem selectorTuple_reference (a s q : ℕ)
    (t : ThirdColumns a s q Y) (k : ReferenceLabels a s q Y) :
    selectorTuple (referenceEmbedding a s q (t, k)) = t := rfl

@[simp] theorem selectorTuple_diagonal (a s q : ℕ)
    (d : SecondRows a s q Y) (k : DiagonalLabels a s q Y) (p : Fin s) :
    selectorTuple (diagonalEmbedding a s q (d, k)) p = d := rfl

theorem reference_tuple_regular (a s q : ℕ) :
    RegularOn (referenceRows (Y := Y) a s q) selectorTuple
      (Fintype.card (ReferenceLabels a s q Y)) := by
  exact regularOn_embedded_product (referenceEmbedding a s q) selectorTuple
    (selectorTuple_reference a s q)

theorem diagonal_selected_regular (a s q : ℕ) (p : Fin s) :
    RegularOn (diagonalRows (Y := Y) a s q) (fun r => selectorTuple r p)
      (Fintype.card (DiagonalLabels a s q Y)) := by
  exact regularOn_embedded_product (diagonalEmbedding a s q)
    (fun r => selectorTuple r p) (fun d k => selectorTuple_diagonal a s q d k p)

theorem reference_diagonal_disjoint (a s q : ℕ) :
    Disjoint (referenceRows (Y := Y) a s q) (diagonalRows (Y := Y) a s q) := by
  classical
  apply Finset.disjoint_left.mpr
  intro r hr hd
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hr
  obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hd
  have h := congrArg (fun z : ProtectedColumns a s q Y => z.1.1) (hx.trans hy.symm)
  norm_num [referenceEmbedding, diagonalEmbedding] at h

theorem reference_labels_pos [Nonempty Y] (a s q : ℕ) (hq : 0 < q) :
    0 < Fintype.card (ReferenceLabels a s q Y) := by
  letI := secondRows_nonempty (Y := Y) a s q hq
  have hm : 0 < referenceMultiplicity (Y := Y) a s q :=
    WeightedDuplication.copies_pos _ _ WeightedDuplication.columnWeight_pos
      (WeightedDuplication.columnSupport_card_pos _ _) 0
  have hu := uniformCopies_pos (Y := Y) a s q hq
  simp only [ReferenceLabels, Fintype.card_prod, Fintype.card_fin]
  exact Nat.mul_pos Fintype.card_pos (Nat.mul_pos hm hu)

theorem diagonal_labels_pos [Nonempty Y] (a s q : ℕ) (hq : 0 < q) :
    0 < Fintype.card (DiagonalLabels a s q Y) := by
  letI := secondRows_nonempty (Y := Y) a s q hq
  have hm : 0 < diagonalMultiplicity (Y := Y) a s q :=
    WeightedDuplication.copies_pos _ _ WeightedDuplication.columnWeight_pos
      (WeightedDuplication.columnSupport_card_pos _ _) 1
  have hu := uniformCopies_pos (Y := Y) a s q hq
  simp only [DiagonalLabels, Fintype.card_prod, Fintype.card_fin]
  exact Nat.mul_pos hm hu

/-- One tuple set works simultaneously for every ordinary bin. -/
theorem reference_common_density [Nonempty Y] (a s q : ℕ) (hq : 0 < q)
    (A : Finset (ProtectedColumns a s q Y)) (hA : A ⊆ referenceRows a s q) :
    (A.card : ℝ) / (referenceRows (Y := Y) a s q).card ≤
      ((A.image selectorTuple).card : ℝ) / Fintype.card (ThirdColumns a s q Y) :=
  regularOn_density_transfer (reference_tuple_regular a s q)
    (reference_labels_pos a s q hq) hA

theorem diagonal_selected_density [Nonempty Y] (a s q : ℕ) (hq : 0 < q)
    (p : Fin s) (A : Finset (ProtectedColumns a s q Y))
    (hA : A ⊆ diagonalRows a s q) :
    (A.card : ℝ) / (diagonalRows (Y := Y) a s q).card ≤
      ((A.image (fun r => selectorTuple r p)).card : ℝ) /
        Fintype.card (SecondRows a s q Y) :=
  regularOn_density_transfer (diagonal_selected_regular a s q p)
    (diagonal_labels_pos a s q hq) hA

/-- Selecting a single ordinary bin preserves the retained reference density. -/
theorem reference_selected_density [Nonempty Y] (a s q : ℕ) (hq : 0 < q)
    (p : Fin s) (A : Finset (ProtectedColumns a s q Y))
    (hA : A ⊆ referenceRows a s q) :
    (A.card : ℝ) / (referenceRows (Y := Y) a s q).card ≤
      ((A.image (fun r => selectorTuple r p)).card : ℝ) /
        Fintype.card (SecondRows a s q Y) := by
  letI := secondRows_nonempty (Y := Y) a s q hq
  let c : SecondRows a s q Y := Classical.choice inferInstance
  have heval := regularOn_univ_iff_isFibreBounded.mpr (isFibreBounded_evalAt p c)
  have hproj := regularOn_density_transfer heval (evalFibre_card_pos p c)
    (Finset.subset_univ (A.image selectorTuple))
  have h := (reference_common_density a s q hq A hA).trans hproj
  simpa only [Finset.image_image, Function.comp_def, Finset.card_univ] using h

end PhysicalRows

section PhysicalColumns

variable {X Y : Type u} [Fintype X] [Fintype Y]

def fullRowMultiplicity (s L nv nb : ℕ) : ℕ :=
  WeightedDuplication.copies
    (WeightedDuplication.rowSupport (RawRows s L nv nb X) (TemplateSupport.{u} s L)
      (VertexRows nv X) (AuxiliaryRows nb X)) WeightedDuplication.rowWeight 0

def extraTemplateMultiplicity (s L nv nb : ℕ) : ℕ :=
  WeightedDuplication.copies
    (WeightedDuplication.rowSupport (RawRows s L nv nb X) (TemplateSupport.{u} s L)
      (VertexRows nv X) (AuxiliaryRows nb X)) WeightedDuplication.rowWeight 1

abbrev TemplateLabels (s L nv nb : ℕ) (X : Type u) [Fintype X] :=
  Fin (fullRowMultiplicity (X := X) s L nv nb) ⊕
    Fin (extraTemplateMultiplicity (X := X) s L nv nb)

/-- Every template column is a full-group or extra-template-group copy. -/
def templateEmbedding (s L nv nb : ℕ) (p : Fin s) :
    Fin L × TemplateLabels s L nv nb X ↪ ProtectedRows s L nv nb X where
  toFun z := match z.2 with
    | .inl k => ⟨0, (Sum.inl (p, z.1), k)⟩
    | .inr k => ⟨1, (ULift.up (p, z.1), k)⟩
  inj' := by
    rintro ⟨z, k | k⟩ ⟨z', k' | k'⟩ h
    · have hd : (Sum.inl (p, z), k) = (Sum.inl (p, z'), k') :=
        eq_of_heq (Sigma.mk.inj_iff.mp h).2
      have hz := congrArg Prod.snd (Sum.inl.inj (congrArg Prod.fst hd))
      exact Prod.ext hz (congrArg Sum.inl (congrArg Prod.snd hd))
    · have ht := congrArg Sigma.fst h
      norm_num at ht
    · have ht := congrArg Sigma.fst h
      norm_num at ht
    · have hd : (ULift.up (p, z), k) = (ULift.up (p, z'), k') :=
        eq_of_heq (Sigma.mk.inj_iff.mp h).2
      have hz := congrArg (fun r : TemplateSupport.{u} s L => r.down.2)
        (congrArg Prod.fst hd)
      exact Prod.ext hz (congrArg Sum.inr (congrArg Prod.snd hd))

def templateBin (s L nv nb : ℕ) (p : Fin s) : Finset (ProtectedRows s L nv nb X) :=
  Finset.univ.image (templateEmbedding (X := X) s L nv nb p)

/-- Forget every row-copy label; this is the raw row at which `B` is evaluated. -/
def rawRow {s L nv nb : ℕ} : ProtectedRows s L nv nb X → RawRows s L nv nb X :=
  WeightedDuplication.rowForget
    (fun r : TemplateSupport.{u} s L => Sum.inl r.down)
    (fun r => Sum.inr (Sum.inl r)) (fun r => Sum.inr (Sum.inr r))

/-- The label quotient is total; its default is never used on a template bin. -/
def templateQuotient {s L nv nb : ℕ} (hL : 0 < L)
    (y : ProtectedRows s L nv nb X) : Fin L :=
  match rawRow y with
  | .inl r => r.2
  | .inr _ => ⟨0, hL⟩

@[simp] theorem rawRow_template (s L nv nb : ℕ) (p : Fin s)
    (z : Fin L) (k : TemplateLabels s L nv nb X) :
    rawRow (templateEmbedding s L nv nb p (z, k)) = Sum.inl (p, z) := by
  cases k <;> rfl

@[simp] theorem quotient_template (s L nv nb : ℕ) (hL : 0 < L) (p : Fin s)
    (z : Fin L) (k : TemplateLabels s L nv nb X) :
    templateQuotient hL (templateEmbedding s L nv nb p (z, k)) = z := by
  simp [templateQuotient]

theorem template_regular (s L nv nb : ℕ) (hL : 0 < L) (p : Fin s) :
    RegularOn (templateBin (X := X) s L nv nb p) (templateQuotient hL)
      (Fintype.card (TemplateLabels s L nv nb X)) :=
  regularOn_embedded_product (templateEmbedding s L nv nb p)
    (templateQuotient hL) (quotient_template s L nv nb hL p)

theorem template_bin_card (s L nv nb : ℕ) (p : Fin s) :
    (templateBin (X := X) s L nv nb p).card =
      L * Fintype.card (TemplateLabels s L nv nb X) := by
  rw [templateBin, Finset.card_image_of_injective _ (templateEmbedding s L nv nb p).injective]
  simp

theorem template_labels_pos [Nonempty X] (s L nv nb : ℕ)
    (hs : 0 < s) (hL : 0 < L) (hv : 0 < nv) (hb : 0 < nb) :
    0 < Fintype.card (TemplateLabels s L nv nb X) := by
  letI : Nonempty (Fin s) := ⟨⟨0, hs⟩⟩
  letI : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  letI : Nonempty (Fin nv) := ⟨⟨0, hv⟩⟩
  letI : Nonempty (Fin nb) := ⟨⟨0, hb⟩⟩
  have hm : 0 < fullRowMultiplicity (X := X) s L nv nb :=
    WeightedDuplication.copies_pos _ _ WeightedDuplication.rowWeight_pos
      (WeightedDuplication.rowSupport_card_pos _ _ _ _) 0
  simp only [TemplateLabels, Fintype.card_sum, Fintype.card_fin]
  omega

theorem template_bins_disjoint (s L nv nb : ℕ) (p p' : Fin s) (hne : p ≠ p') :
    Disjoint (templateBin (X := X) s L nv nb p) (templateBin s L nv nb p') := by
  apply Finset.disjoint_left.mpr
  intro y hy hy'
  obtain ⟨⟨z, k⟩, _, hz⟩ := Finset.mem_image.mp hy
  obtain ⟨⟨z', k'⟩, _, hz'⟩ := Finset.mem_image.mp hy'
  have h := congrArg rawRow (hz.trans hz'.symm)
  simp only [rawRow_template, Sum.inl.injEq, Prod.mk.injEq] at h
  exact hne h.1

/-- The physical value identity required by the two-copy section argument. -/
theorem protected_template_entry (R : X → Y → Bool) (a s q L nv nb : ℕ)
    (hs : 0 < s) (hL : 0 < L) (family : SecondFamily a q L X)
    (order : ItemOrder nv nb) (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (p : Fin s) (y : ProtectedRows s L nv nb X)
    (hy : y ∈ templateBin s L nv nb p) (r : ProtectedColumns a s q Y) :
    protectedMatrix R a s q L nv nb hs family order vectors cap r y =
      secondMatrix R a s q L family (selectorTuple r p) (templateQuotient hL y) := by
  obtain ⟨⟨z, k⟩, _, rfl⟩ := Finset.mem_image.mp hy
  rw [quotient_template]
  change rawMatrix R a s q L nv nb hs family order vectors cap
    (rawRow (templateEmbedding s L nv nb p (z, k)))
    (WeightedDuplication.columnForget diagonal r) = _
  rw [rawRow_template]
  rfl

end PhysicalColumns

section JointPairs

open EthInapproximability.ParameterizedNP.WrapperProjectionCovers

/-- The actual joint projection, never the product of its marginals. -/
def jointPairs {C : Type*} [DecidableEq C] {Q : ℕ}
    (S : Finset (Fin Q → C)) (i j : Fin Q) : Finset (C × C) :=
  S.image (fun w => (w i, w j))

/-- Dense actual bin pairs have one fixed completion into the original columns. -/
theorem select_joint_pairs {C : Type*} [Fintype C] [DecidableEq C]
    {Q s m : ℕ} (S : Finset (Fin Q → C)) (i j : Fin Q)
    (bins : Fin s → Finset C) (hs : 0 < s) (hm : 0 < m)
    (hC : 0 < Fintype.card C)
    (hdisj : ∀ p p' : Fin s, p ≠ p' → Disjoint (bins p) (bins p'))
    (hcard : ∀ p : Fin s, (bins p).card = m) {rho : ℝ}
    (hdens : rho * (Fintype.card C : ℝ)^2 ≤ ((jointPairs S i j).card : ℝ)) :
    ∃ p p' : Fin s, ∃ sigma : C × C → (Fin Q → C),
      aMin rho (templateDensity bins) ≤
        (((jointPairs S i j ∩ (bins p ×ˢ bins p')).card : ℝ) / (m : ℝ)^2) ∧
      ∀ y ∈ jointPairs S i j ∩ (bins p ×ˢ bins p'),
        sigma y ∈ S ∧ sigma y i = y.1 ∧ sigma y j = y.2 := by
  classical
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hCR : (0 : ℝ) < Fintype.card C := by exact_mod_cast hC
  have hlam := templateDensity_eq_of_disjoint bins hdisj hcard
  have hmass :
      aMin rho (templateDensity bins) * ((s : ℝ) * (m : ℝ))^2 =
      (rho + (templateDensity bins)^2 - 1) * (Fintype.card C : ℝ)^2 := by
    unfold aMin
    rw [hlam]
    field_simp
  have hinter := pair_template_intersection (jointPairs S i j)
    (Finset.univ.biUnion bins) hC hdens
  have hinter' :
      aMin rho (templateDensity bins) * ((s : ℝ) * (m : ℝ))^2 ≤
      (((jointPairs S i j) ∩
        ((Finset.univ.biUnion bins) ×ˢ (Finset.univ.biUnion bins))).card : ℝ) := by
    rw [hmass]
    exact hinter
  obtain ⟨p, p', hp⟩ := exists_bin_pair_dense bins hdisj (jointPairs S i j) hs hinter'
  letI : Nonempty C := Fintype.card_pos_iff.mp hC
  let sigma : C × C → (Fin Q → C) :=
    imageSection (inferInstance : Nonempty (Fin Q → C)) S (fun w => (w i, w j))
  refine ⟨p, p', sigma, (le_div_iff₀ (sq_pos_of_pos hmR)).mpr hp, ?_⟩
  intro y hy
  have hymem : y ∈ S.image (fun w => (w i, w j)) := (Finset.mem_inter.mp hy).1
  have hsec := imageSection_apply (hA := (inferInstance : Nonempty (Fin Q → C))) hymem
  exact ⟨imageSection_mem (hA := (inferInstance : Nonempty (Fin Q → C))) hymem,
    congrArg Prod.fst hsec, congrArg Prod.snd hsec⟩

/-- Quotient density survives deletion of actual pairs, with no marginal replacement. -/
theorem surviving_pair_density {C K : Type*} [Fintype K] [DecidableEq C] [DecidableEq K]
    (Bo Bf : Finset C) (zo zf : C → K) {d m : ℕ}
    (ho : RegularOn Bo zo d) (hf : RegularOn Bf zf d) (hd : 0 < d)
    (hBo : Bo.card = m) (hBf : Bf.card = m)
    (Pstar P' : Finset (C × C)) (hstar : Pstar ⊆ Bo ×ˢ Bf) (hsub : P' ⊆ Pstar)
    {a eta : ℝ} (ha : a ≤ (Pstar.card : ℝ) / (m : ℝ)^2)
    (hloss : ((Pstar \ P').card : ℝ) / (m : ℝ)^2 ≤ eta) :
    a - eta ≤ ((P'.image (fun y => (zo y.1, zf y.2))).card : ℝ) /
      (Fintype.card K : ℝ)^2 := by
  have ht := regularOn_density_transfer (regularOn_prod ho hf)
    (Nat.mul_pos hd hd) (hsub.trans hstar)
  rw [Finset.card_product, hBo, hBf, Fintype.card_prod] at ht
  push_cast at ht
  simp only [← pow_two] at ht
  have hc := Finset.card_sdiff_add_card_eq_card hsub
  have hcR : ((Pstar \ P').card : ℝ) + P'.card = Pstar.card := by exact_mod_cast hc
  have heq : ((Pstar \ P').card : ℝ) / (m : ℝ)^2 +
      (P'.card : ℝ) / (m : ℝ)^2 = (Pstar.card : ℝ) / (m : ℝ)^2 := by
    rw [← add_div, hcR]
  linarith

/-- Every quotient pair chooses an original pair from the CURRENT surviving support. -/
theorem surviving_pair_section {C K : Type*} [Nonempty C] [DecidableEq K]
    (P' : Finset (C × C)) (zo zf : C → K) :
    ∃ pick : K × K → C × C,
      ∀ k ∈ P'.image (fun y => (zo y.1, zf y.2)),
        pick k ∈ P' ∧ (zo (pick k).1, zf (pick k).2) = k := by
  let pick := imageSection (inferInstance : Nonempty (C × C)) P'
    (fun y => (zo y.1, zf y.2))
  exact ⟨pick, fun _ hk => ⟨imageSection_mem hk, imageSection_apply hk⟩⟩

end JointPairs

section ConcreteRestriction

open Workspace.Types.CommComplexity Workspace.Types.Interlace NPCC

/-- A section on its image needs no inhabitance assumption on the source. -/
def selectedRowSection {A B : Type*} [DecidableEq B]
    (rows : Finset A) (f : A → B) (r : {b // b ∈ rows.image f}) : A :=
  (Finset.mem_image.mp r.property).choose

theorem selectedRowSection_mem {A B : Type*} [DecidableEq B]
    (rows : Finset A) (f : A → B) (r : {b // b ∈ rows.image f}) :
    selectedRowSection rows f r ∈ rows :=
  (Finset.mem_image.mp r.property).choose_spec.1

@[simp] theorem selectedRowSection_apply {A B : Type*} [DecidableEq B]
    (rows : Finset A) (f : A → B) (r : {b // b ∈ rows.image f}) :
    f (selectedRowSection rows f r) = r.val :=
  (Finset.mem_image.mp r.property).choose_spec.2

theorem selectedRowSection_injective {A B : Type*} [DecidableEq B]
    (rows : Finset A) (f : A → B) :
    Function.Injective (selectedRowSection rows f) := by
  intro r r' h
  apply Subtype.ext
  exact (selectedRowSection_apply rows f r).symm.trans
    ((congrArg f h).trans (selectedRowSection_apply rows f r'))

/-- Independent row sections are jointly injective when their outer tags differ. -/
theorem tagged_sections_injective {A B C : Type*} {Q : ℕ}
    (i j : Fin Q) (hne : i ≠ j) (fo : A → C) (ff : B → C)
    (ho : Function.Injective fo) (hf : Function.Injective ff) :
    Function.Injective (Sum.elim (fun r => (i, fo r)) (fun r => (j, ff r))) := by
  intro r r' h
  cases r with
  | inl r =>
    cases r' with
    | inl r' => exact congrArg Sum.inl (ho (congrArg Prod.snd h))
    | inr r' => exact (hne (congrArg Prod.fst h)).elim
  | inr r =>
    cases r' with
    | inl r' => exact (hne (congrArg Prod.fst h).symm).elim
    | inr r' => exact congrArg Sum.inr (hf (congrArg Prod.snd h))

/-- Fixed completion of actual pairs is injective on their support. -/
theorem joint_completion_injective {C : Type*} {Q : ℕ}
    (P : Finset (C × C)) (i j : Fin Q) (sigma : C × C → Fin Q → C)
    (hsigma : ∀ y ∈ P, sigma y i = y.1 ∧ sigma y j = y.2) :
    Set.InjOn sigma ↑P := by
  intro y hy z hz heq
  apply Prod.ext
  · exact (hsigma y hy).1.symm.trans ((congrFun heq i).trans (hsigma z hz).1)
  · exact (hsigma y hy).2.symm.trans ((congrFun heq j).trans (hsigma z hz).2)

/-- Quotient representatives followed by one fixed pair completion stay injective. -/
theorem joint_quotient_completion_injective {C K : Type*} [DecidableEq K] {Q : ℕ}
    (P : Finset (C × C)) (zo zf : C → K) (i j : Fin Q)
    (sigma : C × C → Fin Q → C)
    (hsigma : ∀ y ∈ P, sigma y i = y.1 ∧ sigma y j = y.2) :
    Function.Injective (fun k => sigma
      (selectedRowSection P (fun y => (zo y.1, zf y.2)) k)) := by
  intro k k' h
  apply selectedRowSection_injective P (fun y => (zo y.1, zf y.2))
  exact joint_completion_injective P i j sigma hsigma
    (selectedRowSection_mem _ _ k) (selectedRowSection_mem _ _ k') h

/-- Each tag uses the corresponding coordinate of the SAME indexed pair. -/
def pairedGame {B K : Type*} (M : B → K → Bool)
    (Eo Ef : Finset B) (Kpair : Finset (K × K)) :
    ({b // b ∈ Eo} ⊕ {b // b ∈ Ef}) → {k // k ∈ Kpair} → Bool
  | .inl r, k => M r.val k.val.1
  | .inr r, k => M r.val k.val.2

variable {X Y : Type u} [Fintype X] [Fintype Y]

/-- The selected two-copy matrix pulls back the actual outer interlace.
For distinct outer tags its row maps are injective by
`tagged_sections_injective`; the column map is injective by
`joint_quotient_completion_injective`. The cost bound itself needs no
distinctness assumption. Row representatives depend only on `Ao, Af, po, pf`, never
on the surviving pair set `P'`. Its column representatives are obtained by
first choosing one surviving physical pair, then applying the SAME fixed
completion `sigma` into the original retained columns. -/
theorem pairedGame_le_actual_interlace
    (R : X → Y → Bool) (a s q L nv nb Q : ℕ)
    (hs : 0 < s) (hL : 0 < L) (family : SecondFamily a q L X)
    (order : ItemOrder nv nb) (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (i j : Fin Q) (po pf : Fin s)
    (A : Finset (Fin Q × ProtectedColumns a s q Y))
    (S : Finset (Fin Q → ProtectedRows s L nv nb X))
    (Ao Af : Finset (ProtectedColumns a s q Y))
    (hAo : ∀ r ∈ Ao, (i, r) ∈ A) (hAf : ∀ r ∈ Af, (j, r) ∈ A)
    (P' : Finset (ProtectedRows s L nv nb X × ProtectedRows s L nv nb X))
    (hP : P' ⊆ templateBin s L nv nb po ×ˢ templateBin s L nv nb pf)
    (sigma : ProtectedRows s L nv nb X × ProtectedRows s L nv nb X →
      Fin Q → ProtectedRows s L nv nb X)
    (hsigma : ∀ y ∈ P', sigma y ∈ S ∧ sigma y i = y.1 ∧ sigma y j = y.2) :
    D (pairedGame (secondMatrix R a s q L family)
      (Ao.image (fun r => selectorTuple r po))
      (Af.image (fun r => selectorTuple r pf))
      (P'.image (fun y => (templateQuotient hL y.1, templateQuotient hL y.2)))) ≤
      D (subgame
        (interlaceFun (protectedMatrix R a s q L nv nb hs family order vectors cap) Q)
        A S) := by
  classical
  let ro := selectedRowSection Ao (fun r => selectorTuple r po)
  let rf := selectedRowSection Af (fun r => selectorTuple r pf)
  let kp := selectedRowSection P'
    (fun y => (templateQuotient hL y.1, templateQuotient hL y.2))
  let rowMap :
      ({b // b ∈ Ao.image (fun r => selectorTuple r po)} ⊕
       {b // b ∈ Af.image (fun r => selectorTuple r pf)}) → {r // r ∈ A} :=
    Sum.elim (fun r => ⟨(i, ro r), hAo _ (selectedRowSection_mem _ _ r)⟩)
      (fun r => ⟨(j, rf r), hAf _ (selectedRowSection_mem _ _ r)⟩)
  let colMap :
      {k // k ∈ P'.image (fun y => (templateQuotient hL y.1, templateQuotient hL y.2))} →
      {w // w ∈ S} :=
    fun k => ⟨sigma (kp k), (hsigma _ (selectedRowSection_mem _ _ k)).1⟩
  have heq : pairedGame (secondMatrix R a s q L family)
      (Ao.image (fun r => selectorTuple r po))
      (Af.image (fun r => selectorTuple r pf))
      (P'.image (fun y => (templateQuotient hL y.1, templateQuotient hL y.2))) =
      fun r k => subgame
        (interlaceFun (protectedMatrix R a s q L nv nb hs family order vectors cap) Q)
        A S (rowMap r) (colMap k) := by
    funext r k
    have hk := selectedRowSection_mem P'
      (fun y => (templateQuotient hL y.1, templateQuotient hL y.2)) k
    have hk' := selectedRowSection_apply P'
      (fun y => (templateQuotient hL y.1, templateQuotient hL y.2)) k
    have hbins := Finset.mem_product.mp (hP hk)
    rcases r with r | r
    · change secondMatrix R a s q L family r.val k.val.1 =
        protectedMatrix R a s q L nv nb hs family order vectors cap (ro r) (sigma (kp k) i)
      rw [(hsigma _ hk).2.1,
        protected_template_entry R a s q L nv nb hs hL family order vectors cap po
          (kp k).1 hbins.1 (ro r)]
      have hr := selectedRowSection_apply Ao (fun r => selectorTuple r po) r
      rw [show selectorTuple (ro r) po = r.val from hr,
        show templateQuotient hL (kp k).1 = k.val.1 from congrArg Prod.fst hk']
    · change secondMatrix R a s q L family r.val k.val.2 =
        protectedMatrix R a s q L nv nb hs family order vectors cap (rf r) (sigma (kp k) j)
      rw [(hsigma _ hk).2.2,
        protected_template_entry R a s q L nv nb hs hL family order vectors cap pf
          (kp k).2 hbins.2 (rf r)]
      have hr := selectedRowSection_apply Af (fun r => selectorTuple r pf) r
      rw [show selectorTuple (rf r) pf = r.val from hr,
        show templateQuotient hL (kp k).2 = k.val.2 from congrArg Prod.snd hk']
  rw [heq]
  exact D_mapNodes_le _ rowMap colMap

end ConcreteRestriction

end EthInapproximability.CurrentPaper.JointTransfer
