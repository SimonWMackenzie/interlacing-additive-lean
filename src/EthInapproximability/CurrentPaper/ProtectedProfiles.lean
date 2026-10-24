import EthInapproximability.CurrentPaper.JointTransfer
import EthInapproximability.CurrentPaper.IndexedProjection

/-!
# Reference restrictions of the literal protected matrix

Source: locked replacement v8, `A-stage4-details.tex`,
`lem:paper-reference-extraction` in `thm:paper-protected-stage4`.

The reference rows retain the whole selector tuple. All physical template
columns, including both kinds of duplicate labels, are quotiented together.
Selecting blocks then produces one actual classical restriction; the row and
column representatives are chosen from the original retained sets.

Lower bounds for the second matrix remain explicit inputs to this extraction.
They are not a substitute for the separate dense protected-matrix theorem.
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.ProtectedProfiles

open scoped BigOperators Classical
open NPCC Workspace.Types.CommComplexity Workspace.Types.Interlace
open Construction JointTransfer
open EthInapproximability.ParameterizedNP.TerminalStateRealization
open EthInapproximability.ParameterizedNP.InheritedContracts

universe u
variable {X Y : Type u} [Fintype X] [Fintype Y]

/-- All copies of template columns, with the bin retained in the quotient. -/
def templateEmbeddingAll (s L nv nb : ℕ) :
    (ThirdRows s L × TemplateLabels s L nv nb X) ↪ ProtectedRows s L nv nb X where
  toFun z := templateEmbedding s L nv nb z.1.1 (z.1.2, z.2)
  inj' := by
    rintro ⟨⟨i, z⟩, k⟩ ⟨⟨i', z'⟩, k'⟩ h
    have hi : i = i' := by
      have hh := congrArg rawRow h
      have hh' : i = i' ∧ z = z' := by
        simpa only [rawRow_template, Sum.inl.injEq, Prod.mk.injEq] using hh
      exact hh'.1
    subst i'
    have hk := (templateEmbedding (X := X) s L nv nb i).injective h
    exact congrArg (fun zk => ((i, zk.1), zk.2)) hk

def templateRows (s L nv nb : ℕ) : Finset (ProtectedRows s L nv nb X) :=
  Finset.univ.image (templateEmbeddingAll s L nv nb)

/-- A total quotient; its default is never used on the template set. -/
def templatePair (s L nv nb : ℕ) (hs : 0 < s) (hL : 0 < L)
    (r : ProtectedRows s L nv nb X) : ThirdRows s L :=
  match rawRow r with
  | .inl z => z
  | .inr _ => (⟨0, hs⟩, ⟨0, hL⟩)

@[simp] theorem templatePair_embedding (s L nv nb : ℕ) (hs : 0 < s) (hL : 0 < L)
    (z : ThirdRows s L) (k : TemplateLabels s L nv nb X) :
    templatePair s L nv nb hs hL (templateEmbeddingAll s L nv nb (z, k)) = z := by
  simp [templatePair, templateEmbeddingAll]

theorem template_regular_all (s L nv nb : ℕ) (hs : 0 < s) (hL : 0 < L) :
    RegularOn (templateRows (X := X) s L nv nb) (templatePair s L nv nb hs hL)
      (Fintype.card (TemplateLabels s L nv nb X)) :=
  regularOn_embedded_product (templateEmbeddingAll s L nv nb)
    (templatePair s L nv nb hs hL) (templatePair_embedding s L nv nb hs hL)

theorem template_rows_card (s L nv nb : ℕ) :
    (templateRows (X := X) s L nv nb).card =
      s * L * Fintype.card (TemplateLabels s L nv nb X) := by
  rw [templateRows, Finset.card_image_of_injective _
    (templateEmbeddingAll s L nv nb).injective]
  simp [ThirdRows]

theorem template_common_density [Nonempty X] (s L nv nb : ℕ)
    (hs : 0 < s) (hL : 0 < L) (hv : 0 < nv) (hb : 0 < nb)
    (B : Finset (ProtectedRows s L nv nb X)) (hB : B ⊆ templateRows s L nv nb) :
    (B.card : ℝ) / (templateRows (X := X) s L nv nb).card ≤
      ((B.image (templatePair s L nv nb hs hL)).card : ℝ) / (s * L) := by
  have h := regularOn_density_transfer (template_regular_all s L nv nb hs hL)
    (template_labels_pos s L nv nb hs hL hv hb) hB
  simpa only [ThirdRows, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] using h

theorem template_entry_all (R : X → Y → Bool) (a s q L nv nb : ℕ)
    (hs : 0 < s) (hL : 0 < L) (family : SecondFamily a q L X)
    (order : ItemOrder nv nb) (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (r : ProtectedColumns a s q Y) (c : ProtectedRows s L nv nb X)
    (hc : c ∈ templateRows s L nv nb) :
    protectedMatrix R a s q L nv nb hs family order vectors cap r c =
      thirdMatrix R a s q L family (templatePair s L nv nb hs hL c) (selectorTuple r) := by
  obtain ⟨⟨z, k⟩, _, rfl⟩ := Finset.mem_image.mp hc
  rw [templatePair_embedding]
  change protectedMatrix R a s q L nv nb hs family order vectors cap r
    (templateEmbedding s L nv nb z.1 (z.2, k)) = _
  rw [protected_template_entry R a s q L nv nb hs hL family order vectors cap z.1 _
    (Finset.mem_image.mpr ⟨(z.2, k), Finset.mem_univ _, rfl⟩), quotient_template]
  rfl

/-- The projected classical game is a restriction of the transpose of the
same physical matrix. Representatives are joint original inputs, not
independent choices for each bin. -/
theorem physical_template_pullback (R : X → Y → Bool) (a s q L nv nb : ℕ)
    (hs : 0 < s) (hL : 0 < L) (family : SecondFamily a q L X)
    (order : ItemOrder nv nb) (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (A : Finset (ProtectedColumns a s q Y)) (B : Finset (ProtectedRows s L nv nb X))
    (hB : B ⊆ templateRows s L nv nb) :
    D (subgame (thirdMatrix R a s q L family)
      (B.image (templatePair s L nv nb hs hL)) (A.image selectorTuple)) ≤
      D (subgame (protectedMatrix R a s q L nv nb hs family order vectors cap) A B) := by
  let f := protectedMatrix R a s q L nv nb hs family order vectors cap
  let rows := B.image (templatePair s L nv nb hs hL)
  let cols := A.image selectorTuple
  let rowMap : rows → B := fun z =>
    ⟨(Finset.mem_image.mp z.property).choose,
      (Finset.mem_image.mp z.property).choose_spec.1⟩
  let colMap : cols → A := fun z =>
    ⟨(Finset.mem_image.mp z.property).choose,
      (Finset.mem_image.mp z.property).choose_spec.1⟩
  have hrow (z : rows) : templatePair s L nv nb hs hL (rowMap z).val = z.val :=
    (Finset.mem_image.mp z.property).choose_spec.2
  have hcol (z : cols) : selectorTuple (colMap z).val = z.val :=
    (Finset.mem_image.mp z.property).choose_spec.2
  have heq : subgame (thirdMatrix R a s q L family) rows cols =
      fun r c => subgame (fun c r => f r c) B A (rowMap r) (colMap c) := by
    funext r c
    change _ = f (colMap c).val (rowMap r).val
    rw [show f (colMap c).val (rowMap r).val = _ from
      template_entry_all R a s q L nv nb hs hL family order vectors cap _ _
        (hB (rowMap r).property), hrow, hcol]
    rfl
  change D (subgame (thirdMatrix R a s q L family) rows cols) ≤ _
  rw [heq]
  have hcost := D_mapNodes_le (subgame (fun c r => f r c) B A) rowMap colMap
  have ht : D (subgame (fun c r => f r c) B A) = D (subgame f A B) :=
    comp_transpose (subgame f A B)
  exact hcost.trans_eq ht

/-- A subset occupying fraction `lambda` of the full carrier retains at
least `(beta+lambda-1)/lambda` after a global `beta` restriction. -/
theorem retained_group_density {C : Type*} [Fintype C] [DecidableEq C]
    (T B : Finset C) (hT : 0 < T.card) {β : ℝ}
    (hB : β * Fintype.card C ≤ B.card) :
    (β + (T.card : ℝ) / Fintype.card C - 1) /
        ((T.card : ℝ) / Fintype.card C) ≤
      ((B ∩ T).card : ℝ) / T.card := by
  have ht : (0 : ℝ) < T.card := by exact_mod_cast hT
  have hcard : T.card ≤ Fintype.card C := Finset.card_le_univ T
  have hn : (0 : ℝ) < Fintype.card C := lt_of_lt_of_le ht (by exact_mod_cast hcard)
  have hun : (B ∪ T).card ≤ Fintype.card C := Finset.card_le_univ (B ∪ T)
  have hi := Finset.card_union_add_card_inter B T
  have hiR : ((B ∪ T).card : ℝ) + (B ∩ T).card = B.card + T.card := by
    exact_mod_cast hi
  have hunR : ((B ∪ T).card : ℝ) ≤ Fintype.card C := by exact_mod_cast hun
  apply (div_le_div_iff₀ (div_pos ht hn) ht).2
  field_simp
  nlinarith

/-- A selected set of dense blocks and common whole tuples gives the
corresponding classical family lower bound on the original interlace. -/
theorem classical_projection_lower_bound {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B → Bool) {s p : ℕ} {x ρ : ℝ}
    (hp : 0 < p) (Q : Finset (Fin s)) (hQ : Q.card = p)
    (E : Finset (Fin s × A)) (T : Finset (Fin s → B))
    (hrows : IsEquipartitionedGE E Q ⌈(Fintype.card A : ℝ) * x⌉₊)
    (hcols : ρ * (Fintype.card B : ℝ) ^ s ≤ T.card) :
    Dfamily (interlaceFun f p) (bracketGE A B p x ρ) ≤
      D (subgame (interlaceFun f s) E T) := by
  let e : Fin p ≃ Q := Fintype.equivOfCardEq (by simpa using hQ.symm)
  have hceil : ⌈(Fintype.card B : ℝ) ^ s * ρ⌉₊ ≤ T.card := by
    rw [Nat.ceil_le]
    simpa only [mul_comm] using hcols
  obtain ⟨RC, hRC, hr, hc⟩ := coordProjection s p hp Q e E T _ x ρ hrows hceil (le_refl _)
  let rowMap : RC.1 → E := fun r => ⟨((e r.val.1).val, r.val.2), hr r.val r.property⟩
  let colMap : RC.2 → T := fun c =>
    ⟨(hc c.val c.property).choose, (hc c.val c.property).choose_spec.1⟩
  have heq : subgame (interlaceFun f p) RC.1 RC.2 =
      fun r c => subgame (interlaceFun f s) E T (rowMap r) (colMap c) := by
    funext r c
    change f r.val.2 (c.val r.val.1) = _
    rw [(hc c.val c.property).choose_spec.2 r.val.1]
    rfl
  have hlow : Dfamily (interlaceFun f p) (bracketGE A B p x ρ) ≤
      D (subgame (interlaceFun f p) RC.1 RC.2) := Nat.sInf_le ⟨RC, hRC, rfl⟩
  rw [heq] at hlow
  exact hlow.trans (D_mapNodes_le _ rowMap colMap)

/-- Physical reference restriction bound. The scalar selection gate and the
second-matrix classical bound are the exact remaining inputs of the source
reference-extraction argument. No lower bound for the protected matrix is
assumed. -/
theorem reference_restriction_bound [Nonempty X] [Nonempty Y]
    (R : X → Y → Bool) (a s q L nv nb : ℕ)
    (hs : 0 < s) (hq : 0 < q) (hL : 0 < L) (hv : 0 < nv) (hb : 0 < nb)
    (family : SecondFamily a q L X) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    {p H : ℕ} {x ρ β : ℝ} (hp : 0 < p) (hx : 0 < x) (hx1 : x < 1)
    (hgate : p ≤ ⌈(s : ℝ) *
      (((β + (templateRows (X := X) s L nv nb).card /
          (Fintype.card (ProtectedRows s L nv nb X) : ℝ) - 1) /
         ((templateRows (X := X) s L nv nb).card /
          (Fintype.card (ProtectedRows s L nv nb X) : ℝ))) - x) / (1 - x)⌉₊)
    (hhard : H ≤ Dfamily (interlaceFun (fun j z => secondMatrix R a s q L family z j) p)
      (bracketGE (Fin L) (SecondRows a s q Y) p x ρ))
    (A : Finset (ProtectedColumns a s q Y)) (B : Finset (ProtectedRows s L nv nb X))
    (hA : A ⊆ referenceRows a s q)
    (hAdensity : ρ ≤ (A.card : ℝ) / (referenceRows (Y := Y) a s q).card)
    (hBdensity : β * Fintype.card (ProtectedRows s L nv nb X) ≤ B.card) :
    H ≤ D (subgame (protectedMatrix R a s q L nv nb hs family order vectors cap) A B) := by
  let BT := B ∩ templateRows (X := X) s L nv nb
  let E := BT.image (templatePair s L nv nb hs hL)
  let T := A.image selectorTuple
  have hBT : BT ⊆ templateRows s L nv nb := Finset.inter_subset_right
  have hmass : 0 < (templateRows (X := X) s L nv nb).card := by
    rw [template_rows_card]
    exact Nat.mul_pos (Nat.mul_pos hs hL) (template_labels_pos s L nv nb hs hL hv hb)
  have hBgroup := retained_group_density (templateRows (X := X) s L nv nb) B hmass hBdensity
  have hEquot := template_common_density s L nv nb hs hL hv hb BT hBT
  have hcount : p ≤ ⌈(s : ℝ) * ((E.card : ℝ) / ((s : ℝ) * (L : ℝ)) - x) / (1 - x)⌉₊ := by
    apply hgate.trans
    apply Nat.ceil_mono
    apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr hx1.le)
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg s)
    exact sub_le_sub_right (hBgroup.trans hEquot) x
  have hcount' : p ≤ ⌈(s : ℝ) *
      ((E.card : ℝ) / ((s : ℝ) * (Fintype.card (Fin L) : ℝ)) - x) / (1 - x)⌉₊ := by
    simpa only [Fintype.card_fin] using hcount
  obtain ⟨Q, hQ, hrows⟩ := IndexedProjection.enough_good_blocks
    (X := Fin L) (q := s) (v := p) (R := E) (x := x) hx hx1 hp hcount'
  have hT := hAdensity.trans (reference_common_density a s q hq A hA)
  letI := secondRows_nonempty (Y := Y) a s q hq
  have hcol : ρ * (Fintype.card (SecondRows a s q Y) : ℝ) ^ s ≤ T.card := by
    have hn : (0 : ℝ) < Fintype.card (ThirdColumns a s q Y) := by exact_mod_cast Fintype.card_pos
    have he := (le_div_iff₀ hn).mp hT
    simpa only [ThirdColumns, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using he
  have hclass := classical_projection_lower_bound
    (A := Fin L) (B := SecondRows a s q Y) (s := s) (p := p) (x := x) (ρ := ρ)
    (fun j z => secondMatrix R a s q L family z j) hp Q hQ E T hrows hcol
  have hphysical := physical_template_pullback R a s q L nv nb hs hL family order vectors cap A BT hBT
  have hsmall : D (subgame (protectedMatrix R a s q L nv nb hs family order vectors cap) A BT) ≤
      D (subgame (protectedMatrix R a s q L nv nb hs family order vectors cap) A B) := by
    let colMap : BT → B := fun c => ⟨c.val, (Finset.mem_inter.mp c.property).1⟩
    exact D_mapNodes_le
      (subgame (protectedMatrix R a s q L nv nb hs family order vectors cap) A B)
      (id : A → A) colMap
  exact hhard.trans (hclass.trans (hphysical.trans hsmall))

end EthInapproximability.CurrentPaper.ProtectedProfiles
