import EthInapproximability.CurrentPaper.ProtectedDefects

/-!
# Actual local copies on one physical branch

Source: locked replacement v8, `03-parameterized-construction.tex`,
`eq:paper-local-capacity`, and `A-stage4-details.tex`,
`lem:paper-protected-preparation`.

The selected template rows and active-active-inactive graph rows all belong
to one actual row domain and one branch. Every identity below uses the same
physical diagonal column, including its two copy labels. No communication
lower bound is a premise of the geometric extraction.
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.ProtectedLocalCopies

open scoped Classical BigOperators
open Construction JointTransfer ProtectedGraphItems

universe u

variable {X Y : Type u} [Fintype X] [Fintype Y]

/-- The literal representative condition, with the public item permutation
retained. It only records which additional physical copies survived. -/
def ItemRepresentatives {s L nv nb t : ℕ} (order : ItemOrder nv nb)
    (A : Finset (ProtectedRows s L nv nb X))
    (branch : ProtectedRows s L nv nb X → Fin s) (p : Fin s)
    (i : Fin (nv + nb)) : Prop :=
  (∃ v, vertexIndex order v = i ∧
    HasRowRepresentatives (vertexEmbedding s L nv nb) A branch t v p) ∨
  (∃ v, auxiliaryIndex order v = i ∧
    HasRowRepresentatives (auxiliaryEmbedding s L nv nb) A branch t v p)

/-- Convert the assignment obtained from physical deletion/pigeonhole into
the uniform item-index interface; no new witness property is supplied. -/
theorem item_representatives_of_retained {s L nv nb t : ℕ} (order : ItemOrder nv nb)
    (A : Finset (ProtectedRows s L nv nb X))
    (branch : ProtectedRows s L nv nb X → Fin s)
    (badV : Finset (Fin nv)) (badB : Finset (Fin nb)) (φ : Fin (nv + nb) → Fin s)
    (hv : ∀ i ∉ badV, HasRowRepresentatives (vertexEmbedding s L nv nb) A branch t i
      (φ (vertexIndex order i)))
    (hb : ∀ i ∉ badB, HasRowRepresentatives (auxiliaryEmbedding s L nv nb) A branch t i
      (φ (auxiliaryIndex order i))) (i : Fin (nv + nb))
    (hi : i ∈ retainedIndices order badV badB) :
    ItemRepresentatives (t := t) order A branch (φ i) i := by
  rcases Finset.mem_union.mp hi with hi | hi
  · obtain ⟨v, hv', rfl⟩ := Finset.mem_image.mp hi
    exact Or.inl ⟨v, rfl, hv v (Finset.mem_sdiff.mp hv').2⟩
  · obtain ⟨v, hv', rfl⟩ := Finset.mem_image.mp hi
    exact Or.inr ⟨v, rfl, hb v (Finset.mem_sdiff.mp hv').2⟩

/-- A retained indexed graph item has actual physical representatives with
its intended matrix values on every physical column. -/
theorem item_section (R : X → Y → Bool) (a s q L nv nb t : ℕ)
    (hs : 0 < s) (family : SecondFamily a q L X) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (A : Finset (ProtectedRows s L nv nb X))
    (branch : ProtectedRows s L nv nb X → Fin s) (p : Fin s)
    (i : Fin (nv + nb)) (hrep : ItemRepresentatives (t := t) order A branch p i) :
    ∃ Z : Finset X, t ≤ Z.card ∧
      ∃ row : Z → ProtectedRows s L nv nb X,
        (∀ x, row x ∈ A ∧ branch (row x) = p) ∧
        (∀ x c, protectedMatrix R a s q L nv nb hs family order vectors cap c (row x) =
          graphEntry R hs vectors cap i x.val
            (WeightedDuplication.columnForget diagonal c)) := by
  rcases hrep with ⟨i, rfl, Z, rep, hZ, _, hrep⟩ | ⟨i, rfl, Z, rep, hZ, _, hrep⟩
  · refine ⟨Z, hZ, (fun x => vertexEmbedding s L nv nb (i, (x.val, rep x.val))), ?_, ?_⟩
    · intro x
      exact hrep x.val x.property
    · intro x c
      exact protected_vertex_entry R a s q L nv nb hs family order vectors cap i x.val
        (rep x.val) c
  · refine ⟨Z, hZ, (fun x => auxiliaryEmbedding s L nv nb (i, (x.val, rep x.val))), ?_, ?_⟩
    · intro x
      exact hrep x.val x.property
    · intro x c
      exact protected_auxiliary_entry R a s q L nv nb hs family order vectors cap i x.val
        (rep x.val) c

/-- Retaining the original list label also retains its entire shared-input
family row. This is the ordinary (non-graph) evaluation identity. -/
theorem template_diagonal_entry (R : X → Y → Bool) (a s q L nv nb : ℕ)
    (hs : 0 < s) (hL : 0 < L) (family : SecondFamily a q L X)
    (order : ItemOrder nv nb) (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s) (p : Fin s)
    (ℓ : Fin L) (k : TemplateLabels s L nv nb X) (α : Fin q)
    (γ : FirstColumns a s Y) (d : DiagonalLabels a s q Y) :
    protectedMatrix R a s q L nv nb hs family order vectors cap
      (diagonalEmbedding a s q ((α, γ), d)) (templateEmbedding s L nv nb p (ℓ, k)) =
      firstMatrix R a s (family ℓ α) γ := by
  rw [protected_template_entry R a s q L nv nb hs hL family order vectors cap p _
    (Finset.mem_image.mpr ⟨(ℓ, k), Finset.mem_univ _, rfl⟩), quotient_template,
    selectorTuple_diagonal]
  rfl

/-- One fixed physical section of the entire retained indexed family.
Equal family strings retain their distinct list labels. -/
theorem indexed_template_section (R : X → Y → Bool) (a s q L nv nb : ℕ)
    (hs : 0 < s) (hL : 0 < L) (family : SecondFamily a q L X)
    (order : ItemOrder nv nb) (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (A : Finset (ProtectedRows s L nv nb X))
    (branch : ProtectedRows s L nv nb X → Fin s) (p bin : Fin s)
    (K : Finset (Fin L))
    (hK : ∀ ℓ ∈ K, ∃ k : TemplateLabels s L nv nb X,
      templateEmbedding s L nv nb bin (ℓ, k) ∈ A ∧
      branch (templateEmbedding s L nv nb bin (ℓ, k)) = p) :
    ∃ row : K → ProtectedRows s L nv nb X,
      (∀ ℓ, row ℓ ∈ A ∧ branch (row ℓ) = p) ∧
      (∀ ℓ (α : Fin q) (γ : FirstColumns a s Y) (d : DiagonalLabels a s q Y),
        protectedMatrix R a s q L nv nb hs family order vectors cap
          (diagonalEmbedding a s q ((α, γ), d)) (row ℓ) =
          firstMatrix R a s (family ℓ.val α) γ) := by
  choose copy hcopy using fun ℓ : K => hK ℓ.val ℓ.property
  exact ⟨(fun ℓ => templateEmbedding s L nv nb bin (ℓ.val, copy ℓ)), hcopy,
    fun ℓ α γ d => template_diagonal_entry R a s q L nv nb hs hL family order vectors cap
      bin ℓ.val (copy ℓ) α γ d⟩

/-- The distinct original `X` rows present in one block of a retained list. -/
def templateBlock {a q L : ℕ} (family : SecondFamily a q L X)
    (K : Finset (Fin L)) (α : Fin q) (b : Fin (qOne a)) : Finset X :=
  Finset.univ.filter fun x => (b, x) ∈ ProtectedDefects.coordinateSupport family K α

/-- Each distinct block row has a physical template representative on the
same branch, chosen once for all diagonal columns. -/
theorem template_block_section (R : X → Y → Bool) (a s q L nv nb : ℕ)
    (hs : 0 < s) (hL : 0 < L) (family : SecondFamily a q L X)
    (order : ItemOrder nv nb) (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (A : Finset (ProtectedRows s L nv nb X))
    (branch : ProtectedRows s L nv nb X → Fin s) (p bin : Fin s)
    (K : Finset (Fin L))
    (hK : ∀ ℓ ∈ K, ∃ k : TemplateLabels s L nv nb X,
      templateEmbedding s L nv nb bin (ℓ, k) ∈ A ∧
      branch (templateEmbedding s L nv nb bin (ℓ, k)) = p)
    (α : Fin q) (b : Fin (qOne a)) :
    ∃ row : templateBlock family K α b → ProtectedRows s L nv nb X,
      (∀ x, row x ∈ A ∧ branch (row x) = p) ∧
      (∀ x (γ : FirstColumns a s Y) (d : DiagonalLabels a s q Y),
        protectedMatrix R a s q L nv nb hs family order vectors cap
          (diagonalEmbedding a s q ((α, γ), d)) (row x) =
          R x.val (γ (firstCoordinate a s b))) := by
  have hex : ∀ x : templateBlock family K α b, ∃ ℓ ∈ K,
      family ℓ α = (b, x.val) := by
    intro x
    exact Finset.mem_image.mp ((Finset.mem_filter.mp x.property).2)
  choose label hlabel hvalue using hex
  choose copy hcopy using fun x => hK (label x) (hlabel x)
  refine ⟨(fun x => templateEmbedding s L nv nb bin (label x, copy x)), hcopy, ?_⟩
  intro x γ d
  rw [template_diagonal_entry R a s q L nv nb hs hL family order vectors cap,
    hvalue]
  rfl

/-- The two active slots and the unused inactive slot are distinct. -/
def graphSelectors {q n s : ℕ} (vectors : Fin n → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s) (α : Fin q)
    (i j : Fin n) (hij : i ≠ j) (hi : vectors i α = true) (hj : vectors j α = true) :
    Fin 3 ↪ Fin (s + 1) where
  toFun := ![Fin.castAdd 1 (activeSlot vectors cap α ⟨i, hi⟩),
    Fin.castAdd 1 (activeSlot vectors cap α ⟨j, hj⟩), Fin.last s]
  inj' := by
    have hab : activeSlot vectors cap α ⟨i, hi⟩ ≠ activeSlot vectors cap α ⟨j, hj⟩ := by
      intro h
      exact hij (congrArg Subtype.val (activeSlot_injective vectors cap α h))
    have hcast : Fin.castAdd 1 (activeSlot vectors cap α ⟨i, hi⟩) ≠
        Fin.castAdd 1 (activeSlot vectors cap α ⟨j, hj⟩) := by
      intro h
      exact hab (Fin.ext (congrArg (fun z : Fin (s + 1) => z.val) h))
    have hiLast := activeSlot_ne_inactive vectors cap α ⟨i, hi⟩
    have hjLast := activeSlot_ne_inactive vectors cap α ⟨j, hj⟩
    intro b c h
    fin_cases b <;> fin_cases c <;> simp_all

/-- Prefix selectors and the three graph selectors live in disjoint parts
of the same tuple. -/
def localSelectors (a : ℕ) {q n s : ℕ} (vectors : Fin n → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s) (α : Fin q)
    (i j : Fin n) (hij : i ≠ j) (hi : vectors i α = true) (hj : vectors j α = true) :
    Fin (qOne a + 3) ↪ Fin (firstLength a s) where
  toFun := Fin.append (firstCoordinate a s)
    (fun b => tailCoordinate a s (graphSelectors vectors cap α i j hij hi hj b))
  inj' := by
    apply Fin.append_injective_iff.mpr
    refine ⟨?_, ?_, ?_⟩
    · intro b c h
      exact Fin.ext (congrArg (fun z : Fin (firstLength a s) => z.val) h)
    · intro b c h
      apply (graphSelectors vectors cap α i j hij hi hj).injective
      apply Fin.ext
      have hv := congrArg Fin.val h
      simp only [tailCoordinate_val] at hv
      omega
    · intro b c
      exact firstCoordinate_ne_tailCoordinate a s b _

@[simp] theorem localSelectors_left (a : ℕ) {q n s : ℕ}
    (vectors : Fin n → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s) (α : Fin q)
    (i j : Fin n) (hij : i ≠ j) (hi : vectors i α = true) (hj : vectors j α = true)
    (b : Fin (qOne a)) :
    localSelectors a vectors cap α i j hij hi hj (Fin.castAdd 3 b) =
      firstCoordinate a s b := by simp [localSelectors]

@[simp] theorem localSelectors_right (a : ℕ) {q n s : ℕ}
    (vectors : Fin n → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s) (α : Fin q)
    (i j : Fin n) (hij : i ≠ j) (hi : vectors i α = true) (hj : vectors j α = true)
    (b : Fin 3) :
    localSelectors a vectors cap α i j hij hi hj (Fin.natAdd (qOne a) b) =
      tailCoordinate a s (graphSelectors vectors cap α i j hij hi hj b) := by
  simp [localSelectors]

/-- The nondeficient-coordinate statement is exactly the distinct-row
cardinality needed by local extraction. -/
theorem template_block_card_of_good {a q L t : ℕ} (family : SecondFamily a q L X)
    (K : Finset (Fin L)) (α : Fin q)
    (hgood : α ∉ ParameterizedNP.DenseSourceOwners.templateBadSet t
      (ProtectedDefects.coordinateSupport family K)) (b : Fin (qOne a)) :
    t ≤ (templateBlock family K α b).card := by
  have hcard : ((ProtectedDefects.coordinateSupport family K α).filter
      (fun r => r.1 = b)).card = (templateBlock family K α b).card := by
    apply Finset.card_bij (fun r _ => r.2)
    · intro r hr
      obtain ⟨hr, hb⟩ := Finset.mem_filter.mp hr
      simp only [templateBlock, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa only [← hb] using hr
    · intro r hr r' hr' h
      exact Prod.ext ((Finset.mem_filter.mp hr).2.trans (Finset.mem_filter.mp hr').2.symm) h
    · intro x hx
      exact ⟨(b, x), Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).2, rfl⟩, rfl⟩
  have hn : ¬ ((ProtectedDefects.coordinateSupport family K α).filter
      (fun r => r.1 = b)).card < t := by
    intro h
    exact hgood (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨b, h⟩⟩)
  omega

/-- Package separate actual row sections as one literal interlace row set.
The section is fixed before columns, so one protocol pulls back simultaneously. -/
theorem assemble_rows {W C : Type*} [Fintype W] {k t : ℕ}
    (F : C → W → Bool) (base : X → Y → Bool) (A : Finset W)
    (branch : W → Fin s) (p : Fin s) (selector : Fin k → C → Y)
    (sections : ∀ j : Fin k, ∃ Z : Finset X, t ≤ Z.card ∧
      ∃ row : Z → W, (∀ x, row x ∈ A ∧ branch (row x) = p) ∧
      (∀ x c, F c (row x) = base x.val (selector j c))) :
    ∃ E : Finset (Fin k × X), NPCC.IsEquipartitionedGE E Finset.univ t ∧
      ∃ row : E → W, (∀ r, row r ∈ A ∧ branch (row r) = p) ∧
        (∀ r c, F c (row r) = base r.val.2 (selector r.val.1 c)) := by
  choose Z hZ row hrow hvalue using sections
  let E : Finset (Fin k × X) := Finset.univ.filter fun r => r.2 ∈ Z r.1
  have hcount : ∀ j : Fin k, (E.filter (fun r => r.1 = j)).card = (Z j).card := by
    intro j
    apply Finset.card_bij (fun r _ => r.2)
    · intro r hr
      obtain ⟨hr, hj⟩ := Finset.mem_filter.mp hr
      simpa only [← hj] using (Finset.mem_filter.mp hr).2
    · intro r hr r' hr' h
      exact Prod.ext ((Finset.mem_filter.mp hr).2.trans (Finset.mem_filter.mp hr').2.symm) h
    · intro x hx
      exact ⟨(j, x), by simp [E, hx], rfl⟩
  refine ⟨E, ?_, (fun r => row r.val.1 ⟨r.val.2, (Finset.mem_filter.mp r.property).2⟩), ?_, ?_⟩
  · intro j _
    rw [hcount]
    exact hZ j
  · intro r
    exact hrow _ _
  · intro r c
    exact hvalue _ _ _

/-- The three graph sections have distinct tuple selectors and share both
the real prefix branch and every physical diagonal-column label. -/
theorem graph_sections (R : X → Y → Bool) (a s q L nv nb t : ℕ)
    (hs : 0 < s) (family : SecondFamily a q L X) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (A : Finset (ProtectedRows s L nv nb X))
    (branch : ProtectedRows s L nv nb X → Fin s) (p : Fin s) (α : Fin q)
    (i j k : Fin (nv + nb)) (hij : i ≠ j)
    (hi : vectors i α = true) (hj : vectors j α = true) (hk : vectors k α = false)
    (hri : ItemRepresentatives (t := t) order A branch p i)
    (hrj : ItemRepresentatives (t := t) order A branch p j)
    (hrk : ItemRepresentatives (t := t) order A branch p k) :
    ∀ b : Fin 3, ∃ Z : Finset X, t ≤ Z.card ∧
      ∃ row : Z → ProtectedRows s L nv nb X,
        (∀ x, row x ∈ A ∧ branch (row x) = p) ∧
        (∀ x (γ : FirstColumns a s Y) (d : DiagonalLabels a s q Y),
          protectedMatrix R a s q L nv nb hs family order vectors cap
            (diagonalEmbedding a s q ((α, γ), d)) (row x) =
          R x.val (γ (tailCoordinate a s (graphSelectors vectors cap α i j hij hi hj b)))) := by
  obtain ⟨Zi, hZi, ri, hri', hei⟩ :=
    item_section R a s q L nv nb t hs family order vectors cap A branch p i hri
  obtain ⟨Zj, hZj, rj, hrj', hej⟩ :=
    item_section R a s q L nv nb t hs family order vectors cap A branch p j hrj
  obtain ⟨Zk, hZk, rk, hrk', hek⟩ :=
    item_section R a s q L nv nb t hs family order vectors cap A branch p k hrk
  intro b
  fin_cases b
  · refine ⟨Zi, hZi, ri, hri', ?_⟩
    intro x γ d
    rw [hei]
    change graphEntry R hs vectors cap i x.val (diagonal (α, γ)) = _
    simpa [graphSelectors] using graphEntry_diagonal_active R hs vectors cap α γ i hi x.val
  · refine ⟨Zj, hZj, rj, hrj', ?_⟩
    intro x γ d
    rw [hej]
    change graphEntry R hs vectors cap j x.val (diagonal (α, γ)) = _
    simpa [graphSelectors] using graphEntry_diagonal_active R hs vectors cap α γ j hj x.val
  · refine ⟨Zk, hZk, rk, hrk', ?_⟩
    intro x γ d
    rw [hek]
    change graphEntry R hs vectors cap k x.val (diagonal (α, γ)) = _
    simpa [graphSelectors] using graphEntry_diagonal_inactive R hs vectors cap α γ k hk x.val

/-- A nondeficient template coordinate and an actual graph witness contain
`qOne a + 3` ordinary copies of the base matrix on one physical branch.
No protocol or local lower bound is assumed. The `row` map is fixed once,
and works on every common diagonal tuple and on every copy of that tuple. -/
theorem physical_local_copies (R : X → Y → Bool) (a s q L nv nb t : ℕ)
    (hs : 0 < s) (hL : 0 < L) (family : SecondFamily a q L X)
    (order : ItemOrder nv nb) (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (A : Finset (ProtectedRows s L nv nb X))
    (branch : ProtectedRows s L nv nb X → Fin s) (p bin : Fin s)
    (K : Finset (Fin L))
    (hK : ∀ ℓ ∈ K, ∃ k : TemplateLabels s L nv nb X,
      templateEmbedding s L nv nb bin (ℓ, k) ∈ A ∧
      branch (templateEmbedding s L nv nb bin (ℓ, k)) = p)
    (α : Fin q)
    (hgood : α ∉ ParameterizedNP.DenseSourceOwners.templateBadSet t
      (ProtectedDefects.coordinateSupport family K))
    (i j k : Fin (nv + nb)) (hij : i ≠ j)
    (hi : vectors i α = true) (hj : vectors j α = true) (hk : vectors k α = false)
    (hri : ItemRepresentatives (t := t) order A branch p i)
    (hrj : ItemRepresentatives (t := t) order A branch p j)
    (hrk : ItemRepresentatives (t := t) order A branch p k) :
    ∃ E : Finset (Fin (qOne a + 3) × X), NPCC.IsEquipartitionedGE E Finset.univ t ∧
      ∃ row : E → ProtectedRows s L nv nb X,
        (∀ r, row r ∈ A ∧ branch (row r) = p) ∧
        (∀ r (γ : FirstColumns a s Y) (d : DiagonalLabels a s q Y),
          protectedMatrix R a s q L nv nb hs family order vectors cap
            (diagonalEmbedding a s q ((α, γ), d)) (row r) =
          R r.val.2 (γ (localSelectors a vectors cap α i j hij hi hj r.val.1))) := by
  let e := localSelectors a vectors cap α i j hij hi hj
  let F : (FirstColumns a s Y × DiagonalLabels a s q Y) →
      ProtectedRows s L nv nb X → Bool := fun c r =>
    protectedMatrix R a s q L nv nb hs family order vectors cap
      (diagonalEmbedding a s q ((α, c.1), c.2)) r
  have sections : ∀ b : Fin (qOne a + 3), ∃ Z : Finset X, t ≤ Z.card ∧
      ∃ row : Z → ProtectedRows s L nv nb X,
        (∀ x, row x ∈ A ∧ branch (row x) = p) ∧
        (∀ x (c : FirstColumns a s Y × DiagonalLabels a s q Y),
          F c (row x) = R x.val (c.1 (e b))) := by
    intro b
    refine Fin.addCases ?_ ?_ b
    · intro b
      obtain ⟨row, hrow, hval⟩ := template_block_section R a s q L nv nb hs hL
        family order vectors cap A branch p bin K hK α b
      refine ⟨templateBlock family K α b, template_block_card_of_good family K α hgood b,
        row, hrow, ?_⟩
      intro x c
      simpa only [F, e, localSelectors_left] using hval x c.1 c.2
    · intro b
      obtain ⟨Z, hZ, row, hrow, hval⟩ := graph_sections R a s q L nv nb t hs
        family order vectors cap A branch p α i j k hij hi hj hk hri hrj hrk b
      refine ⟨Z, hZ, row, hrow, ?_⟩
      intro x c
      simpa only [F, e, localSelectors_right] using hval x c.1 c.2
  obtain ⟨E, hE, row, hrow, hval⟩ := assemble_rows F R A branch p
    (fun b c => c.1 (e b)) sections
  exact ⟨E, hE, row, hrow, fun r γ d => hval r (γ, d)⟩

end EthInapproximability.CurrentPaper.ProtectedLocalCopies
