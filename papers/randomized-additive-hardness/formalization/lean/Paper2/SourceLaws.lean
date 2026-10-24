import Paper2.SourceMatrix
import Paper2.RationalTupleTransport

/-!
# Positive rational laws on the actual source carriers

Frozen v12 Section 4, the protected input laws and `eq:mixture`.
The product and tagged-mixture distributions below are constructed from
the original positive rational base laws. Their normalization, tag masses,
and bin marginals are proved, not supplied as distributional contracts.
-/

namespace Paper2

open scoped BigOperators

namespace PositiveRationalLaw

variable {A B : Type*} [Fintype A] [Fintype B]

noncomputable def uniform (A : Type*) [Fintype A] [Nonempty A] :
    PositiveRationalLaw A where
  weight _ := (Fintype.card A : ℚ)⁻¹
  positive _ := inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
  total := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_pos.ne')

noncomputable def prod (μ : PositiveRationalLaw A) (ν : PositiveRationalLaw B) :
    PositiveRationalLaw (A × B) where
  weight a := μ.weight a.1 * ν.weight a.2
  positive a := mul_pos (μ.positive _) (ν.positive _)
  total := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, ν.total, mul_one, μ.total]

noncomputable def iid (μ : PositiveRationalLaw A) (n : ℕ) :
    PositiveRationalLaw (Fin n → A) where
  weight a := ∏ i, μ.weight (a i)
  positive a := Finset.prod_pos (fun i _ => μ.positive _)
  total := by
    classical
    rw [← Fintype.prod_sum]
    simp only [μ.total, Finset.prod_const_one]

theorem toFiniteLaw_prod (μ : PositiveRationalLaw A) (ν : PositiveRationalLaw B) :
    (μ.prod ν).toFiniteLaw = μ.toFiniteLaw.prod ν.toFiniteLaw := by
  have hh : (μ.prod ν).toFiniteLaw.weight = (μ.toFiniteLaw.prod ν.toFiniteLaw).weight := by
    funext a
    simp [toFiniteLaw, prod, FiniteLaw.prod]
  cases h₁ : (μ.prod ν).toFiniteLaw
  cases h₂ : μ.toFiniteLaw.prod ν.toFiniteLaw
  simp only [h₁, h₂] at hh
  cases hh
  rfl

theorem toFiniteLaw_iid (μ : PositiveRationalLaw A) (n : ℕ) :
    (μ.iid n).toFiniteLaw = μ.toFiniteLaw.iid n := by
  have hh : (μ.iid n).toFiniteLaw.weight = (μ.toFiniteLaw.iid n).weight := by
    funext a
    simp [toFiniteLaw, iid, FiniteLaw.iid]
  cases h₁ : (μ.iid n).toFiniteLaw
  cases h₂ : μ.toFiniteLaw.iid n
  simp only [h₁, h₂] at hh
  cases hh
  rfl

end PositiveRationalLaw

namespace FiniteLaw

variable {A B : Type*} [Fintype A] [Fintype B]

/-- A specified coordinate of an independent tuple has exactly the base law. -/
theorem iid_prob_coordinate (μ : FiniteLaw A) (n : ℕ) (i : Fin n) (E : A → Prop) :
    (μ.iid n).prob (fun x => E (x i)) = μ.prob E := by
  classical
  have he : (fun x : Fin n → A => E (x i)) =
      (fun x => ∀ j, if j = i then E (x j) else True) := by
    funext x
    apply propext
    simp
  rw [he, iid_prob_coordinatewise μ n (fun j a => if j = i then E a else True)]
  have hcoord (j : Fin n) :
      μ.prob (fun a => if j = i then E a else True) =
        if j = i then μ.prob E else 1 := by
    by_cases h : j = i <;> simp [h]
  simp_rw [hcoord]
  simp

theorem prod_prob_snd (μ : FiniteLaw A) (ν : FiniteLaw B) (E : B → Prop) :
    (μ.prod ν).prob (fun x => E x.2) = ν.prob E := by
  rw [prod_prob μ ν (fun _ b => E b), ← Finset.sum_mul, μ.total, one_mul]

theorem prod_prob_fixed_fst (μ : FiniteLaw A) (ν : FiniteLaw B)
    (a : A) (E : B → Prop) :
    (μ.prod ν).prob (fun x => x.1 = a ∧ E x.2) = μ.weight a * ν.prob E := by
  classical
  rw [prod_prob μ ν (fun x y => x = a ∧ E y)]
  have he (x : A) : ν.prob (fun y => x = a ∧ E y) =
      if x = a then ν.prob E else 0 := by
    by_cases hx : x = a <;> simp [hx]
  simp_rw [he, mul_ite, mul_zero]
  simp

end FiniteLaw

namespace SourceLaws

open SourceMatrix

variable {Y : Type*} [Fintype Y]

/-- The complete outer-coordinate and word law. -/
noncomputable def outerLaw (ν : PositiveRationalLaw Y) (q₁ q₂ s : ℕ)
    [NeZero q₂] : PositiveRationalLaw (OuterColumn q₁ q₂ s Y) :=
  (PositiveRationalLaw.uniform (Fin q₂)).prod (ν.iid (q₁ + s + 1))

noncomputable def rawLaw (ν : PositiveRationalLaw Y) (q₁ q₂ s : ℕ)
    [NeZero q₂] : PositiveRationalLaw (RawColumn q₁ q₂ s Y) :=
  (ν.iid (s + 1)).prod ((outerLaw ν q₁ q₂ s).iid s)

noncomputable def fixedTailLaw (ν : PositiveRationalLaw Y) (q₁ q₂ s : ℕ)
    [NeZero q₂] : PositiveRationalLaw (Fin s → OuterColumn q₁ q₂ s Y) :=
  (outerLaw ν q₁ q₂ s).iid s

/-- The tagged source carrier is a disjoint sum, even when the raw
columns underlying different tags happen to be equal. -/
def taggedEquiv (q₁ q₂ s : ℕ) (Y : Type*) :
    TaggedColumn q₁ q₂ s Y ≃
      RawColumn q₁ q₂ s Y ⊕ ((Fin s → OuterColumn q₁ q₂ s Y) ⊕ OuterColumn q₁ q₂ s Y) where
  toFun
    | .unrestricted Z => .inl Z
    | .fixedTail js => .inr (.inl js)
    | .diagonal j => .inr (.inr j)
  invFun
    | .inl Z => .unrestricted Z
    | .inr (.inl js) => .fixedTail js
    | .inr (.inr j) => .diagonal j
  left_inv a := by cases a <;> rfl
  right_inv a := by rcases a with a | (a | a) <;> rfl

theorem sum_tagged {α : Type*} [AddCommMonoid α]
    (q₁ q₂ s : ℕ) (f : TaggedColumn q₁ q₂ s Y → α) :
    (∑ Z, f Z) = (∑ Z, f (.unrestricted Z)) +
      (∑ js, f (.fixedTail js)) + ∑ j, f (.diagonal j) := by
  rw [← (taggedEquiv q₁ q₂ s Y).symm.sum_comp]
  simp only [Fintype.sum_sum_type, taggedEquiv, Equiv.coe_fn_symm_mk]
  exact (add_assoc _ _ _).symm

/-- The manuscript's actual protected mixture, with every input carrying
a positive rational probability. -/
noncomputable def taggedLaw (ν : PositiveRationalLaw Y) (q₁ q₂ s : ℕ)
    [NeZero q₂] : PositiveRationalLaw (TaggedColumn q₁ q₂ s Y) where
  weight
    | .unrestricted Z => (127 / 128) * (rawLaw ν q₁ q₂ s).weight Z
    | .fixedTail js => (1 / 256) * (fixedTailLaw ν q₁ q₂ s).weight js
    | .diagonal j => (1 / 256) * (outerLaw ν q₁ q₂ s).weight j
  positive Z := by
    cases Z with
    | unrestricted Z => exact mul_pos (by norm_num) ((rawLaw ν q₁ q₂ s).positive Z)
    | fixedTail js => exact mul_pos (by norm_num) ((fixedTailLaw ν q₁ q₂ s).positive js)
    | diagonal j => exact mul_pos (by norm_num) ((outerLaw ν q₁ q₂ s).positive j)
  total := by
    rw [sum_tagged]
    simp only [← Finset.mul_sum, PositiveRationalLaw.total, mul_one]
    norm_num

/-- Exact event probabilities, retaining each conditional family's own
carrier instead of identifying coincident raw labels. -/
theorem tagged_prob (ν : PositiveRationalLaw Y) (q₁ q₂ s : ℕ) [NeZero q₂]
    (E : TaggedColumn q₁ q₂ s Y → Prop) :
    (taggedLaw ν q₁ q₂ s).toFiniteLaw.prob E =
      (127 / 128 : ℝ) * (rawLaw ν q₁ q₂ s).toFiniteLaw.prob (fun Z => E (.unrestricted Z)) +
      (1 / 256 : ℝ) * (fixedTailLaw ν q₁ q₂ s).toFiniteLaw.prob (fun js => E (.fixedTail js)) +
      (1 / 256 : ℝ) * (outerLaw ν q₁ q₂ s).toFiniteLaw.prob (fun j => E (.diagonal j)) := by
  classical
  unfold FiniteLaw.prob
  rw [sum_tagged]
  simp only [PositiveRationalLaw.toFiniteLaw, taggedLaw, Rat.cast_mul,
    Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Finset.mul_sum]
  simp only [mul_ite, mul_zero]

/-- The map used by a template bin on the actual tagged source columns. -/
def binProjection {q₁ q₂ s : ℕ} (ξ₀ : Tail s Y) (p : Fin s)
    (Z : TaggedColumn q₁ q₂ s Y) : OuterColumn q₁ q₂ s Y :=
  (forgetTag ξ₀ Z).2 p

theorem fixedTail_bin_marginal (ν : PositiveRationalLaw Y) (q₁ q₂ s : ℕ)
    [NeZero q₂] (p : Fin s) (E : OuterColumn q₁ q₂ s Y → Prop) :
    (fixedTailLaw ν q₁ q₂ s).toFiniteLaw.prob (fun js => E (js p)) =
      (outerLaw ν q₁ q₂ s).toFiniteLaw.prob E := by
  rw [fixedTailLaw, PositiveRationalLaw.toFiniteLaw_iid,
    FiniteLaw.iid_prob_coordinate]

theorem unrestricted_bin_marginal (ν : PositiveRationalLaw Y) (q₁ q₂ s : ℕ)
    [NeZero q₂] (p : Fin s) (E : OuterColumn q₁ q₂ s Y → Prop) :
    (rawLaw ν q₁ q₂ s).toFiniteLaw.prob (fun Z => E (Z.2 p)) =
      (outerLaw ν q₁ q₂ s).toFiniteLaw.prob E := by
  rw [rawLaw, PositiveRationalLaw.toFiniteLaw_prod,
    FiniteLaw.prod_prob_snd (ν.iid (s + 1)).toFiniteLaw
      ((outerLaw ν q₁ q₂ s).iid s).toFiniteLaw
      (fun js : Fin s → OuterColumn q₁ q₂ s Y => E (js p)),
    PositiveRationalLaw.toFiniteLaw_iid, FiniteLaw.iid_prob_coordinate]

theorem diagonal_bin_marginal (ν : PositiveRationalLaw Y) (q₁ q₂ s : ℕ)
    [NeZero q₂] (ξ₀ : Tail s Y) (p : Fin s) (E : OuterColumn q₁ q₂ s Y → Prop) :
    (outerLaw ν q₁ q₂ s).toFiniteLaw.prob (fun j => E (binProjection ξ₀ p (.diagonal j))) =
      (outerLaw ν q₁ q₂ s).toFiniteLaw.prob E := rfl

/-- Every tag has the same bin marginal, so the protected mixture does
too. This statement concerns the actual `forgetTag` used by the entries. -/
theorem tagged_bin_marginal (ν : PositiveRationalLaw Y) (q₁ q₂ s : ℕ)
    [NeZero q₂] (ξ₀ : Tail s Y) (p : Fin s) (E : OuterColumn q₁ q₂ s Y → Prop) :
    (taggedLaw ν q₁ q₂ s).toFiniteLaw.prob (fun Z => E (binProjection ξ₀ p Z)) =
      (outerLaw ν q₁ q₂ s).toFiniteLaw.prob E := by
  rw [tagged_prob]
  change (127 / 128 : ℝ) * (rawLaw ν q₁ q₂ s).toFiniteLaw.prob (fun Z => E (Z.2 p)) +
    (1 / 256 : ℝ) * (fixedTailLaw ν q₁ q₂ s).toFiniteLaw.prob (fun js => E (js p)) +
    (1 / 256 : ℝ) * (outerLaw ν q₁ q₂ s).toFiniteLaw.prob E = _
  rw [unrestricted_bin_marginal, fixedTail_bin_marginal]
  ring

def tagIndex {q₁ q₂ s : ℕ} : TaggedColumn q₁ q₂ s Y → Fin 3
  | .unrestricted _ => 0
  | .fixedTail _ => 1
  | .diagonal _ => 2

/-- Exact protected tag masses, including the dominant reference family. -/
theorem tag_masses (ν : PositiveRationalLaw Y) (q₁ q₂ s : ℕ) [NeZero q₂] :
    (taggedLaw ν q₁ q₂ s).toFiniteLaw.prob (fun Z => tagIndex Z = 0) = 127 / 128 ∧
    (taggedLaw ν q₁ q₂ s).toFiniteLaw.prob (fun Z => tagIndex Z = 1) = 1 / 256 ∧
    (taggedLaw ν q₁ q₂ s).toFiniteLaw.prob (fun Z => tagIndex Z = 2) = 1 / 256 := by
  simp only [tagged_prob, tagIndex]
  norm_num [Fin.ext_iff]

section RowLaws

variable {X V A : Type*} [Fintype X] [Fintype V] [Fintype A]
  [Nonempty V] [Nonempty A]

/-- A template has independent inner rows; each inner row consists of a
uniform coordinate and an original base-row input. -/
noncomputable def templateLaw (μ : PositiveRationalLaw X) (q₁ q₂ : ℕ) [NeZero q₁] :
    PositiveRationalLaw (Template q₁ q₂ X) :=
  ((PositiveRationalLaw.uniform (Fin q₁)).prod μ).iid q₂

noncomputable def templateRowLaw (μ : PositiveRationalLaw X) (q₁ q₂ s : ℕ)
    [NeZero q₁] [NeZero s] : PositiveRationalLaw (Fin s × Template q₁ q₂ X) :=
  (PositiveRationalLaw.uniform (Fin s)).prod (templateLaw μ q₁ q₂)

noncomputable def itemRowLaw (μ : PositiveRationalLaw X) (J : Type*)
    [Fintype J] [Nonempty J] : PositiveRationalLaw (J × X) :=
  (PositiveRationalLaw.uniform J).prod μ

omit [Nonempty V] [Nonempty A] in
theorem sum_rows {α : Type*} [AddCommMonoid α] (q₁ q₂ s : ℕ)
    (f : RawRow q₁ q₂ s X (V ⊕ A) → α) :
    (∑ k, f k) = (∑ k, f (.inl k)) +
      (∑ k : V × X, f (.inr (.inl k.1, k.2))) +
      ∑ k : A × X, f (.inr (.inr k.1, k.2)) := by
  simp only [RawRow, Fintype.sum_sum_type, Fintype.sum_prod_type]
  exact (add_assoc _ _ _).symm

/-- The exact source row mixture. Vertex and auxiliary labels remain
distinct, and every label is sampled uniformly within its own family. -/
noncomputable def rowLaw (μ : PositiveRationalLaw X) (q₁ q₂ s : ℕ)
    [NeZero q₁] [NeZero s] : PositiveRationalLaw (RawRow q₁ q₂ s X (V ⊕ A)) where
  weight
    | .inl k => (255 / 256) * (templateRowLaw μ q₁ q₂ s).weight k
    | .inr (.inl v, x) => (1 / 512) * (itemRowLaw μ V).weight (v, x)
    | .inr (.inr a, x) => (1 / 512) * (itemRowLaw μ A).weight (a, x)
  positive k := by
    rcases k with k | ⟨v | a, x⟩
    · exact mul_pos (by norm_num) ((templateRowLaw μ q₁ q₂ s).positive k)
    · exact mul_pos (by norm_num) ((itemRowLaw μ V).positive (v, x))
    · exact mul_pos (by norm_num) ((itemRowLaw μ A).positive (a, x))
  total := by
    rw [sum_rows]
    simp only [← Finset.mul_sum, PositiveRationalLaw.total, mul_one]
    change (255 / 256 : ℚ) + (1 / 512) * (∑ k, (itemRowLaw μ V).weight k) +
      (1 / 512) * (∑ k, (itemRowLaw μ A).weight k) = 1
    rw [(itemRowLaw μ V).total, (itemRowLaw μ A).total]
    norm_num

theorem row_prob (μ : PositiveRationalLaw X) (q₁ q₂ s : ℕ)
    [NeZero q₁] [NeZero s] (E : RawRow q₁ q₂ s X (V ⊕ A) → Prop) :
    (rowLaw μ q₁ q₂ s).toFiniteLaw.prob E =
      (255 / 256 : ℝ) * (templateRowLaw μ q₁ q₂ s).toFiniteLaw.prob (fun k => E (.inl k)) +
      (1 / 512 : ℝ) * (itemRowLaw μ V).toFiniteLaw.prob (fun k => E (.inr (.inl k.1, k.2))) +
      (1 / 512 : ℝ) * (itemRowLaw μ A).toFiniteLaw.prob (fun k => E (.inr (.inr k.1, k.2))) := by
  classical
  unfold FiniteLaw.prob
  rw [sum_rows]
  simp only [PositiveRationalLaw.toFiniteLaw, rowLaw, Rat.cast_mul,
    Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Finset.mul_sum, mul_ite, mul_zero]

def rowFamilyIndex {q₁ q₂ s : ℕ} : RawRow q₁ q₂ s X (V ⊕ A) → Fin 3
  | .inl _ => 0
  | .inr (.inl _, _) => 1
  | .inr (.inr _, _) => 2

theorem row_family_masses (μ : PositiveRationalLaw X) (q₁ q₂ s : ℕ)
    [NeZero q₁] [NeZero s] :
    (rowLaw (V := V) (A := A) μ q₁ q₂ s).toFiniteLaw.prob
      (fun k => rowFamilyIndex k = 0) = 255 / 256 ∧
    (rowLaw (V := V) (A := A) μ q₁ q₂ s).toFiniteLaw.prob
      (fun k => rowFamilyIndex k = 1) = 1 / 512 ∧
    (rowLaw (V := V) (A := A) μ q₁ q₂ s).toFiniteLaw.prob
      (fun k => rowFamilyIndex k = 2) = 1 / 512 := by
  simp only [row_prob, rowFamilyIndex]
  norm_num [Fin.ext_iff]

/-- Each coordinate of a template has the original independent law on
the coordinate-labelled base rows. -/
theorem template_coordinate_marginal (μ : PositiveRationalLaw X) (q₁ q₂ : ℕ)
    [NeZero q₁] (i : Fin q₂) (E : InnerRow q₁ X → Prop) :
    (templateLaw μ q₁ q₂).toFiniteLaw.prob (fun z => E (z i)) =
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μ).toFiniteLaw.prob E := by
  rw [templateLaw, PositiveRationalLaw.toFiniteLaw_iid, FiniteLaw.iid_prob_coordinate]

/-- A template bin has exactly the product law on its whole template. -/
theorem template_bin_law (μ : PositiveRationalLaw X) (q₁ q₂ s : ℕ)
    [NeZero q₁] [NeZero s] (E : Template q₁ q₂ X → Prop) :
    (templateRowLaw μ q₁ q₂ s).toFiniteLaw.prob (fun k => E k.2) =
      (templateLaw μ q₁ q₂).toFiniteLaw.prob E := by
  rw [templateRowLaw, PositiveRationalLaw.toFiniteLaw_prod, FiniteLaw.prod_prob_snd]

/-- The law within each fixed template bin, with its actual joint mass.
The base template law does not depend on which bin was selected. -/
theorem fixed_template_bin_law (μ : PositiveRationalLaw X) (q₁ q₂ s : ℕ)
    [NeZero q₁] [NeZero s] (p : Fin s) (E : Template q₁ q₂ X → Prop) :
    (templateRowLaw μ q₁ q₂ s).toFiniteLaw.prob (fun k => k.1 = p ∧ E k.2) =
      (s : ℝ)⁻¹ * (templateLaw μ q₁ q₂).toFiniteLaw.prob E := by
  rw [templateRowLaw, PositiveRationalLaw.toFiniteLaw_prod,
    FiniteLaw.prod_prob_fixed_fst]
  simp only [PositiveRationalLaw.toFiniteLaw, PositiveRationalLaw.uniform,
    Fintype.card_fin, Rat.cast_inv, Rat.cast_natCast]

def templateBinEvent {q₁ q₂ s : ℕ} (p : Fin s) (E : Template q₁ q₂ X → Prop) :
    RawRow q₁ q₂ s X (V ⊕ A) → Prop
  | .inl k => k.1 = p ∧ E k.2
  | .inr _ => False

/-- Within the complete source mixture, every template bin has mass
`(255/256)/s` and the conditional product law on its template. -/
theorem row_template_bin_law (μ : PositiveRationalLaw X) (q₁ q₂ s : ℕ)
    [NeZero q₁] [NeZero s] (p : Fin s) (E : Template q₁ q₂ X → Prop) :
    (rowLaw (V := V) (A := A) μ q₁ q₂ s).toFiniteLaw.prob (templateBinEvent p E) =
      (255 / 256 : ℝ) * (s : ℝ)⁻¹ * (templateLaw μ q₁ q₂).toFiniteLaw.prob E := by
  rw [row_prob]
  simp only [templateBinEvent, FiniteLaw.prob_false, mul_zero, add_zero]
  rw [fixed_template_bin_law]
  ring

end RowLaws

end SourceLaws
end Paper2

#print axioms Paper2.SourceLaws.tagged_prob
#print axioms Paper2.SourceLaws.tagged_bin_marginal
#print axioms Paper2.SourceLaws.row_prob
#print axioms Paper2.SourceLaws.row_family_masses
#print axioms Paper2.SourceLaws.row_template_bin_law
