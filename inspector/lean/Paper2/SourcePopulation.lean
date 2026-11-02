import Paper2.StrongSeedSelection

/-!
# Selecting populated coordinate blocks

Frozen v12 Section 4, `src:profiles`, equation `eq:population`.
The blocks are equally weighted in the outer population; each block may
carry an arbitrary inner law. The threshold count concerns actual block
masses, and the selected indices form an injection into the original blocks.
-/

namespace Paper2.SourcePopulation

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Blocks whose actual conditional retained mass meets the threshold. -/
noncomputable def qualifying (mass : ι → ℝ) (t : ℝ) : Finset ι :=
  Finset.univ.filter (fun i => t ≤ mass i)

@[simp] theorem mem_qualifying (mass : ι → ℝ) (t : ℝ) (i : ι) :
    i ∈ qualifying mass t ↔ t ≤ mass i := by
  classical
  simp [qualifying]

/-- Bound the total by one on qualifying blocks and by the threshold on
the remaining blocks. Equality with the threshold counts as qualifying. -/
theorem sum_le_population (mass : ι → ℝ) (t : ℝ)
    (hupper : ∀ i, mass i ≤ 1) :
    ∑ i, mass i ≤ (Fintype.card ι : ℝ) * t +
      ((qualifying mass t).card : ℝ) * (1 - t) := by
  classical
  have hh : ∀ i, mass i ≤ t + if t ≤ mass i then 1 - t else 0 := by
    intro i
    split_ifs with hi
    · linarith [hupper i]
    · have := lt_of_not_ge hi
      linarith
  calc
    _ ≤ ∑ i, (t + if t ≤ mass i then 1 - t else 0) :=
      Finset.sum_le_sum (fun i _ => hh i)
    _ = _ := by
      simp [Finset.sum_add_distrib, Finset.sum_ite, qualifying, nsmul_eq_mul]
      ring

/-- The population count in the source-profile proof, including the
ceiling. No positivity of the resulting numerator is needed. -/
theorem qualifying_card_bound (mass : ι → ℝ) (β t : ℝ)
    (hupper : ∀ i, mass i ≤ 1) (ht : t < 1)
    (htotal : (Fintype.card ι : ℝ) * β ≤ ∑ i, mass i) :
    ⌈(Fintype.card ι : ℝ) * (β - t) / (1 - t)⌉₊ ≤
      (qualifying mass t).card := by
  apply Nat.ceil_le.mpr
  apply (div_le_iff₀ (by linarith : 0 < 1 - t)).mpr
  have hh := sum_le_population mass t hupper
  nlinarith

/-- Convert a proved population count into exactly the requested number
of distinct original indices. -/
theorem exists_selection_of_card (mass : ι → ℝ) (t : ℝ)
    (n : ℕ) (hn : n ≤ (qualifying mass t).card) :
    ∃ e : Fin n ↪ ι, ∀ j, t ≤ mass (e j) := by
  classical
  have hcard : n ≤ Fintype.card (qualifying mass t) := by
    simpa only [Fintype.card_coe] using hn
  let e : Fin n → qualifying mass t := fun j =>
    (Fintype.equivFin (qualifying mass t)).symm ⟨j.val, lt_of_lt_of_le j.isLt hcard⟩
  have he : Function.Injective e := by
    intro i j hij
    have hh := (Fintype.equivFin (qualifying mass t)).symm.injective hij
    exact Fin.ext (congrArg (fun z : Fin (Fintype.card (qualifying mass t)) => z.val) hh)
  refine ⟨⟨fun j => (e j).val, Subtype.val_injective.comp he⟩, ?_⟩
  intro j
  exact (mem_qualifying mass t _).mp (e j).property

/-- Exactly the requested number of actual qualifying indices can be
selected whenever the population lower bound is at least that number. -/
theorem exists_selection (mass : ι → ℝ) (β t : ℝ)
    (hupper : ∀ i, mass i ≤ 1) (ht : t < 1)
    (htotal : (Fintype.card ι : ℝ) * β ≤ ∑ i, mass i)
    (n : ℕ) (hn : n ≤ ⌈(Fintype.card ι : ℝ) * (β - t) / (1 - t)⌉₊) :
    ∃ e : Fin n ↪ ι, ∀ j, t ≤ mass (e j) :=
  exists_selection_of_card mass t n
    (hn.trans (qualifying_card_bound mass β t hupper ht htotal))

/-- Division-free form suitable for an explicit source parameter schedule. -/
theorem exists_selection_of_budget (mass : ι → ℝ) (β t : ℝ)
    (hupper : ∀ i, mass i ≤ 1) (ht : t < 1)
    (htotal : (Fintype.card ι : ℝ) * β ≤ ∑ i, mass i)
    (n : ℕ)
    (hbudget : (n : ℝ) * (1 - t) ≤ (Fintype.card ι : ℝ) * (β - t)) :
    ∃ e : Fin n ↪ ι, ∀ j, t ≤ mass (e j) := by
  have hh := sum_le_population mass t hupper
  have hcard : (n : ℝ) ≤ ((qualifying mass t).card : ℝ) := by
    nlinarith
  exact exists_selection_of_card mass t n (by exact_mod_cast hcard)

/-- Equivalent capacity form: the proposed number of fully occupied
blocks and threshold-filled remaining blocks already fits below total mass. -/
theorem exists_selection_of_capacity (mass : ι → ℝ) (β t : ℝ)
    (hupper : ∀ i, mass i ≤ 1) (ht : t < 1)
    (htotal : (Fintype.card ι : ℝ) * β ≤ ∑ i, mass i)
    (n : ℕ)
    (hcapacity : (n : ℝ) + ((Fintype.card ι : ℝ) - n) * t ≤
      (Fintype.card ι : ℝ) * β) :
    ∃ e : Fin n ↪ ι, ∀ j, t ≤ mass (e j) :=
  exists_selection_of_budget mass β t hupper ht htotal n (by nlinarith)

open Workspace.Types.CommComplexity

/-- Apply the population argument and the strong seed directly to an
actual retained interlace. The only schedule assumption is the displayed
numerical block-count inequality, not a lower-bound certificate. -/
theorem retained_interlace_bound
    {X Y : Type*} [Fintype X] [Fintype Y]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (F : X → Y → Bool) (H a : ℕ) (hH : 3 ≤ H) (ha : 4 ≤ a)
    (θ β : ℝ) (hθ : 0 < θ) (ht : (2 : ℝ) ^ a * θ < 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw θ (H : ℤ))
    (q : ℕ) (R : Finset (Fin q × X)) (K : Finset (Fin q → Y))
    (hrows : (q : ℝ) * β ≤ ∑ i : Fin q,
      μ.toFiniteLaw.prob (fun x => (i, x) ∈ R))
    (hbudget : (StrongSeed.copies a : ℝ) * (1 - (2 : ℝ) ^ a * θ) ≤
      (q : ℝ) * (β - (2 : ℝ) ^ a * θ))
    (hcolumns : (2 : ℝ) ^ (-((2 : ℝ) ^ a / 1024)) ≤
      (ν.toFiniteLaw.iid q).prob (· ∈ K)) :
    H + a ≤ D (NPCC.subgame (fullInterlace F q) R K) := by
  obtain ⟨e, he⟩ := exists_selection_of_budget
    (fun i : Fin q => μ.toFiniteLaw.prob (fun x => (i, x) ∈ R)) β
    ((2 : ℝ) ^ a * θ) (fun i => μ.toFiniteLaw.prob_le_one _) ht
    (by simpa only [Fintype.card_fin] using hrows) (StrongSeed.copies a)
    (by simpa only [Fintype.card_fin] using hbudget)
  exact StrongSeedSelection.selected_member μ ν F H a hH ha θ hθ ht.le hprofile
    q e e.injective R K he hcolumns

end Paper2.SourcePopulation
