import NPCC.Relaxed
import NPCC.Twin
import EthInapproximability.ParameterizedNP.InheritedContracts

/-!
# Indexed projection for the current paper

Source: v8 `02-foundations.tex`, `lem:paper-indexed-projection` and
`lem:paper-balanced-extraction`. Family labels are never deduplicated before
counting retained columns. The projected classical game uses actual retained
labels, so its communication bound transfers to the same relaxed restriction.

Generic finite counting is proved here. The balanced extraction construction
reuses `NPCC.relaxed_to_classical`, whose actual row and column provenance is
retained; no balanced-family existence theorem is imported or assumed.
-/

namespace EthInapproximability.CurrentPaper.IndexedProjection

open scoped BigOperators
open NPCC
open Workspace.Types.CommComplexity Workspace.Types.Interlace

/-- Counting all retained labels by their projected values, with multiplicity. -/
theorem card_le_image_card_mul {A B : Type*} [DecidableEq A] [DecidableEq B]
    (K : Finset A) (f : A → B) {bound : ℝ}
    (hfibre : ∀ b, ((K.filter (fun a => f a = b)).card : ℝ) ≤ bound) :
    (K.card : ℝ) ≤ ((K.image f).card : ℝ) * bound := by
  have hsum : K.card = ∑ b ∈ K.image f, (K.filter (fun a => f a = b)).card :=
    Finset.card_eq_sum_card_fiberwise (fun a ha => Finset.mem_image_of_mem f ha)
  have hsumR : (K.card : ℝ) =
      ∑ b ∈ K.image f, ((K.filter (fun a => f a = b)).card : ℝ) := by
    exact_mod_cast hsum
  rw [hsumR]
  calc
    _ ≤ ∑ _b ∈ K.image f, bound := Finset.sum_le_sum (fun b _ => hfibre b)
    _ = _ := by simp

/-- The strict integer gate gives the exact ceiling, including boundary cases. -/
theorem image_card_ge_of_strict_gate {A B : Type*}
    [DecidableEq A] [DecidableEq B] (K : Finset A) (f : A → B)
    {bound : ℝ} {threshold : ℕ} (hb : 0 ≤ bound)
    (hfibre : ∀ b, ((K.filter (fun a => f a = b)).card : ℝ) ≤ bound)
    (hgate : ((threshold : ℝ) - 1) * bound < K.card) :
    threshold ≤ (K.image f).card := by
  by_contra h
  have hn : (K.image f).card + 1 ≤ threshold := by omega
  have hr : ((K.image f).card : ℝ) ≤ (threshold : ℝ) - 1 := by
    have hr' : ((K.image f).card : ℝ) + 1 ≤ (threshold : ℝ) := by exact_mod_cast hn
    linarith
  have hc := card_le_image_card_mul K f hfibre
  have hm := mul_le_mul_of_nonneg_right hr hb
  linarith

/-- The density version of the same fibre count; no lower fibre bound is used. -/
theorem image_card_ge_of_density {A B : Type*}
    [DecidableEq A] [DecidableEq B] (K : Finset A) (f : A → B)
    {L N κ z : ℝ} (hL : 0 < L) (hN : 0 < N) (hκ : 0 < κ)
    (hfibre : ∀ b, ((K.filter (fun a => f a = b)).card : ℝ) ≤ κ * L / N)
    (hcol : z * L ≤ K.card) :
    ⌈N * (z / κ)⌉₊ ≤ (K.image f).card := by
  rw [Nat.ceil_le]
  have hc := hcol.trans (card_le_image_card_mul K f hfibre)
  have hc' : z * L * N ≤ ((K.image f).card : ℝ) * κ * L := by
    apply (le_div_iff₀ hN).mp
    simpa only [mul_div_assoc, mul_assoc] using hc
  rw [← mul_div_assoc, div_le_iff₀ hκ]
  have hfinal : (N * z) * L ≤ (((K.image f).card : ℝ) * κ) * L := by nlinarith
  exact le_of_mul_le_mul_right hfinal hL

/-- Positive density meets the strict ceiling gate even at integer endpoints. -/
theorem strict_gate_of_density {L N κ z retained : ℝ}
    (hL : 0 < L) (hN : 0 < N) (hκ : 0 < κ) (hz : 0 < z)
    (hretained : z * L ≤ retained) :
    ((⌈N * (z / κ)⌉₊ : ℝ) - 1) * (κ * L / N) < retained := by
  have hc : (⌈N * (z / κ)⌉₊ : ℝ) < N * (z / κ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hm := mul_lt_mul_of_pos_right (by linarith :
    (⌈N * (z / κ)⌉₊ : ℝ) - 1 < N * (z / κ))
    (by positivity : 0 < κ * L / N)
  have heq : N * (z / κ) * (κ * L / N) = z * L := by
    field_simp
  rw [heq] at hm
  exact hm.trans_le hretained

/-- Actual row/label provenance gives a protocol pullback, not just a count. -/
theorem projected_subgame_le {X Y : Type*} [Fintype X] [Fintype Y]
    {q u L : ℕ} (f : X → Y → Bool) (S : Fin L → Fin q → Y)
    {R : Finset (Fin q × X)} {K : Finset (Fin L)}
    {R' : Finset (Fin u × X)} {C' : Finset (Fin u → Y)}
    (e : Fin u → Fin q)
    (hrows : ∀ a ∈ R', (e a.1, a.2) ∈ R)
    (hcols : ∀ c ∈ C', ∃ j ∈ K, ∀ i, c i = S j (e i)) :
    D (subgame (interlaceFun f u) R' C') ≤ D (subgame (relaxedInterlace f S) R K) := by
  classical
  let ρ : {a // a ∈ R'} → {a // a ∈ R} :=
    fun a => ⟨(e a.1.1, a.1.2), hrows a.1 a.2⟩
  let σ : {c // c ∈ C'} → {j // j ∈ K} :=
    fun c => ⟨(hcols c.1 c.2).choose, (hcols c.1 c.2).choose_spec.1⟩
  have heq : subgame (interlaceFun f u) R' C' =
      (fun a c => subgame (relaxedInterlace f S) R K (ρ a) (σ c)) := by
    funext a c
    apply congrArg (f a.1.2)
    exact (hcols c.1 c.2).choose_spec.2 a.1.1
  rw [heq]
  exact D_mapNodes_le _ ρ σ

/-- The paper's strict-ceiling indexed projection, needing only an upper
fibre bound on the specified coordinates. The conclusion retains actual
row and label representatives and transfers their protocol cost. -/
theorem indexed_projection {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    {q u L : ℕ} (f : X → Y → Bool) (S : Fin L → Fin q → Y)
    {x z κ : ℝ} (hu : 0 < u) (hκ : 0 ≤ κ)
    {Q : Finset (Fin q)} (e : Fin u ≃ {i // i ∈ Q})
    {R : Finset (Fin q × X)} {K : Finset (Fin L)}
    (hrow : IsEquipartitionedGE R Q ⌈(Fintype.card X : ℝ) * x⌉₊)
    (hfibre : ∀ c : Fin u → Y,
      ((Finset.univ.filter (fun j : Fin L => (fun i => S j (e i).val) = c)).card : ℝ)
        ≤ κ * L / (Fintype.card Y : ℝ) ^ u)
    (hgate : ((⌈(Fintype.card Y : ℝ) ^ u * z⌉₊ : ℝ) - 1) *
      (κ * L / (Fintype.card Y : ℝ) ^ u) < K.card) :
    ∃ RC' : Finset (Fin u × X) × Finset (Fin u → Y),
      RC' ∈ bracketGE X Y u x z ∧
      (∀ a ∈ RC'.1, ((e a.1).val, a.2) ∈ R) ∧
      (∀ c ∈ RC'.2, ∃ j ∈ K, ∀ i, c i = S j (e i).val) ∧
      D (subgame (interlaceFun f u) RC'.1 RC'.2) ≤
        D (subgame (relaxedInterlace f S) R K) := by
  classical
  have hfull : ⌈(Fintype.card Y : ℝ) ^ q * 1⌉₊ ≤
      (Finset.univ : Finset (Fin q → Y)).card := by
    simp only [mul_one, ← Nat.cast_pow, Nat.ceil_natCast, Finset.card_univ,
      Fintype.card_fun, Fintype.card_fin]
    exact le_refl _
  obtain ⟨RC0, hmem0, hrows, _⟩ :=
    EthInapproximability.ParameterizedNP.InheritedContracts.coordProjection
      q u hu Q e R Finset.univ ⌈(Fintype.card X : ℝ) * x⌉₊ x 1
      hrow hfull (le_refl _)
  let proj : Fin L → Fin u → Y := fun j i => S j (e i).val
  let cols := K.image proj
  have hrestricted : ∀ c, ((K.filter (fun j => proj j = c)).card : ℝ) ≤
      κ * L / (Fintype.card Y : ℝ) ^ u := by
    intro c
    have hsub : K.filter (fun j => proj j = c) ⊆
        Finset.univ.filter (fun j : Fin L => proj j = c) :=
      Finset.filter_subset_filter _ (Finset.subset_univ K)
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hfibre c)
  have hcols : ∀ c ∈ cols, ∃ j ∈ K, ∀ i, c i = S j (e i).val := by
    intro c hc
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hc
    exact ⟨j, hj, fun _ => rfl⟩
  have hcount : ⌈(Fintype.card Y : ℝ) ^ u * z⌉₊ ≤ cols.card :=
    image_card_ge_of_strict_gate K proj (by positivity) hrestricted hgate
  exact ⟨(RC0.1, cols), ⟨hmem0.1, hcount⟩, hrows, hcols,
    projected_subgame_le f S (fun i => (e i).val) hrows hcols⟩

/-- Density-form indexed projection with only the upper balance bound.
All retained labels are counted before selecting distinct tuple representatives. -/
theorem indexed_projection_of_density {X Y : Type*}
    [Fintype X] [Fintype Y] [Nonempty Y] [DecidableEq Y]
    {q u L : ℕ} (f : X → Y → Bool) (S : Fin L → Fin q → Y)
    {x z κ : ℝ} (hu : 0 < u) (hL : 0 < L) (hκ : 0 < κ) (hz : 0 < z)
    {Q : Finset (Fin q)} (e : Fin u ≃ {i // i ∈ Q})
    {R : Finset (Fin q × X)} {K : Finset (Fin L)}
    (hrow : IsEquipartitionedGE R Q ⌈(Fintype.card X : ℝ) * x⌉₊)
    (hfibre : ∀ c : Fin u → Y,
      ((Finset.univ.filter (fun j : Fin L => (fun i => S j (e i).val) = c)).card : ℝ)
        ≤ κ * L / (Fintype.card Y : ℝ) ^ u)
    (hcol : z * (L : ℝ) ≤ K.card) :
    ∃ RC' : Finset (Fin u × X) × Finset (Fin u → Y),
      RC' ∈ bracketGE X Y u x (z / κ) ∧
      (∀ a ∈ RC'.1, ((e a.1).val, a.2) ∈ R) ∧
      (∀ c ∈ RC'.2, ∃ j ∈ K, ∀ i, c i = S j (e i).val) ∧
      D (subgame (interlaceFun f u) RC'.1 RC'.2) ≤
        D (subgame (relaxedInterlace f S) R K) := by
  apply indexed_projection f S hu hκ.le e hrow hfibre
  exact strict_gate_of_density (by exact_mod_cast hL) (by positivity) hκ hz hcol

/-- A specified balanced coordinate set yields an actual classical restriction,
with its cost bounded by the original indexed-label restriction. -/
theorem balanced_projection {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    {q u t L : ℕ} (f : X → Y → Bool) {S : Fin L → Fin q → Y}
    {ε x z : ℝ} (hu : 0 < u) (hut : u ≤ t)
    (hS : IsBalancedFamily t S ε) (hε : 0 ≤ ε)
    {Q : Finset (Fin q)} (e : Fin u ≃ {i // i ∈ Q})
    {R : Finset (Fin q × X)} {K : Finset (Fin L)}
    (hrow : IsEquipartitionedGE R Q ⌈(Fintype.card X : ℝ) * x⌉₊)
    (hcol : z * (L : ℝ) ≤ K.card) :
    ∃ RC' : Finset (Fin u × X) × Finset (Fin u → Y),
      RC' ∈ bracketGE X Y u x (z / (1 + ε)) ∧
      (∀ a ∈ RC'.1, ((e a.1).val, a.2) ∈ R) ∧
      (∀ c ∈ RC'.2, ∃ j ∈ K, ∀ i, c i = S j (e i).val) ∧
      D (subgame (interlaceFun f u) RC'.1 RC'.2) ≤
        D (subgame (relaxedInterlace f S) R K) := by
  obtain ⟨RC', hmem, hrows, hcols⟩ :=
    relaxed_to_classical hu hut hS hε e hrow hcol (le_refl _)
  exact ⟨RC', hmem, hrows, hcols,
    projected_subgame_le f S (fun i => (e i).val) hrows hcols⟩

/-- The extracted game proves the advertised lower bound for actual protocols. -/
theorem balanced_projection_lower_bound {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq Y]
    {q u t L : ℕ} (f : X → Y → Bool) {S : Fin L → Fin q → Y}
    {ε x z : ℝ} (hu : 0 < u) (hut : u ≤ t)
    (hS : IsBalancedFamily t S ε) (hε : 0 ≤ ε)
    {Q : Finset (Fin q)} (e : Fin u ≃ {i // i ∈ Q})
    {R : Finset (Fin q × X)} {K : Finset (Fin L)}
    (hrow : IsEquipartitionedGE R Q ⌈(Fintype.card X : ℝ) * x⌉₊)
    (hcol : z * (L : ℝ) ≤ K.card) :
    Dfamily (interlaceFun f u) (bracketGE X Y u x (z / (1 + ε))) ≤
      D (subgame (relaxedInterlace f S) R K) := by
  obtain ⟨RC', hmem, _, _, hcost⟩ := balanced_projection f hu hut hS hε e hrow hcol
  apply le_trans _ hcost
  exact Nat.sInf_le ⟨RC', hmem, rfl⟩

/-- Total retained row density gives the precise ceiling number of good blocks.
The condition `beta >= x` is derived, not silently added to the manuscript. -/
theorem enough_good_blocks {X : Type*} [Fintype X]
    {q v : ℕ} {R : Finset (Fin q × X)} {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (hv : 1 ≤ v)
    (hcount : v ≤ ⌈(q : ℝ) *
      ((R.card : ℝ) / ((q : ℝ) * (Fintype.card X : ℝ)) - x) / (1 - x)⌉₊) :
    ∃ P : Finset (Fin q), P.card = v ∧
      IsEquipartitionedGE R P ⌈(Fintype.card X : ℝ) * x⌉₊ := by
  have hβ : x ≤ (R.card : ℝ) / ((q : ℝ) * (Fintype.card X : ℝ)) := by
    by_contra h
    have hβlt := lt_of_not_ge h
    have hz : (q : ℝ) *
        ((R.card : ℝ) / ((q : ℝ) * (Fintype.card X : ℝ)) - x) / (1 - x) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg
      · exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg q) (by linarith)
      · linarith
    rw [Nat.ceil_eq_zero.mpr hz] at hcount
    omega
  obtain ⟨Q, hQcard, hQ⟩ := block_balancing hx0 hx1 hβ
  obtain ⟨P, hPQ, hPcard⟩ := Finset.exists_subset_card_eq (hcount.trans hQcard)
  exact ⟨P, hPcard, hQ.mono_Q hPQ⟩

/-- A genuine duplicate-label example: three retained labels yield two tuples. -/
theorem duplicate_labels_regression :
    let K : Finset (Fin 6) := {0, 1, 2}
    let f : Fin 6 → Fin 3 := fun i => ⟨i.val / 2, by omega⟩
    K.card = 3 ∧ (K.image f).card = 2 := by decide

/-- Equality in the counting gate is insufficient: four retained labels in
two-point fibres do not guarantee three distinct projected tuples. -/
theorem strict_gate_required_regression :
    let K : Finset (Fin 6) := {0, 1, 2, 3}
    let f : Fin 6 → Fin 3 := fun i => ⟨i.val / 2, by omega⟩
    (∀ y : Fin 3, ((Finset.univ : Finset (Fin 6)).filter
      (fun i => f i = y)).card ≤ 2) ∧
    (3 - 1) * 2 = K.card ∧ (K.image f).card < 3 := by decide

end EthInapproximability.CurrentPaper.IndexedProjection
