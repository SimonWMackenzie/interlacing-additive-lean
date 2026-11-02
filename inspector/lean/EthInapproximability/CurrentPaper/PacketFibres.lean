import EthInapproximability.ParameterizedNP.WrapperProtectedEarly
import EthBridge.Induction

/-!
# Actual row selection for several protected copies

Source: v8 `A-stage4-details.tex`, `lem:paper-uniform-protected-packet`,
the averaging and row trimming in its proof. A donor supplies an actual
subset of `Fin q × X`; the construction retains donor identity when these
sets are flattened into the `v*q` blocks of one interlace.

Only the generic reverse-Markov counting lemma and the exact row-trimming
lemma are reused. No old protected-closure or communication endpoint is used.
-/

namespace EthInapproximability.CurrentPaper.PacketFibres

open scoped BigOperators
open NPCC

variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [Fintype X]

omit [Fintype X] in
/-- Every row is counted in exactly one coordinate fibre. -/
theorem sum_fibre_card (R : Finset (ι × X)) :
    ∑ i : ι, (R.filter (fun r => r.1 = i)).card = R.card := by
  classical
  exact (Finset.card_eq_sum_card_fiberwise
    (t := Finset.univ) (f := Prod.fst) (fun _ _ => Finset.mem_univ _)).symm

omit [Fintype ι] in
/-- A coordinate fibre contains at most all the payload rows. -/
theorem fibre_card_le (R : Finset (ι × X)) (i : ι) :
    (R.filter (fun r => r.1 = i)).card ≤ Fintype.card X := by
  classical
  have hsub : R.filter (fun r => r.1 = i) ⊆
      ({i} : Finset ι) ×ˢ (Finset.univ : Finset X) := by
    intro r hr
    simp only [Finset.mem_filter] at hr
    exact Finset.mem_product.mpr ⟨Finset.mem_singleton.mpr hr.2, Finset.mem_univ _⟩
  simpa using Finset.card_le_card hsub

/-- Density at least `d` supplies at least `d/2` of all the coordinate
fibres, each of density at least `d/2`. The density comes from actual rows. -/
theorem good_fibres_card [Nonempty X] (R : Finset (ι × X)) {d : ℝ}
    (hd : 0 ≤ d)
    (hrows : d * Fintype.card ι * Fintype.card X ≤ (R.card : ℝ)) :
    d / 2 * Fintype.card ι ≤
      ((Finset.univ.filter (fun i =>
        d / 2 * Fintype.card X ≤ ((R.filter (fun r => r.1 = i)).card : ℝ))).card : ℝ) := by
  classical
  have hn : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  let f : ι → ℝ := fun i => ((R.filter (fun r => r.1 = i)).card : ℝ) /
    Fintype.card X
  have hf : ∀ i ∈ (Finset.univ : Finset ι), f i ≤ 1 := by
    intro i _
    dsimp [f]
    rw [div_le_one hn]
    exact_mod_cast fibre_card_le R i
  have hsum : d * (Finset.univ : Finset ι).card ≤ ∑ i : ι, f i := by
    simp only [Finset.card_univ]
    dsimp [f]
    rw [← Finset.sum_div, ← Nat.cast_sum, sum_fibre_card]
    exact (le_div_iff₀ hn).2 hrows
  have hc := ParameterizedNP.WrapperProtectedEarly.card_ge_of_sum_ge
    (Finset.univ : Finset ι) f (a := d) (b := d / 2) (by positivity) hf hsum
  have hpred : (Finset.univ.filter (fun i => d / 2 ≤ f i)) =
      (Finset.univ.filter (fun i => d / 2 * Fintype.card X ≤
        ((R.filter (fun r => r.1 = i)).card : ℝ))) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, f, le_div_iff₀ hn]
  rw [hpred, Finset.card_univ] at hc
  convert hc using 1
  ring

/-- Donor-major flattening: coordinate `(j,alpha)` has index `j*q+alpha`. -/
def flattenEquiv (v q : ℕ) (X : Type*) :
    (Fin v × (Fin q × X)) ≃ (Fin (v * q) × X) :=
  (Equiv.prodAssoc (Fin v) (Fin q) X).symm.trans
    (Equiv.prodCongr finProdFinEquiv (Equiv.refl X))

omit [Fintype X] in
@[simp] theorem flattenEquiv_apply (v q : ℕ) (z : Fin v × (Fin q × X)) :
    flattenEquiv v q X z = (finProdFinEquiv (z.1, z.2.1), z.2.2) := rfl

/-- The actual rows supplied by all selected donors, retaining their labels. -/
noncomputable def donorRows {v q : ℕ} (E : Fin v → Finset (Fin q × X)) :
    Finset (Fin v × (Fin q × X)) := by
  classical
  exact Finset.univ.filter (fun z => z.2 ∈ E z.1)

/-- The same rows in the block type used by localized stopping. -/
noncomputable def packetRows {v q : ℕ} (E : Fin v → Finset (Fin q × X)) :
    Finset (Fin (v * q) × X) :=
  (donorRows E).map (flattenEquiv v q X).toEmbedding

@[simp] theorem mem_packetRows {v q : ℕ} (E : Fin v → Finset (Fin q × X))
    (j : Fin v) (a : Fin q) (x : X) :
    (finProdFinEquiv (j, a), x) ∈ packetRows E ↔ (a, x) ∈ E j := by
  classical
  change flattenEquiv v q X (j, (a, x)) ∈ _ ↔ _
  simp only [packetRows, Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨z, hz, he⟩
    have he' := (flattenEquiv v q X).injective he
    subst z
    simpa [donorRows] using hz
  · intro h
    exact ⟨(j, (a, x)), by simpa [donorRows], rfl⟩

/-- Flattening does not discard repeated payloads belonging to different donors. -/
theorem packetRows_card {v q : ℕ} (E : Fin v → Finset (Fin q × X)) :
    (packetRows E).card = ∑ j : Fin v, (E j).card := by
  classical
  rw [packetRows, Finset.card_map, ← sum_fibre_card]
  apply Finset.sum_congr rfl
  intro j _
  have hf : (donorRows E).filter (fun z => z.1 = j) =
      ({j} : Finset (Fin v)) ×ˢ E j := by
    ext z
    simp only [donorRows, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_product, Finset.mem_singleton]
    constructor
    · rintro ⟨hz, rfl⟩
      exact ⟨rfl, hz⟩
    · rintro ⟨rfl, hz⟩
      exact ⟨hz, rfl⟩
  rw [hf]
  simp

/-- The density premise for each donor implies the density of the actual
flattened row set. No average-fibre premise is assumed. -/
theorem packetRows_density {v q : ℕ} (E : Fin v → Finset (Fin q × X))
    {d : ℝ} (hE : ∀ j, d * q * Fintype.card X ≤ ((E j).card : ℝ)) :
    d * Fintype.card (Fin (v * q)) * Fintype.card X ≤
      ((packetRows E).card : ℝ) := by
  rw [packetRows_card, Nat.cast_sum]
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin v)))
    (fun j _ => hE j)
  simpa [mul_assoc, mul_left_comm, mul_comm] using hsum

omit [Fintype X] in
/-- The exact number of selected coordinate blocks can be prescribed.
Rows outside these blocks are removed, and all remaining fibres are trimmed
to the same integer threshold. -/
theorem select_exact_rows (R : Finset (ι × X)) (T p : ℕ)
    (hp : p ≤ (Finset.univ.filter (fun i =>
      T ≤ (R.filter (fun r => r.1 = i)).card)).card) :
    ∃ (Q : Finset ι) (R' : Finset (ι × X)),
      Q.card = p ∧ R' ⊆ R ∧ (∀ r ∈ R', r.1 ∈ Q) ∧
      (∀ i ∈ Q, (R'.filter (fun r => r.1 = i)).card = T) ∧
      IsEquipartitionedGE R' Q T := by
  classical
  obtain ⟨Q, hQsub, hQcard⟩ := Finset.exists_subset_card_eq hp
  let RQ := R.filter (fun r => r.1 ∈ Q)
  have hRQ : IsEquipartitionedGE RQ Q T := by
    intro i hi
    have hg := (Finset.mem_filter.mp (hQsub hi)).2
    have he : RQ.filter (fun r => r.1 = i) = R.filter (fun r => r.1 = i) := by
      ext r
      simp only [RQ, Finset.mem_filter]
      constructor
      · exact fun h => ⟨h.1.1, h.2⟩
      · rintro ⟨hr, rfl⟩
        exact ⟨⟨hr, hi⟩, rfl⟩
    rw [he]
    exact hg
  obtain ⟨R', hR', hcounts⟩ := EthBridge.equipartitionGE_exists_exact_subset RQ Q T hRQ
  refine ⟨Q, R', hQcard, fun r hr => (Finset.mem_filter.mp (hR' hr)).1,
    fun r hr => (Finset.mem_filter.mp (hR' hr)).2, hcounts, ?_⟩
  intro i hi
  exact (hcounts i hi).ge

/-- Complete row-selection step of the uniform protected-packet argument.
For the paper instantiate `p = 9*K/16`; using arbitrary `p ≤ K` also
exposes the finite rounding boundary explicitly. -/
theorem protected_packet_rows [Nonempty X] {v q K p : ℕ}
    (E : Fin v → Finset (Fin q × X)) {d x : ℝ}
    (hd : 0 ≤ d)
    (hE : ∀ j, d * q * Fintype.card X ≤ ((E j).card : ℝ))
    (hcount : (K : ℝ) ≤ (v : ℝ) * d * q / 2)
    (hthreshold : (K : ℝ) * x ≤ d / 2) (hp : p ≤ K) :
    ∃ (Q : Finset (Fin (v * q))) (R' : Finset (Fin (v * q) × X)),
      Q.card = p ∧ R' ⊆ packetRows E ∧ (∀ r ∈ R', r.1 ∈ Q) ∧
      (∀ i ∈ Q, (R'.filter (fun r => r.1 = i)).card =
        ⌈(Fintype.card X : ℝ) * (K * x)⌉₊) ∧
      IsEquipartitionedGE R' Q ⌈(Fintype.card X : ℝ) * (K * x)⌉₊ := by
  classical
  apply select_exact_rows
  have hc := good_fibres_card (packetRows E) hd (packetRows_density E hE)
  have hK : K ≤ (Finset.univ.filter (fun i =>
      d / 2 * Fintype.card X ≤
        (((packetRows E).filter (fun r => r.1 = i)).card : ℝ))).card := by
    apply (Nat.cast_le (α := ℝ)).mp
    refine hcount.trans ?_
    simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hc
  refine hp.trans (hK.trans (Finset.card_le_card ?_))
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  refine ⟨hi.1, Nat.ceil_le.2 ?_⟩
  have hm := mul_le_mul_of_nonneg_right hthreshold
    (show (0 : ℝ) ≤ Fintype.card X by positivity)
  nlinarith [hi.2]

/-- The literal `9*K/16` block choice in the manuscript. -/
theorem protected_packet_nine_sixteenths [Nonempty X] {v q K : ℕ}
    (E : Fin v → Finset (Fin q × X)) {d x : ℝ}
    (hd : 0 ≤ d)
    (hE : ∀ j, d * q * Fintype.card X ≤ ((E j).card : ℝ))
    (hcount : (K : ℝ) ≤ (v : ℝ) * d * q / 2)
    (hthreshold : (K : ℝ) * x ≤ d / 2) :
    ∃ (Q : Finset (Fin (v * q))) (R' : Finset (Fin (v * q) × X)),
      Q.card = 9 * K / 16 ∧ R' ⊆ packetRows E ∧ (∀ r ∈ R', r.1 ∈ Q) ∧
      (∀ i ∈ Q, (R'.filter (fun r => r.1 = i)).card =
        ⌈(Fintype.card X : ℝ) * (K * x)⌉₊) ∧
      IsEquipartitionedGE R' Q ⌈(Fintype.card X : ℝ) * (K * x)⌉₊ := by
  exact protected_packet_rows E hd hE hcount hthreshold (by omega)

/-- A nonempty finite packet: nine distinct blocks, one row in each,
extracted from one donor's actual `32 × 2` full row set. -/
theorem full_rows_packet_regression :
    ∃ (Q : Finset (Fin 32)) (R' : Finset (Fin 32 × Fin 2)),
      Q.card = 9 ∧ R' ⊆ packetRows (fun _ : Fin 1 =>
        (Finset.univ : Finset (Fin 32 × Fin 2))) ∧
      (∀ r ∈ R', r.1 ∈ Q) ∧
      (∀ i ∈ Q, (R'.filter (fun r => r.1 = i)).card = 1) ∧
      IsEquipartitionedGE R' Q 1 := by
  have h := protected_packet_nine_sixteenths
    (K := 16) (d := 1) (x := (1 : ℝ) / 32)
    (fun _ : Fin 1 => (Finset.univ : Finset (Fin 32 × Fin 2)))
    (by norm_num) (by intro j; norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

end EthInapproximability.CurrentPaper.PacketFibres
