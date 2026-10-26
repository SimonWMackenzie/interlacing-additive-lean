import Mathlib

/-!
# Prefix-free frontier capacity

Locked source: v12 Section 4, `src:frontier` (lines 330--350).
The stopping nodes are actual finite binary paths. Their Kraft bound is
proved, not a certificate field. The overload argument works even for
nonnegative real counts, hence includes the stated integer counts.

The elementary completion-count proof below adapts the checked generic
combinatorics in `EthInapproximability/ParameterizedNP/`
`DenseFrontierConservation.lean`, lines 300--416. Only Mathlib is imported;
none of that campaign's protocol or source contracts is consumed.
-/

namespace Paper2.Frontier

open scoped BigOperators

/-- Distinct stopping nodes cannot be prefixes of each other. -/
def PrefixFree {ι : Type*} (route : ι → List Bool) : Prop :=
  ∀ v w : ι, v ≠ w → ¬ (route v).IsPrefix (route w)

private def blocks (n : ℕ) : Finset (List Bool) :=
  (Finset.univ : Finset (Fin n → Bool)).image (fun f => List.ofFn f)

private theorem mem_blocks {n : ℕ} {w : List Bool} :
    w ∈ blocks n ↔ w.length = n := by
  constructor
  · intro hw
    obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp hw
    simp
  · intro hw
    subst hw
    exact Finset.mem_image.mpr ⟨w.get, Finset.mem_univ _, List.ofFn_get w⟩

private theorem card_blocks (n : ℕ) : (blocks n).card = 2 ^ n := by
  rw [blocks, Finset.card_image_of_injective _ List.ofFn_injective]
  simp

private def extensions (r : ℕ) (p : List Bool) : Finset (List Bool) :=
  (blocks (r - p.length)).image (fun s => p ++ s)

private theorem card_extensions (r : ℕ) (p : List Bool) :
    (extensions r p).card = 2 ^ (r - p.length) := by
  rw [extensions,
    Finset.card_image_of_injective _ (fun s t h => List.append_cancel_left h), card_blocks]

private theorem prefix_of_mem_extensions {r : ℕ} {p w : List Bool}
    (h : w ∈ extensions r p) : p <+: w := by
  obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp h
  exact ⟨s, rfl⟩

private theorem extensions_subset_blocks {r : ℕ} {p : List Bool}
    (hp : p.length ≤ r) : extensions r p ⊆ blocks r := by
  intro w hw
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hw
  rw [mem_blocks] at hs ⊢
  rw [List.length_append, hs]
  omega

private theorem prefix_or_prefix : ∀ {p q w : List Bool},
    p <+: w → q <+: w → p <+: q ∨ q <+: p := by
  intro p
  induction p with
  | nil => intro q w _ _; exact Or.inl List.nil_prefix
  | cons a p ih =>
    intro q w hp hq
    cases q with
    | nil => exact Or.inr List.nil_prefix
    | cons b q =>
      obtain ⟨t, rfl⟩ := hp
      obtain ⟨u, hu⟩ := hq
      rw [List.cons_append, List.cons_append, List.cons.injEq] at hu
      obtain ⟨hab, hqu⟩ := hu
      subst hab
      rcases ih (q := q) (w := p ++ t) ⟨t, rfl⟩ ⟨u, hqu⟩ with h | h
      · obtain ⟨s, rfl⟩ := h
        exact Or.inl ⟨s, by simp⟩
      · obtain ⟨s, rfl⟩ := h
        exact Or.inr ⟨s, by simp⟩

/-- Count disjoint completions to one common depth. -/
theorem sum_integer_capacity_le {ι : Type*} [Fintype ι]
    (route : ι → List Bool) (hpf : PrefixFree route) (r : ℕ)
    (hdepth : ∀ v, (route v).length ≤ r) :
    ∑ v, 2 ^ (r - (route v).length) ≤ 2 ^ r := by
  classical
  have hdisj : ∀ v ∈ (Finset.univ : Finset ι), ∀ w ∈ (Finset.univ : Finset ι),
      v ≠ w → Disjoint (extensions r (route v)) (extensions r (route w)) := by
    intro v _ w _ hvw
    rw [Finset.disjoint_left]
    intro p hp hp'
    rcases prefix_or_prefix (prefix_of_mem_extensions hp)
      (prefix_of_mem_extensions hp') with h | h
    · exact hpf v w hvw h
    · exact hpf w v (Ne.symm hvw) h
  have hsub : Finset.univ.biUnion (fun v => extensions r (route v)) ⊆ blocks r := by
    intro w hw
    obtain ⟨v, -, hv⟩ := Finset.mem_biUnion.mp hw
    exact extensions_subset_blocks (hdepth v) hv
  have hle := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisj, card_blocks] at hle
  simpa [card_extensions] using hle

/-- Kraft's bound for arbitrary nonnegative real initial capacity, including
the empty frontier and the root-only frontier. -/
theorem sum_capacity_le {ι : Type*} [Fintype ι]
    (route : ι → List Bool) (hpf : PrefixFree route) (q : ℝ) (hq : 0 ≤ q) :
    ∑ v, q / 2 ^ (route v).length ≤ q := by
  classical
  let r := Finset.univ.sup (fun v => (route v).length)
  have hdepth (v : ι) : (route v).length ≤ r :=
    Finset.le_sup (f := fun v => (route v).length) (Finset.mem_univ v)
  have hnat := sum_integer_capacity_le route hpf r hdepth
  have hreal : ∑ v, (2 : ℝ) ^ (r - (route v).length) ≤ (2 : ℝ) ^ r := by
    exact_mod_cast hnat
  have heq (v : ι) : q / 2 ^ (route v).length =
      (q / 2 ^ r) * 2 ^ (r - (route v).length) := by
    rw [pow_sub₀ (2 : ℝ) (by norm_num : (2 : ℝ) ≠ 0) (hdepth v)]
    field_simp
  simp_rw [heq]
  rw [← Finset.mul_sum]
  have h := mul_le_mul_of_nonneg_left hreal
    (show 0 ≤ q / 2 ^ r from div_nonneg hq (by positivity))
  simpa using h

/-- The overload calculation, separated from the actual prefix-free proof.
The only capacity premise is the displayed finite-sum inequality. -/
theorem overload_of_capacity_sum {ι : Type*} [Fintype ι]
    (κ h z : ι → ℝ) (q b t w₀ : ℝ)
    (hκ : ∀ v, 0 ≤ κ v) (hz : ∀ v, 0 ≤ z v)
    (hzh : ∀ v, z v ≤ h v)
    (hsumκ : ∑ v, κ v ≤ q) (hsumh : ∑ v, h v = q - b + t)
    (hsumz : ∑ v, z v = w₀ - t) (ht : 0 ≤ t) (hw : 3 * b < w₀) :
    ∃ v, 3 * κ v / 4 ≤ h v ∧ κ v < h v + z v := by
  classical
  by_contra! hno
  have hhk (v : ι) : h v ≤ κ v := by
    by_contra! hv
    have hlarge : 3 * κ v / 4 ≤ h v := by linarith [hκ v]
    have := hno v hlarge
    linarith [hz v]
  have hlocal (v : ι) : z v ≤ 3 * (κ v - h v) := by
    by_cases hv : h v + z v ≤ κ v
    · linarith [hhk v]
    · have hsmall : h v < 3 * κ v / 4 := by
        by_contra! hn
        exact hv (hno v hn)
      linarith [hzh v]
  have hsum := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hlocal v)
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib, hsumh, hsumz] at hsum
  linarith

/-- Full manuscript frontier inequality on actual prefix-free binary paths.
The hypotheses allow real counts; nonnegative integer counts are a special case. -/
theorem frontier_overload {ι : Type*} [Fintype ι]
    (route : ι → List Bool) (hpf : PrefixFree route)
    (h z : ι → ℝ) (q b t w₀ : ℝ) (hq : 0 ≤ q)
    (hz : ∀ v, 0 ≤ z v) (hzh : ∀ v, z v ≤ h v)
    (hsumh : ∑ v, h v = q - b + t)
    (hsumz : ∑ v, z v = w₀ - t) (ht : 0 ≤ t) (hw : 3 * b < w₀) :
    ∃ v, 3 * (q / 2 ^ (route v).length) / 4 ≤ h v ∧
      q / 2 ^ (route v).length < h v + z v := by
  apply overload_of_capacity_sum (fun v => q / 2 ^ (route v).length)
    h z q b t w₀
  · intro v
    exact div_nonneg hq (by positivity)
  · exact hz
  · exact hzh
  · exact sum_capacity_le route hpf q hq
  · exact hsumh
  · exact hsumz
  · exact ht
  · exact hw

end Paper2.Frontier
