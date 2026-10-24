import NPCC.Stage1

/-!
# The exact indexing threshold of the current paper

Source: `2026-09-22-complete-replacement-v8`,
`03-exact-hardness.tex`, `lem:exact-index-threshold`.

The columns remain family labels, so repeated binary strings are counted
with their multiplicities. This proof uses only balanced pattern counts,
the actual protocol heavy-leaf theorem, and elementary finite arithmetic.
It does not use an old reduction matrix or the existence axiom for its sampler.
The generic imported heavy-leaf proof counts both Alice's and Bob's bits;
the output is the public Boolean label of a leaf.

The construction and running time of a balanced family are separate obligations.
-/

namespace EthInapproximability.CurrentPaper.ExactIndexing

open Workspace.Types.CommComplexity

/-- Balancedness bounds every prescribed pattern, counting column labels. -/
theorem balancedPattern_card_le {q N t : ℕ} {C : Fin N → Fin q → Bool}
    {ε : ℝ} (hC : NPCC.IsBalancedFamily t C ε)
    (J : Finset (Fin q)) (hJ : J.card ≤ t) (pattern : Fin q → Bool) :
    ((Finset.univ.filter
      (fun j : Fin N => ∀ i ∈ J, C j i = pattern i)).card : ℝ) ≤
      (1 + ε) / (2 : ℝ) ^ J.card * N := by
  classical
  have hupper := (abs_le.mp (hC.2 J hJ pattern)).2
  norm_num only [Fintype.card_bool] at hupper
  have hN : (0 : ℝ) < N := by exact_mod_cast hC.1
  apply (div_le_iff₀ hN).mp
  have hsum : (1 : ℝ) / 2 ^ J.card + ε / 2 ^ J.card =
      (1 + ε) / 2 ^ J.card := by ring
  linarith

/-- A monochromatic indexing rectangle prescribing at least `s` coordinates
has at most the balanced-family pattern bound many labelled columns. -/
theorem monochromaticRectangle_card_le {q N t : ℕ} {C : Fin N → Fin q → Bool}
    {ε : ℝ} (hC : NPCC.IsBalancedFamily t C ε)
    (R : Finset (Fin q)) (B : Finset (Fin N)) (z : Bool)
    (hmono : ∀ i ∈ R, ∀ j ∈ B, C j i = z)
    {s : ℕ} (hsR : s ≤ R.card) (hst : s ≤ t) :
    (B.card : ℝ) ≤ (1 + ε) / (2 : ℝ) ^ s * N := by
  classical
  obtain ⟨J, hJR, hJcard⟩ := Finset.exists_subset_card_eq hsR
  have hsub : B ⊆ Finset.univ.filter
      (fun j : Fin N => ∀ i ∈ J, C j i = (fun _ => z) i) := by
    intro j hj
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    intro i hi
    exact hmono i (hJR hi) j hj
  have hcount : (B.card : ℝ) ≤ ((Finset.univ.filter
      (fun j : Fin N => ∀ i ∈ J, C j i = (fun _ => z) i)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hbound := balancedPattern_card_le hC J (by omega) (fun _ => z)
  rw [hJcard] at hbound
  exact hcount.trans hbound

/-- Heavy-path row arithmetic at the exact `2^a+1` threshold. -/
theorem heavyRows_ge_bobBits_add_one {a u v r : ℕ}
    (hrow : 2 ^ a + 1 ≤ 2 ^ u * r) (hbits : u + v ≤ a + 1) :
    v + 1 ≤ r := by
  by_cases hua : u ≤ a
  · have hpow : 2 ^ a = 2 ^ u * 2 ^ (a - u) := by
      rw [← pow_add]
      congr 1
      omega
    have hltmul : 2 ^ u * 2 ^ (a - u) < 2 ^ u * r := by
      rw [← hpow]
      exact lt_of_lt_of_le (Nat.lt_succ_self _) hrow
    have hlt : 2 ^ (a - u) < r := Nat.lt_of_mul_lt_mul_left hltmul
    have hk : (a - u) + 1 ≤ 2 ^ (a - u) :=
      Nat.succ_le_of_lt Nat.lt_two_pow_self
    omega
  · have hv : v = 0 := by omega
    have hr : 0 < r := by
      by_contra h
      have : r = 0 := by omega
      simp [this] at hrow
    omega

/-- The current paper's strict indexing threshold after column loss.

No separate sign assumption on `ε` is needed: positive family length is
part of balancedness, and the displayed strict retained-label threshold is
exactly what the contradiction consumes. In the paper `ε=d^(-8)>0`.
-/
theorem indexingThreshold {a N t : ℕ}
    (C : Fin N → Fin (2 ^ a + 1) → Bool) {ε : ℝ}
    (hC : NPCC.IsBalancedFamily t C ε) (ht : a + 2 ≤ t)
    (L : Finset (Fin N)) (hL : (1 + ε) * N / 2 < (L.card : ℝ)) :
    a + 2 ≤ D (fun i (j : {j // j ∈ L}) => C j.val i) := by
  classical
  by_contra hnot
  have hD : D (fun i (j : {j // j ∈ L}) => C j.val i) ≤ a + 1 := by omega
  obtain ⟨R, B, u, v, z, hbits, hrow, hcol, hmono⟩ :=
    NPCC.exists_mono_rectangle_of_D_le _ hD
  have hrowNat : 2 ^ a + 1 ≤ 2 ^ u * R.card := by simpa using hrow
  have hR : v + 1 ≤ R.card := heavyRows_ge_bobBits_add_one hrowNat hbits
  let B' : Finset (Fin N) := B.image Subtype.val
  have hBcard : B'.card = B.card :=
    Finset.card_image_of_injective _ Subtype.val_injective
  have hmono' : ∀ i ∈ R, ∀ j ∈ B', C j i = z := by
    intro i hi j hj
    obtain ⟨j', hj', rfl⟩ := Finset.mem_image.mp hj
    exact hmono i hi j' hj'
  have hbound := monochromaticRectangle_card_le hC R B' z hmono' hR (by omega)
  rw [hBcard] at hbound
  have hcolNat : L.card ≤ 2 ^ v * B.card := by simpa using hcol
  have hcolReal : (L.card : ℝ) ≤ (2 : ℝ) ^ v * B.card := by
    exact_mod_cast hcolNat
  have hchain : (L.card : ℝ) ≤ (1 + ε) * N / 2 := by
    calc
      (L.card : ℝ) ≤ (2 : ℝ) ^ v * B.card := hcolReal
      _ ≤ (2 : ℝ) ^ v * ((1 + ε) / (2 : ℝ) ^ (v + 1) * N) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = (1 + ε) * N / 2 := by
        rw [pow_succ]
        field_simp [show (2 : ℝ) ^ v ≠ 0 by positivity]
  exact (not_lt_of_ge hchain) hL

/-- Any Boolean matrix with at most `2^a` labelled rows has a public-output
protocol of cost at most `a+1`. This applies to every column restriction of
the indexing construction, with no balancedness assumption. -/
theorem indexingUpper_of_card_le {A B : Type*} [Fintype A] [Fintype B]
    (g : A → B → Bool) (a : ℕ) (hA : Fintype.card A ≤ 2 ^ a) :
    D g ≤ a + 1 := by
  classical
  have hcard : Fintype.card A ≤ Fintype.card (Fin (2 ^ a)) := by simpa using hA
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  apply NPCC.comp_le_of_row_types_succ g a e
  intro x y hxy
  rw [e.injective hxy]

/-- The upper half of `lem:exact-index-threshold`, with explicit sets of
retained coordinates and column labels. -/
theorem indexingUpper {q N a : ℕ} (C : Fin N → Fin q → Bool)
    (R : Finset (Fin q)) (L : Finset (Fin N)) (hR : R.card ≤ 2 ^ a) :
    D (fun (i : {i // i ∈ R}) (j : {j // j ∈ L}) => C j.val i.val) ≤ a + 1 := by
  apply indexingUpper_of_card_le _ a
  simpa using hR

end EthInapproximability.CurrentPaper.ExactIndexing
