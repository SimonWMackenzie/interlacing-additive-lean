import CurrentAdditive.SmallBiasRectangle
/-!
# V27 small-bias escape from an actual alternating lookup protocol

Source: v27 `sections/07a-small-bias.tex`, `yao:small-bias-escape` and
`yao:cut-inequality`. All retained probability is under the original law.
The suffix catalogue is obtained from the actual cut protocol after the
evaluation-preserving canonical normalization of `Paper2.Yao`.
-/

namespace CurrentAdditive.SmallBias

open Paper2.Yao Workspace.Types.Protocol

variable {Ω Λ : Type*} [Fintype Λ]

private theorem cut_numeric (d k : ℕ) (hk : d + 1 ≤ k) :
    (2 ^ d : ℝ) * ((1 / 2 : ℝ) ^ k + (1 / 2 : ℝ) ^ (d + 4)) < 1 := by
  have hle : (1 / 2 : ℝ) ^ k ≤ (1 / 2 : ℝ) ^ (d + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
  have hcancel (r : ℕ) :
      (2 ^ d : ℝ) * (1 / 2 : ℝ) ^ (d + r) = (1 / 2 : ℝ) ^ r := by
    rw [pow_add, ← mul_assoc]
    have hunit : (2 ^ d : ℝ) * (1 / 2 : ℝ) ^ d = 1 := by
      rw [← mul_pow]
      norm_num
    rw [hunit, one_mul]
  have hfirst : (2 ^ d : ℝ) * (1 / 2 : ℝ) ^ k ≤ 1 / 2 := by
    calc
      _ ≤ (2 ^ d : ℝ) * (1 / 2 : ℝ) ^ (d + 1) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
      _ = 1 / 2 := by rw [hcancel 1]; norm_num
  have hsecond : (2 ^ d : ℝ) * (1 / 2 : ℝ) ^ (d + 4) = 1 / 16 := by
    rw [hcancel 4]
    norm_num
  nlinarith

/-- The actual suffix at any cut, together with original-law mass and its
normalized canonical catalogue. The numerical threshold is kept explicit
to make this lemma reusable with different source parameter calculations. -/
theorem no_short_lookup_actual_cut
    (μ : Paper2.FiniteLaw Λ) (word : Λ → Ω → Bool)
    (ε : ℝ) (hε : 0 ≤ ε) (hμ : IsSmallBiased μ word ε)
    (X : Finset Ω) (t i h k : ℕ) (ht : 1 ≤ t) (hh : 1 ≤ h)
    (hk : 1 ≤ k) (hrows : 2 ^ i * (k - 1) < X.card)
    (P : Protocol Ω Λ Bool)
    (hc : IsComplete P ((2 * t - 1) + 2 * (i + h)))
    (ha : Alternates .alice P)
    (σ : ResponseStrategy t)
    (hσ : ∀ x ∈ X, earlyStrategy t P x = σ)
    (hlookup : ∀ x ∈ X, ∀ ℓ, P.eval x ℓ = word ℓ x)
    (hnum : (2 ^ (t - 1 + i) : ℝ) * (2 ^ (2 ^ h - 1) : ℝ) *
      ((1 / 2 : ℝ) ^ k + ε) < 1) : False := by
  classical
  obtain ⟨X', Y', Q, hX', -, hcard, hmass, hcQ, haQ, heval⟩ :=
    actual_cut_rectangle μ t i h ht P hc ha X (fun _ => True) σ hσ
  have hk' : k ≤ X'.card := by
    by_contra hnot
    have hless : X'.card ≤ k - 1 := by omega
    have hm := Nat.mul_le_mul_left (2 ^ i) hless
    omega
  obtain ⟨I, hI, hIcard⟩ := Finset.exists_subset_card_eq hk'
  let Qn := normalizeTree (2 * h) Q
  have hcQn : IsComplete Qn (2 * h) := normalizeTree_isComplete _ _ hcQ
  have haQn : Alternates .bob Qn := normalizeTree_alternates _ _ .bob hcQ haQ
  have hnQn : CanonicalLastLeaves (2 * h) Qn := by
    have heq : (2 * h - 1) + 1 = 2 * h := by omega
    simpa only [heq] using normalizeTree_canonical (2 * h - 1) Q (by simpa only [heq] using hcQ)
  let F := columnCatalogue Qn
  have hF : F.card ≤ 2 ^ (2 ^ h - 1) :=
    (suffix_catalogue_bounds (X := Ω) (Y := Λ) h).2 Qn hcQn haQn (Or.inr hnQn)
  have hcover : ∀ ℓ, Y' ℓ → ∃ z ∈ F, ∀ j ∈ I, word ℓ j = z j := by
    intro ℓ hℓ
    refine ⟨fun j => Qn.eval j ℓ, actualColumn_mem_catalogue Qn ℓ, ?_⟩
    intro j hj
    have hjX' : j ∈ X' := hI hj
    have hjX : j ∈ X := hX' hjX'
    exact ((hlookup j hjX ℓ).symm).trans
      ((heval j hjX' ℓ hℓ).trans (normalizeTree_eval _ _ hcQ j ℓ).symm)
  have hcovered : μ.prob Y' ≤ (F.card : ℝ) * ((1 / 2 : ℝ) ^ I.card + ε) := by
    calc
      _ ≤ μ.prob (fun ℓ => ∃ z ∈ F, ∀ j ∈ I, word ℓ j = z j) := μ.prob_mono hcover
      _ ≤ _ := patterns_prob_le μ word ε hε hμ I F
  have hFreal : (F.card : ℝ) ≤ (2 ^ (2 ^ h - 1) : ℝ) := by exact_mod_cast hF
  have hfactor : 0 ≤ (1 / 2 : ℝ) ^ I.card + ε := by positivity
  have hbound : μ.prob Y' ≤
      (2 ^ (2 ^ h - 1) : ℝ) * ((1 / 2 : ℝ) ^ k + ε) := by
    rw [hIcard] at hcovered
    rw [hIcard] at hfactor
    exact hcovered.trans (mul_le_mul_of_nonneg_right hFreal hfactor)
  have htrue : μ.prob (fun _ : Λ => True) = 1 := μ.prob_true
  rw [htrue] at hmass
  have hm' := mul_le_mul_of_nonneg_left hbound
    (show 0 ≤ (2 ^ (t - 1 + i) : ℝ) by positivity)
  nlinarith [hm']

#print axioms CurrentAdditive.SmallBias.no_short_lookup_actual_cut

/-- The source feasibility inequality forces a nonempty Bob--Alice suffix.
In fact it leaves at least `t+2` pairs, so the excess `δQ` is an integer
power of two. Maximality of `i` is unnecessary for this exclusion theorem. -/
theorem feasible_cut_suffix (b t i h : ℕ) (ht : 4 ≤ t)
    (ha : i + h = b + 2 * t - 2)
    (hf : 2 ^ i * (t + i - 2) ≤ 2 ^ (t + b - 3)) : t + 2 ≤ h := by
  have htwo : 2 ≤ t + i - 2 := by omega
  have hpow : 2 ^ (i + 1) ≤ 2 ^ (t + b - 3) := by
    rw [pow_succ]
    have hm := Nat.mul_le_mul_left (2 ^ i) htwo
    omega
  have hexp : i + 1 ≤ t + b - 3 :=
    (pow_le_pow_iff_right₀ (by decide : (1 : ℕ) < 2)).mp hpow
  omega

/-- The literal v27 stopping-rule parameters. The only cut assumption is
feasibility; the source's maximal feasible choice is a special case. -/
theorem no_short_lookup_v27
    (μ : Paper2.FiniteLaw Λ) (word : Λ → Ω → Bool)
    (b t i h : ℕ) (ht : 4 ≤ t)
    (ha : i + h = b + 2 * t - 2)
    (hf : 2 ^ i * (t + i - 2) ≤ 2 ^ (t + b - 3))
    (X : Finset Ω)
    (hX : 2 ^ (b + 2 * t - 2) + 2 ^ (t + b - 3) + 1 ≤ X.card)
    (hμ : IsSmallBiased μ word ((1 / 2 : ℝ) ^ (2 ^ h + t + i + 2)))
    (P : Protocol Ω Λ Bool)
    (hc : IsComplete P ((2 * t - 1) + 2 * (b + 2 * t - 2)))
    (hP : Alternates .alice P)
    (σ : ResponseStrategy t)
    (hσ : ∀ x ∈ X, earlyStrategy t P x = σ)
    (hlookup : ∀ x ∈ X, ∀ ℓ, P.eval x ℓ = word ℓ x) : False := by
  let Q := 2 ^ h
  let r := 2 ^ (h - t - 1)
  let k := Q + r + 1
  let d := Q + t + i - 2
  have hh : t + 2 ≤ h := feasible_cut_suffix b t i h ht ha hf
  have hsum : i + (h - t - 1) = t + b - 3 := by omega
  have hpower : 2 ^ i * Q = 2 ^ (b + 2 * t - 2) := by
    dsimp only [Q]
    rw [← pow_add, ha]
  have hsurplus : 2 ^ i * r = 2 ^ (t + b - 3) := by
    dsimp only [r]
    rw [← pow_add, hsum]
  have hr : t + i - 2 ≤ r := by
    have hm : 0 < 2 ^ i := by positivity
    exact Nat.le_of_mul_le_mul_left (by simpa only [hsurplus] using hf) hm
  have hk : 1 ≤ k := by simp [k]
  have hrows : 2 ^ i * (k - 1) < X.card := by
    have hident : 2 ^ i * (k - 1) =
        2 ^ (b + 2 * t - 2) + 2 ^ (t + b - 3) := by
      dsimp only [k]
      have heq : Q + r + 1 - 1 = Q + r := by omega
      rw [heq, mul_add, hpower, hsurplus]
    omega
  have hdk : d + 1 ≤ k := by dsimp [d, k]; omega
  have heps : d + 4 = Q + t + i + 2 := by
    have hq : 1 ≤ Q := by dsimp [Q]; exact Nat.one_le_pow h 2 (by decide)
    dsimp only [d]
    omega
  have hdexp : (t - 1 + i) + (Q - 1) = d := by
    dsimp [d, Q]
    have hq : 1 ≤ 2 ^ h := Nat.one_le_pow h 2 (by decide)
    omega
  have hnum : (2 ^ (t - 1 + i) : ℝ) * (2 ^ (Q - 1) : ℝ) *
      ((1 / 2 : ℝ) ^ k + (1 / 2 : ℝ) ^ (Q + t + i + 2)) < 1 := by
    calc
      _ = (2 ^ d : ℝ) * ((1 / 2 : ℝ) ^ k + (1 / 2 : ℝ) ^ (d + 4)) := by
        rw [← pow_add, hdexp, heps]
      _ < 1 := cut_numeric d k hdk
  have hc' : IsComplete P ((2 * t - 1) + 2 * (i + h)) := by
    simpa only [ha] using hc
  exact no_short_lookup_actual_cut μ word _ (by positivity) hμ X t i h k
    (by omega) (by omega) hk hrows P hc' hP σ hσ hlookup
    (by simpa only [Q] using hnum)

#print axioms CurrentAdditive.SmallBias.feasible_cut_suffix
#print axioms CurrentAdditive.SmallBias.no_short_lookup_v27

end CurrentAdditive.SmallBias
