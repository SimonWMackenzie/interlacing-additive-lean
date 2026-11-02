import CurrentAdditive.SmallBiasBoundedCost

/-!
# The selected v37 general alternating lookup obstruction

Source: `papers/randomized-additive-hardness/versions/v37/source/sections/alternation.tex`,
`yao:small-bias-escape` (lines 213-261). The selected paper's row set is
represented by the finite indexed set `J`; the actual protocol has an early
response strategy common to all rows, and every probability uses the original
labelled finite law. The last-output normalization is performed by the imported
actual-cut theorem, after the common prefix is removed.
-/

namespace CurrentAdditive.SmallBias

open Paper2.Yao Workspace.Types.Protocol

variable {Ω Λ : Type*} [Fintype Λ]

/-- The exact v37 array-law premise, measured under the original labelled law
for every requested coordinate set and pattern. -/
def HasPatternBound (μ : Paper2.FiniteLaw Λ) (word : Λ → Ω → Bool)
    (ε : ℝ) : Prop :=
  ∀ (I : Finset Ω) (z : Ω → Bool),
    μ.prob (fun ℓ => ∀ j ∈ I, word ℓ j = z j) ≤
      (1 / 2 : ℝ) ^ I.card + ε

/-- The existing finite-field small-bias interface supplies the exact pattern
premise when an application has already constructed such a source. The lookup
theorem itself does not assume this stronger Fourier property. -/
theorem HasPatternBound.ofSmallBias
    (μ : Paper2.FiniteLaw Λ) (word : Λ → Ω → Bool) (ε : ℝ)
    (hε : 0 ≤ ε) (hμ : IsSmallBiased μ word ε) :
    HasPatternBound μ word ε := by
  intro I z
  exact pattern_prob_le μ word ε hε hμ I z

private theorem patterns_prob_le_direct
    (μ : Paper2.FiniteLaw Λ) (word : Λ → Ω → Bool) (ε : ℝ)
    (hpattern : HasPatternBound μ word ε)
    (I : Finset Ω) (F : Finset (Ω → Bool)) :
    μ.prob (fun ℓ => ∃ z ∈ F, ∀ j ∈ I, word ℓ j = z j) ≤
      (F.card : ℝ) * ((1 / 2 : ℝ) ^ I.card + ε) := by
  calc
    _ ≤ ∑ z ∈ F, μ.prob (fun ℓ => ∀ j ∈ I, word ℓ j = z j) :=
      μ.prob_exists_le_sum F _
    _ ≤ ∑ _z ∈ F, ((1 / 2 : ℝ) ^ I.card + ε) := by
      apply Finset.sum_le_sum
      intro z _
      exact hpattern I z
    _ = (F.card : ℝ) * ((1 / 2 : ℝ) ^ I.card + ε) := by simp [mul_add]

/-- The actual v37 cut of one protocol. This is the generic rectangle and
suffix-catalogue argument, with the paper's pattern-law premise rather than
the stronger Fourier small-bias premise used in the v27 specialization. -/
private theorem no_short_lookup_actual_cut_pattern
    (μ : Paper2.FiniteLaw Λ) (word : Λ → Ω → Bool)
    (ε : ℝ) (hε : 0 ≤ ε) (hpattern : HasPatternBound μ word ε)
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
    simpa only [heq] using normalizeTree_canonical (2 * h - 1) Q
      (by simpa only [heq] using hcQ)
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
      _ ≤ _ := patterns_prob_le_direct μ word ε hpattern I F
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

private theorem v37_numeric
    (m t i h : ℕ) (ht : 1 ≤ t) (hh : 1 ≤ h)
    (hm : m = t + i + h)
    (hQlo : m ≤ 2 ^ h) (hQhi : 2 ^ h ≤ 2 * m) :
    (2 ^ (t - 1 + i) : ℝ) * (2 ^ (2 ^ h - 1) : ℝ) *
      ((1 / 2 : ℝ) ^ (2 * (2 ^ h)) + (1 / 2 : ℝ) ^ (4 * m)) < 1 := by
  let Q := 2 ^ h
  let d := (t - 1 + i) + (Q - 1)
  have hQ : 1 ≤ Q := by dsimp [Q]; exact Nat.one_le_pow h 2 (by decide)
  have hA : t - 1 + i ≤ Q - 1 := by omega
  have hd1 : d + 2 ≤ 2 * Q := by dsimp [d]; omega
  have hd2 : d + 2 ≤ 4 * m := by omega
  have hpow1 : (1 / 2 : ℝ) ^ (2 * Q) ≤ (1 / 2 : ℝ) ^ (d + 2) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hd1
  have hpow2 : (1 / 2 : ℝ) ^ (4 * m) ≤ (1 / 2 : ℝ) ^ (d + 2) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hd2
  have hcancel : (2 ^ d : ℝ) * (1 / 2 : ℝ) ^ (d + 2) = 1 / 4 := by
    have hp : (1 / 2 : ℝ) ^ (d + 2) =
        (1 / 2 : ℝ) ^ d * (1 / 2 : ℝ) ^ 2 := pow_add _ _ _
    rw [hp, ← mul_assoc, ← mul_pow]
    norm_num
  have hfact : (2 ^ (t - 1 + i) : ℝ) * (2 ^ (Q - 1) : ℝ) = 2 ^ d := by
    dsimp [d]
    rw [← pow_add]
  change (2 ^ (t - 1 + i) : ℝ) * (2 ^ (Q - 1) : ℝ) *
    ((1 / 2 : ℝ) ^ (2 * Q) + (1 / 2 : ℝ) ^ (4 * m)) < 1
  rw [hfact]
  have hnonneg : 0 ≤ (2 ^ d : ℝ) := by positivity
  calc
    (2 ^ d : ℝ) * ((1 / 2 : ℝ) ^ (2 * Q) + (1 / 2 : ℝ) ^ (4 * m))
        ≤ (2 ^ d : ℝ) * ((1 / 2 : ℝ) ^ (d + 2) + (1 / 2 : ℝ) ^ (d + 2)) := by
          exact mul_le_mul_of_nonneg_left (add_le_add hpow1 hpow2) hnonneg
    _ = 1 / 2 := by rw [mul_add, hcancel]; norm_num
    _ < 1 := by norm_num

/-- V37's general lookup lemma, for a complete actual Alice-first protocol.
`m` is the total number of Alice turns and `t` is the number of common early
turns. The proof uses one fixed original column law, including after a cut. -/
theorem no_short_lookup_v37_complete
    (μ : Paper2.FiniteLaw Λ) (word : Λ → Ω → Bool)
    (m t : ℕ) (ht : 1 ≤ t) (hm : t < m)
    (hlog : Nat.clog 2 m ≤ m - t)
    (J : Finset Ω) (hJ : 2 ^ (m - t + 1) ≤ J.card)
    (hpattern : HasPatternBound μ word ((1 / 2 : ℝ) ^ (4 * m)))
    (P : Protocol Ω Λ Bool) (hc : IsComplete P (2 * m - 1))
    (ha : Alternates .alice P) (σ : ResponseStrategy t)
    (hσ : ∀ x ∈ J, earlyStrategy t P x = σ)
    (hlookup : ∀ x ∈ J, ∀ ℓ, P.eval x ℓ = word ℓ x) : False := by
  let h := Nat.clog 2 m
  let i := m - t - h
  let Q := 2 ^ h
  let k := 2 * Q
  have hh : 1 ≤ h := Nat.clog_pos (by decide) (by omega)
  have hi : m = t + i + h := by dsimp [i, h] at *; omega
  have hQlo : m ≤ Q := by
    dsimp [Q, h]
    exact Nat.le_pow_clog (by decide) m
  have hQhi : Q ≤ 2 * m := by
    have hp : 2 ^ (h - 1) < m := by
      simpa only [h, Nat.pred_eq_sub_one] using
        (Nat.pow_pred_clog_lt_self (by decide : 1 < (2 : ℕ)) (by omega : 1 < m))
    have he : h = (h - 1) + 1 := by omega
    have hQeq : Q = 2 * 2 ^ (h - 1) := by
      calc
        Q = 2 ^ h := rfl
        _ = 2 ^ ((h - 1) + 1) := congrArg (fun z : ℕ => 2 ^ z) he
        _ = 2 * 2 ^ (h - 1) := by rw [pow_succ]; omega
    omega
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hdim : 2 ^ (m - t + 1) = 2 ^ i * k := by
    have he : m - t + 1 = i + (h + 1) := by omega
    calc
      2 ^ (m - t + 1) = 2 ^ (i + (h + 1)) := by rw [he]
      _ = 2 ^ i * 2 ^ (h + 1) := by rw [pow_add]
      _ = 2 ^ i * k := by dsimp [k, Q]; rw [pow_succ]; ring
  have hrows : 2 ^ i * (k - 1) < J.card := by
    have hlt : k - 1 < k := by omega
    have hmul : 2 ^ i * (k - 1) < 2 ^ i * k :=
      Nat.mul_lt_mul_of_pos_left hlt (by positivity)
    rw [← hdim] at hmul
    exact hmul.trans_le hJ
  have hc' : IsComplete P ((2 * t - 1) + 2 * (i + h)) := by
    have he : 2 * m - 1 = (2 * t - 1) + 2 * (i + h) := by omega
    simpa only [he] using hc
  have hnum := v37_numeric m t i h ht hh hi hQlo hQhi
  exact no_short_lookup_actual_cut_pattern μ word _ (by positivity) hpattern J t i h k
    ht hh hk hrows P hc' ha σ hσ hlookup (by simpa only [k, Q] using hnum)

/-- V37's source lemma for any actual Alice-first protocol of cost at most
`2*m-1`. Normalizing to full odd depth preserves the first `t` complete
response strategies and the value of the protocol on every input. -/
theorem no_short_lookup_v37_at_bound
    (μ : Paper2.FiniteLaw Λ) (word : Λ → Ω → Bool)
    (m t : ℕ) (ht : 1 ≤ t) (hm : t < m)
    (hlog : Nat.clog 2 m ≤ m - t)
    (J : Finset Ω) (hJ : 2 ^ (m - t + 1) ≤ J.card)
    (hpattern : HasPatternBound μ word ((1 / 2 : ℝ) ^ (4 * m)))
    (P : Protocol Ω Λ Bool) (hcost : P.cost ≤ 2 * m - 1)
    (ha : Alternates .alice P) (σ : ResponseStrategy t)
    (hσ : ∀ x ∈ J, earlyStrategy t P x = σ)
    (hlookup : ∀ x ∈ J, ∀ ℓ, P.eval x ℓ = word ℓ x) : False := by
  let r := m - 1
  have hr : 2 * m - 1 = 2 * r + 1 := by dsimp [r]; omega
  have hguard : 2 * t < 2 * r + 1 := by dsimp [r]; omega
  obtain ⟨Q, hcQ, haQ, _, hsQ, heQ⟩ :=
    exists_normalized_preserving_strategy t r P ha (by simpa only [hr] using hcost) hguard
  have hcQ' : IsComplete Q (2 * m - 1) := by simpa only [hr] using hcQ
  exact no_short_lookup_v37_complete μ word m t ht hm hlog J hJ hpattern Q hcQ' haQ σ
    (by intro x hx; exact (hsQ x).trans (hσ x hx))
    (by intro x hx ℓ; exact (heQ x ℓ).trans (hlookup x hx ℓ))

/-- The literal v37 form allows any original-law pattern error at most
`2^(-4m)`. It is applied to actual, possibly repeated, array labels. -/
theorem no_short_lookup_v37
    (μ : Paper2.FiniteLaw Λ) (word : Λ → Ω → Bool)
    (m t : ℕ) (ht : 1 ≤ t) (hm : t < m)
    (hlog : Nat.clog 2 m ≤ m - t)
    (J : Finset Ω) (hJ : 2 ^ (m - t + 1) ≤ J.card)
    (ε : ℝ) (hε : ε ≤ (1 / 2 : ℝ) ^ (4 * m))
    (hpattern : HasPatternBound μ word ε)
    (P : Protocol Ω Λ Bool) (hcost : P.cost ≤ 2 * m - 1)
    (ha : Alternates .alice P) (σ : ResponseStrategy t)
    (hσ : ∀ x ∈ J, earlyStrategy t P x = σ)
    (hlookup : ∀ x ∈ J, ∀ ℓ, P.eval x ℓ = word ℓ x) : False := by
  have hbound : HasPatternBound μ word ((1 / 2 : ℝ) ^ (4 * m)) := by
    intro I z
    have hp := hpattern I z
    linarith
  exact no_short_lookup_v37_at_bound μ word m t ht hm hlog J hJ hbound
    P hcost ha σ hσ hlookup

#print axioms CurrentAdditive.SmallBias.no_short_lookup_v37_complete
#print axioms CurrentAdditive.SmallBias.no_short_lookup_v37_at_bound
#print axioms CurrentAdditive.SmallBias.no_short_lookup_v37
#print axioms CurrentAdditive.SmallBias.HasPatternBound.ofSmallBias

end CurrentAdditive.SmallBias
