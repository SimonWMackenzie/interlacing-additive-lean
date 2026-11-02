import CurrentAdditive.V38Public

/-! Private v42 source-trace packet. Author-supplied source SHA256 is pinned in
`block_inventory.json`; selected source `yao:small-bias-escape` lines 3345--3385.
The cut, column weights, normalization, and suffix catalogue are all actual
protocol objects. No old lower-bound endpoint is used by this proof. -/

namespace CurrentAdditive.SmallBias.V42
open Paper2.Yao Workspace.Types.Protocol
open CurrentAdditive.SmallBias
variable {Ω Λ : Type*} [Fintype Λ]

theorem patterns_prob_le_direct
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
theorem no_short_lookup_actual_cut_pattern
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

theorem numeric_pattern_gap
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

theorem no_short_lookup_complete
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
  have hnum := numeric_pattern_gap m t i h ht hh hi hQlo hQhi
  exact no_short_lookup_actual_cut_pattern μ word _ (by positivity) hpattern J t i h k
    ht hh hk hrows P hc' ha σ hσ hlookup (by simpa only [k, Q] using hnum)

/-- V37's source lemma for any actual Alice-first protocol of cost at most
`2*m-1`. Normalizing to full odd depth preserves the first `t` complete
response strategies and the value of the protocol on every input. -/
theorem no_short_lookup_at_bound
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
  exact no_short_lookup_complete μ word m t ht hm hlog J hJ hpattern Q hcQ' haQ σ
    (by intro x hx; exact (hsQ x).trans (hσ x hx))
    (by intro x hx ℓ; exact (heQ x ℓ).trans (hlookup x hx ℓ))

/-- The literal v37 form allows any original-law pattern error at most
`2^(-4m)`. It is applied to actual, possibly repeated, array labels. -/
theorem no_short_lookup
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
  exact no_short_lookup_at_bound μ word m t ht hm hlog J hJ hbound
    P hcost ha σ hσ hlookup


/-- The elementary inequality used in v42's cutoff calculation, including
its boundary case m=2,t=1. -/
theorem twice_le_pow (n : ℕ) (hn : 1 ≤ n) : 2*n ≤ 2^n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      rw [pow_succ]
      omega

/-- The new paper hypothesis m≥2t≥2 supplies exactly the cut position h≤m−t.
No asymptotic or source-specific guard is assumed. -/
theorem log_guard (m t : ℕ) (hmt : 2*t ≤ m) (htwo : 2 ≤ 2*t) :
    Nat.clog 2 m ≤ m-t := by
  apply (Nat.clog_le_iff_le_pow (by decide)).2
  have hrem : 1 ≤ m-t := by omega
  exact (show m ≤ 2*(m-t) by omega).trans (twice_le_pow (m-t) hrem)

/-- Literal v42 lookup obstruction for all integers represented by natural
parameters. Its premise m≥2t≥2 is the source's new premise; arrays remain
under their one original labelled law throughout the argument. -/
theorem no_short_lookup_v42
    (μ : Paper2.FiniteLaw Λ) (word : Λ → Ω → Bool)
    (m t : ℕ) (hmt : 2*t ≤ m) (htwo : 2 ≤ 2*t)
    (J : Finset Ω) (hJ : 2 ^ (m - t + 1) ≤ J.card)
    (ε : ℝ) (hε : ε ≤ (1 / 2 : ℝ) ^ (4 * m))
    (hpattern : HasPatternBound μ word ε)
    (P : Protocol Ω Λ Bool) (hcost : P.cost ≤ 2 * m - 1)
    (ha : Alternates .alice P) (σ : ResponseStrategy t)
    (hσ : ∀ x ∈ J, earlyStrategy t P x = σ)
    (hlookup : ∀ x ∈ J, ∀ ℓ, P.eval x ℓ = word ℓ x) : False := by
  exact no_short_lookup μ word m t (by omega) (by omega)
    (log_guard m t hmt htwo) J hJ ε hε hpattern P hcost ha σ hσ hlookup

#print axioms CurrentAdditive.SmallBias.V42.log_guard
#print axioms CurrentAdditive.SmallBias.V42.no_short_lookup_v42
open Paper2.YaoLookup Paper2.YaoLowerBound
theorem no_implies_strategy_colouring
    {V E : Type*} (t : ℕ)
    (edges : E → Fin (2 ^ t * 2 ^ t) ↪ V)
    (hno : ∀ colour : V → Fin (2 ^ (2 ^ t)),
      ∃ e c, ∀ i, colour (edges e i) = c) :
    ∀ colour : V → Fin (2 ^ (2 ^ t - 1)),
      ∃ e c, ∀ i, colour (edges e i) = c := by
  intro colour
  have hle : 2 ^ (2 ^ t - 1) ≤ 2 ^ (2 ^ t) :=
    Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  let f : Fin (2 ^ (2 ^ t - 1)) ↪ Fin (2 ^ (2 ^ t)) := Fin.castLEEmb hle
  obtain ⟨e, c, hc⟩ := hno (fun v => f (colour v))
  let i0 : Fin (2 ^ t * 2 ^ t) := ⟨0, by positivity⟩
  refine ⟨e, colour (edges e i0), ?_⟩
  intro i
  exact f.injective ((hc i).trans (hc i0).symm)

theorem lower_bound_matrix
    {V E : Type*} [Fintype V] {b t labels samples : ℕ}
    (ht : 4 ≤ t) (hlabels : 0 < labels)
    (edges : E → Fin (2 ^ t * 2 ^ t) ↪ V)
    (index : E ↪ Fin (2 ^ b))
    (hno : ∀ colour : V → Fin (2 ^ (2 ^ t)),
      ∃ e c, ∀ i, colour (edges e i) = c)
    (C : Fin labels → Fin (2 ^ (t - 1)) → Fin (2 ^ b))
    (hC : selectorGood (2 ^ (t - 1)) (2 ^ b) (2 ^ (2 ^ t - 1)) labels C)
    (W : Fin samples → Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t) → Bool)
    (μ : Paper2.FiniteLaw (Fin samples))
    (hpattern : HasPatternBound μ W
      ((1 / 2 : ℝ) ^ (4 * (b + 3 * t)))) :
    (2 * b + 4 * t + 2) + 2 * t - 8 ≤
      Dalt .alice (matrixV38 (placeEdges edges index) C W) := by
  classical
  obtain ⟨P, hcost, hP⟩ := exists_optimal .alice
    (matrixV38 (placeEdges edges index) C W)
  by_contra h
  have hp : P.cost ≤ 2 * (b + 3 * t - 3) - 1 := by omega
  obtain ⟨e, σ, _, hσ, hsize⟩ :=
    LowerBound.exists_monochromatic_dominantClasses t P.toProtocol edges
      (no_implies_strategy_colouring t edges hno)
  let Z : Fin (2 ^ t * 2 ^ t) → Finset (Fin labels) :=
    fun i => LowerBound.dominantClass t P.toProtocol (edges e i)
  have hproj (i : Fin (2 ^ t * 2 ^ t)) :
      (3 : ℝ) / (4 * (2 : ℝ) ^ (2 ^ t - 1)) ≤
        ∏ g, ((Restriction.addresses C g Z i).card : ℝ) / (2 : ℝ) ^ b := by
    simpa only [Restriction.addresses, Nat.cast_pow, Nat.cast_ofNat] using
      retained_projection_product (2 ^ (2 ^ t - 1)) (pow_pos (by decide) _)
        hlabels C hC (Z i) (hsize i)
  obtain ⟨g, hg⟩ := exists_large_projection t b ht
    (fun i g => (Restriction.addresses C g Z i).card) hproj
  let Q := Restriction.protocol (edges e) C g (index e) Z P
  let f : Restriction.Rows C g Z → Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t) :=
    fun p => (p.2.val, p.1)
  have hf : Function.Injective f := by
    intro p r he
    cases p with
    | mk i a =>
      cases r with
      | mk j c =>
        have hi : i = j := congrArg Prod.snd he
        have ha : a.val = c.val := congrArg Prod.fst he
        cases hi
        cases Subtype.ext ha
        rfl
  have hrow : 2 ^ ((b + 3 * t - 3) - t + 1) ≤
      (Finset.univ : Finset (Restriction.Rows C g Z)).card := by
    rw [Finset.card_univ, Restriction.row_card]
    exact (v37_payload_minimum b t ht).trans hg
  have hpatternRows : HasPatternBound μ (fun ℓ p => W ℓ (f p))
      ((1 / 2 : ℝ) ^ (4 * (b + 3 * t))) :=
    HasPatternBound.comp_injective μ W _ hpattern f hf
  have hQcost : Q.toProtocol.cost ≤ 2 * (b + 3 * t - 3) - 1 := by
    change (Restriction.protocol (edges e) C g (index e) Z P).cost ≤ _
    simpa only [Restriction.protocol_cost] using hp
  have hQstrategy : ∀ p,
      earlyStrategy t Q.toProtocol p = σ :=
    Restriction.protocol_earlyStrategy t (edges e) C g (index e) Z P σ hσ
  have hQlookup : ∀ p ℓ, Q.toProtocol.eval p ℓ = W ℓ (f p) := by
    intro p ℓ
    have hcompute := Restriction.protocol_computes
      (placeEdges edges index) C (v38WithZero W)
      (index e) (edges e) (placeEdges_real edges index e) g Z P
      (by simpa only [matrixV38] using hP)
    exact (hcompute p ℓ).trans (by
      simp [f, Restriction.payloadMap])
  exact no_short_lookup_v42 μ (fun ℓ p => W ℓ (f p))
    (b + 3 * t - 3) t (by omega) (by omega)
    Finset.univ hrow _ (v38_bias_le_lookup b t)
    hpatternRows Q.toProtocol hQcost Q.alternates σ
    (by intro p _; exact hQstrategy p)
    (by intro p _ ℓ; exact hQlookup p ℓ)


/-- The complete address list used in the new source, without any externally
supplied selector event. Both the table and its array weights are the actual
objects used in the restriction proof above. -/
theorem lower_bound_complete_addresses
    {V E : Type*} [Fintype V] {b t samples : ℕ}
    (ht : 4 ≤ t)
    (edges : E → Fin (2 ^ t * 2 ^ t) ↪ V)
    (index : E ↪ Fin (2 ^ b))
    (hno : ∀ colour : V → Fin (2 ^ (2 ^ t)),
      ∃ e c, ∀ i, colour (edges e i) = c)
    (W : Fin samples → Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t) → Bool)
    (μ : Paper2.FiniteLaw (Fin samples))
    (hpattern : HasPatternBound μ W
      ((1 / 2 : ℝ) ^ (4 * (b + 3 * t)))) :
    (2*b + 4*t + 2) + 2*t - 8 ≤
      Dalt .alice (matrixV38 (placeEdges edges index)
        (fullSelector (2^(t-1)) (2^b)) W) := by
  apply lower_bound_matrix ht (by simp) edges index hno
    (fullSelector (2^(t-1)) (2^b))
    (fullSelector_good _ _ _ (by positivity)) W μ hpattern

#print axioms CurrentAdditive.SmallBias.V42.lower_bound_matrix
#print axioms CurrentAdditive.SmallBias.V42.lower_bound_complete_addresses

end CurrentAdditive.SmallBias.V42
