import CurrentAdditive.PrefixSuffixGlue
import CurrentAdditive.DeterministicSuffixMid

/-! Private source-specific composition of the checked short suffix cases. The
good-coordinate total-variation estimate remains an explicit analytic input. -/

namespace CurrentAdditive.ArbitraryPrefix

open Paper2

variable {X Z S : Type*} [Fintype X] [Fintype Z] [Fintype S]

private def selectGood {q n : ℕ} (Good : Finset (Fin q))
    (h : n ≤ Good.card) : Fin n → Fin q :=
  fun j => Good.orderEmbOfFin rfl (Fin.castLE h j)

private theorem selectGood_injective {q n : ℕ} (Good : Finset (Fin q))
    (h : n ≤ Good.card) : Function.Injective (selectGood Good h) := by
  exact (Good.orderEmbOfFin rfl).injective.comp (Fin.castLE_injective h)

private theorem selectGood_mem {q n : ℕ} (Good : Finset (Fin q))
    (h : n ≤ Good.card) (j : Fin n) : selectGood Good h j ∈ Good :=
  Good.orderEmbOfFin_mem rfl (Fin.castLE h j)

/-- The manuscript's `b=0,1,2,3,4` suffix cases for actual retained indexed
columns. The only source-specific premise is the good-coordinate marginal
estimate; no communication lower bound is assumed. -/
theorem rare_suffix_short
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (source : FiniteLaw S)
    {q b : ℕ} (hb : b ≤ 4) (decode : S → Fin q → Z)
    (Good : Finset (Fin q)) (hGood : 2^b + 1 ≤ Good.card)
    (Rows : Fin q → Set X) (Y K : Set S)
    (d : ℕ) (x ε : ℝ)
    (hd : 2 ≤ d) (hx : 0 < x)
    (hscale : (2 : ℝ)^(b+1) * x ≤ 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x (d : ℤ))
    (hrow : ∀ i ∈ Good, (2 : ℝ)^(b+1) * x ≤ μ.toFiniteLaw.prob (· ∈ Rows i))
    (hY : 0 < source.prob (· ∈ Y)) (hK : K ⊆ Y)
    (hcond : 1 / (2 : ℝ)^(b+1) ≤ source.prob (· ∈ K) / source.prob (· ∈ Y))
    (hε : ε ≤ 1 / 1000)
    (hgood : ∀ (n : ℕ) (hn : n ≤ 8) (e : Fin n → Fin q),
      (∀ j, e j ∈ Good) → ∀ P : (Fin n → Z) → Prop,
      |source.prob (fun s => s ∈ Y ∧ P (fun j => decode s (e j))) /
        source.prob (· ∈ Y) - (ν.toFiniteLaw.iid n).prob P| ≤ ε) :
    d + 1 ≤ Paper2.Compression.restrictionD
      (fun a s => F a.2 (decode s a.1)) (rowRectangle Good Rows) K := by
  interval_cases b
  · have hc : 2 ≤ Good.card := by simpa using hGood
    let e : Fin 2 → Fin q := selectGood Good hc
    apply SuffixSmall.suffix_zero μ ν F source decode e
      (rowRectangle Good Rows) Y K d x ε hd hx
    · simpa using hscale
    · exact hprofile
    · intro j
      rw [rowRectangle_fiber Good Rows _ (selectGood_mem Good hc j)]
      simpa [e] using hrow (e j) (selectGood_mem Good hc j)
    · exact hY
    · exact hK
    · simpa using hcond
    · linarith
    · exact hgood 2 (by omega) e (fun j => selectGood_mem Good hc j)
  · have hc : 3 ≤ Good.card := by simpa using hGood
    norm_num at hscale hrow hcond
    let e : Fin 3 → Fin q := selectGood Good hc
    apply SuffixSmall.suffix_one μ ν F source decode e
      (rowRectangle Good Rows) Y K d x ε hd hx
    · simpa using hscale
    · exact hprofile
    · intro j
      rw [rowRectangle_fiber Good Rows _ (selectGood_mem Good hc j)]
      simpa [e] using hrow (e j) (selectGood_mem Good hc j)
    · exact hY
    · exact hK
    · simpa using hcond
    · linarith
    · exact hgood 3 (by omega) e (fun j => selectGood_mem Good hc j)
  · have hc : 5 ≤ Good.card := by simpa using hGood
    norm_num at hscale hrow hcond
    let e : Fin 5 → Fin q := selectGood Good hc
    apply SuffixMid.suffix_two μ ν F source decode e
      (selectGood_injective Good hc) (rowRectangle Good Rows) Y K d x ε hd hx
    · simpa using hscale
    · exact hprofile
    · intro j
      rw [rowRectangle_fiber Good Rows _ (selectGood_mem Good hc j)]
      simpa [e] using hrow (e j) (selectGood_mem Good hc j)
    · exact hY
    · exact hK
    · simpa using hcond
    · linarith
    · exact hgood 5 (by omega) e (fun j => selectGood_mem Good hc j)
  · have hc : 8 ≤ Good.card := by omega
    norm_num at hscale hrow hcond
    let e : Fin 8 → Fin q := selectGood Good hc
    apply SuffixMid.suffix_three μ ν F source decode e
      (selectGood_injective Good hc) (rowRectangle Good Rows) Y K d x ε hd hx
    · simpa using hscale
    · exact hprofile
    · intro j
      rw [rowRectangle_fiber Good Rows _ (selectGood_mem Good hc j)]
      simpa [e] using hrow (e j) (selectGood_mem Good hc j)
    · exact hY
    · exact hK
    · simpa using hcond
    · linarith
    · exact hgood 8 (by omega) e (fun j => selectGood_mem Good hc j)
  · have hc : 8 ≤ Good.card := by omega
    norm_num at hscale hrow hcond
    let e : Fin 8 → Fin q := selectGood Good hc
    apply SuffixMid.suffix_four μ ν F source decode e
      (selectGood_injective Good hc) (rowRectangle Good Rows) Y K d x ε hd hx
    · simpa using hscale
    · exact hprofile
    · intro j
      rw [rowRectangle_fiber Good Rows _ (selectGood_mem Good hc j)]
      simpa [e] using hrow (e j) (selectGood_mem Good hc j)
    · exact hY
    · exact hK
    · simpa using hcond
    · linarith
    · exact hgood 8 (by omega) e (fun j => selectGood_mem Good hc j)

/-- Rare-conditioning amplification when `a ≤ 5`. Every possible Bob count
`B` then falls into one of the checked short suffix cases. -/
theorem rareboost_short
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (source : FiniteLaw S)
    {q : ℕ} (decode : S → Fin q → Z)
    (Good : Finset (Fin q)) (Rows : Fin q → Set X) (Y K : Set S)
    (d a : ℕ) (x ε : ℝ)
    (ha : 1 ≤ a) (ha5 : a ≤ 5) (hd : 2 ≤ d) (hx : 0 < x)
    (hscale : (2 : ℝ)^a * x ≤ 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x (d : ℤ))
    (hcount : 2^(a-1) + 1 ≤ Good.card)
    (hrow : ∀ i ∈ Good, (2 : ℝ)^a * x ≤ μ.toFiniteLaw.prob (· ∈ Rows i))
    (hY : 0 < source.prob (· ∈ Y)) (hK : K ⊆ Y)
    (hcond : (1/2 : ℝ) ≤ source.prob (· ∈ K) / source.prob (· ∈ Y))
    (hε : ε ≤ 1 / 1000)
    (hgood : ∀ (n : ℕ) (hn : n ≤ 8) (e : Fin n → Fin q),
      (∀ j, e j ∈ Good) → ∀ P : (Fin n → Z) → Prop,
      |source.prob (fun s => s ∈ Y ∧ P (fun j => decode s (e j))) /
        source.prob (· ∈ Y) - (ν.toFiniteLaw.iid n).prob P| ≤ ε) :
    d+a ≤ Paper2.Compression.restrictionD
      (fun a s => F a.2 (decode s a.1)) (rowRectangle Good Rows) K := by
  let G : (Fin q × X) → S → Bool := fun a s => F a.2 (decode s a.1)
  let D := Paper2.Compression.restrictionD G (rowRectangle Good Rows) K
  by_contra hn
  change ¬ (d+a ≤ D) at hn
  have hD : D ≤ d+a-1 := by omega
  obtain ⟨A, B, Good', Rows', K', P', hab, hcount', hrow', hcond',
    hGoodsub, hRowssub, hKsub, hKY, hcost, heval⟩ :=
    rare_prefix_state μ.toFiniteLaw source G Good Rows Y K d a x
      ha hx hcount hrow hY hK hcond hD
  have hb : B ≤ 4 := by omega
  have hscale' : (2 : ℝ)^(B+1) * x ≤ 1 := by
    have hp : (2 : ℝ)^(B+1) ≤ (2 : ℝ)^a :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    exact (mul_le_mul_of_nonneg_right hp hx.le).trans hscale
  have htv : ∀ (n : ℕ) (hn : n ≤ 8) (e : Fin n → Fin q),
      (∀ j, e j ∈ Good') → ∀ P : (Fin n → Z) → Prop,
      |source.prob (fun s => s ∈ Y ∧ P (fun j => decode s (e j))) /
        source.prob (· ∈ Y) - (ν.toFiniteLaw.iid n).prob P| ≤ ε := by
    intro n hn e he P
    exact hgood n hn e (fun j => hGoodsub (he j)) P
  have hlower := rare_suffix_short μ ν F source hb decode Good' hcount'
    Rows' Y K' d x ε hd hx hscale' hprofile hrow' hY hKY hcond' hε htv
  have hupper : Paper2.Compression.restrictionD G
      (rowRectangle Good' Rows') K' ≤ d :=
    residual_restriction_upper G Good' Rows' K' P' d hcost heval
  change d + 1 ≤ Paper2.Compression.restrictionD G
    (rowRectangle Good' Rows') K' at hlower
  omega

#print axioms CurrentAdditive.ArbitraryPrefix.rare_suffix_short
#print axioms CurrentAdditive.ArbitraryPrefix.rareboost_short

end CurrentAdditive.ArbitraryPrefix
