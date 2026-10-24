import EthInapproximability.CurrentPaper.ExactConstruction
import EthInapproximability.CurrentPaper.ExactIndexing
import EthInapproximability.CurrentPaper.ProtocolSeparation

/-!
# The local contradiction in the current exact-NP reduction

Source: v8 `03-exact-hardness.tex`, the NO direction of `thm:exact-main`,
and `G-exact-control.tex`, the local indexing problem.  Every column used
below is one actual joint diagonal column of `ExactConstruction.matrix`.
The statement retains the list labels, including labels of equal strings.

This module first proves the local contradiction on an actual retained
rectangle. The protocol-control lemmas must supply that rectangle from
arbitrary short protocols; those are distinct obligations, not assumed
completed by the local statement.
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.ExactLowerBound

open Workspace.Types.CommComplexity
open ExactConstruction
open scoped BigOperators

/-- No coordinate can be absent from the dominant-coordinate map: its
entire block would otherwise be distributed among small nondominant fibres.
The map is between transcript labels and input coordinates, not an assumed
identification of those two sets. -/
theorem dominantIndex_surjective {q N τ : ℕ} (hq : 0 < q)
    (lab : Fin q × Fin N → Fin q)
    (hNW : NPCC.NoWasteConclusion Finset.univ Finset.univ lab N τ)
    (hgate : q * τ < N) :
    Function.Surjective (NPCC.Protocol.dominantIndex Finset.univ Finset.univ lab hNW) := by
  classical
  intro α
  by_contra hmiss
  have hmissing : ∀ j, NPCC.Protocol.dominantIndex Finset.univ Finset.univ lab hNW j ≠ α :=
    fun j hj => hmiss ⟨j, hj⟩
  have hfibre : ∀ j : Fin q,
      ((Finset.univ : Finset (Fin N)).filter (fun ℓ => lab (α, ℓ) = j)).card < τ := by
    intro j
    have hsmall := (NPCC.Protocol.dominantIndex_spec Finset.univ Finset.univ lab hNW j).2.2
      α (Finset.mem_univ _) (Ne.symm (hmissing j))
    have heq : ((Finset.univ : Finset (Fin q × Fin N)).filter
        (fun r => lab r = j ∧ r.1 = α)).card =
        ((Finset.univ : Finset (Fin N)).filter (fun ℓ => lab (α, ℓ) = j)).card := by
      apply Finset.card_bij (fun r _ => r.2)
      · intro r hr
        obtain ⟨_, hrj, hrα⟩ := Finset.mem_filter.mp hr
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        simpa [← hrα] using hrj
      · intro r hr s hs h
        exact Prod.ext ((Finset.mem_filter.mp hr).2.2.trans
          (Finset.mem_filter.mp hs).2.2.symm) h
      · intro ℓ hℓ
        exact ⟨(α, ℓ), by simpa using hℓ, rfl⟩
    rwa [heq] at hsmall
  have hsum : N = ∑ j : Fin q,
      ((Finset.univ : Finset (Fin N)).filter (fun ℓ => lab (α, ℓ) = j)).card := by
    simpa using (Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (Fin N))) (t := (Finset.univ : Finset (Fin q)))
      (f := fun ℓ => lab (α, ℓ)) (fun _ _ => Finset.mem_univ _))
  have hne : (Finset.univ : Finset (Fin q)).Nonempty :=
    ⟨⟨0, hq⟩, Finset.mem_univ _⟩
  have hlt := Finset.sum_lt_sum_of_nonempty hne (fun j _ => hfibre j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hlt
  omega

/-- The two distinct active vectors occupy the two different active slots. -/
theorem activeSlots_cover {n d : ℕ} (v : Fin n → Fin d → Bool)
    (cap : ∀ α, (Construction.activeItems v α).card ≤ 2)
    (α : Fin d) (i j : Fin n) (hij : i ≠ j)
    (hi : v i α = true) (hj : v j α = true) (b : Fin 2) :
    activeSlot v cap α ⟨i, hi⟩ = b ∨ activeSlot v cap α ⟨j, hj⟩ = b := by
  have hne : activeSlot v cap α ⟨i, hi⟩ ≠ activeSlot v cap α ⟨j, hj⟩ := by
    intro h
    exact hij (congrArg Subtype.val (Construction.activeSlot_injective v cap α h))
  have hiLt := (activeSlot v cap α ⟨i, hi⟩).isLt
  have hjLt := (activeSlot v cap α ⟨j, hj⟩).isLt
  have hbLt := b.isLt
  by_cases heq : activeSlot v cap α ⟨i, hi⟩ = b
  · exact Or.inl heq
  · right
    apply Fin.ext
    have hnval : (activeSlot v cap α ⟨i, hi⟩).val ≠
        (activeSlot v cap α ⟨j, hj⟩).val := fun h => hne (Fin.ext h)
    have hbval : (activeSlot v cap α ⟨i, hi⟩).val ≠ b.val := fun h => heq (Fin.ext h)
    omega

/-- Prefix rows and one active-active-inactive triple give every indexing
coordinate on the very same labelled diagonal columns. -/
theorem allCoordinates_present {a d N₁ N₂ n : ℕ}
    (ha : 2 ≤ a) (C₁ : FirstFamily a N₁) (C₂ : SecondFamily a d N₂)
    (v : Fin n → Fin d → Bool) (cap : ∀ α, (Construction.activeItems v α).card ≤ 2)
    (R : Finset (Rows N₂ n)) (p : Fin 4) (α : Fin d)
    (hprefix : ∀ u : Fin (prefixLength a), ∃ z : Fin N₂,
      Sum.inl (p, z) ∈ R ∧ duplicateLabel a ha (C₂ z α) = u)
    (i j k : Fin n) (hij : i ≠ j)
    (hi : v i α = true) (hj : v j α = true) (hk : v k α = false)
    (hiR : Sum.inr i ∈ R) (hjR : Sum.inr j ∈ R) (hkR : Sum.inr k ∈ R) :
    ∀ u : Fin (prefixLength a + 3), ∃ r ∈ R,
      ∀ ℓ : Fin N₁, matrix ha C₁ C₂ v cap r (diagonal C₁ α ℓ) = C₁ ℓ u := by
  intro u
  refine Fin.addCases ?_ ?_ u
  · intro u
    obtain ⟨z, hzR, hz⟩ := hprefix u
    refine ⟨Sum.inl (p, z), hzR, ?_⟩
    intro ℓ
    rw [matrix_template_diagonal, hz]
    rfl
  · intro b
    by_cases hb : b.val < 2
    · let b' : Fin 2 := ⟨b.val, hb⟩
      rcases activeSlots_cover v cap α i j hij hi hj b' with hiSlot | hjSlot
      · refine ⟨Sum.inr i, hiR, ?_⟩
        intro ℓ
        rw [matrix_active_diagonal ha C₁ C₂ v cap i α ℓ hi, hiSlot]
        rfl
      · refine ⟨Sum.inr j, hjR, ?_⟩
        intro ℓ
        rw [matrix_active_diagonal ha C₁ C₂ v cap j α ℓ hj, hjSlot]
        rfl
    · have hb2 : b = 2 := Fin.ext (by have := b.isLt; omega)
      subst b
      exact ⟨Sum.inr k, hkR, fun ℓ => matrix_inactive_diagonal ha C₁ C₂ v cap k α ℓ hk⟩

/-- An actual retained rectangle that contains all coordinate rows and
joint diagonal columns contains labelled binary indexing as a restriction. -/
theorem indexing_le_rectangle {a d N₁ N₂ n : ℕ}
    (ha : 2 ≤ a) (C₁ : FirstFamily a N₁) (C₂ : SecondFamily a d N₂)
    (v : Fin n → Fin d → Bool) (cap : ∀ α, (Construction.activeItems v α).card ≤ 2)
    (R : Finset (Rows N₂ n)) (S : Finset (Columns d N₁))
    (α : Fin d) (J : Finset (Fin N₁))
    (hrows : ∀ u : Fin (prefixLength a + 3), ∃ r ∈ R,
      ∀ ℓ : Fin N₁, matrix ha C₁ C₂ v cap r (diagonal C₁ α ℓ) = C₁ ℓ u)
    (hcols : ∀ ℓ ∈ J, diagonal C₁ α ℓ ∈ S) :
    D (fun u (ℓ : {ℓ // ℓ ∈ J}) => C₁ ℓ.val u) ≤
      D (fun (r : {r // r ∈ R}) (c : {c // c ∈ S}) => matrix ha C₁ C₂ v cap r.val c.val) := by
  classical
  choose row row_mem row_entry using hrows
  let rowMap : Fin (prefixLength a + 3) → {r // r ∈ R} := fun u => ⟨row u, row_mem u⟩
  let colMap : {ℓ // ℓ ∈ J} → {c // c ∈ S} :=
    fun ℓ => ⟨diagonal C₁ α ℓ.val, hcols ℓ.val ℓ.property⟩
  have hle := ParameterizedNP.DenseStageFourOpening.D_precomp_le
    (fun (r : {r // r ∈ R}) (c : {c // c ∈ S}) => matrix ha C₁ C₂ v cap r.val c.val)
    rowMap colMap
  have heq : (fun u ℓ => matrix ha C₁ C₂ v cap (rowMap u).val (colMap ℓ).val) =
      (fun u (ℓ : {ℓ // ℓ ∈ J}) => C₁ ℓ.val u) := by
    funext u ℓ
    exact row_entry u ℓ.val
  rw [heq] at hle
  exact hle

/-- The local one-bit contradiction, with the paper's literal `2^a+1`
indexing coordinates. All premises name concrete retained rows/columns,
balancedness, or the explicit strict label-density gate. -/
theorem local_indexing_lower_bound {a d N₁ N₂ n t : ℕ} {ε : ℝ}
    (ha : 2 ≤ a) (C₁ : FirstFamily a N₁) (C₂ : SecondFamily a d N₂)
    (v : Fin n → Fin d → Bool) (cap : ∀ α, (Construction.activeItems v α).card ≤ 2)
    (hC₁ : NPCC.IsBalancedFamily t C₁ ε) (ht : a + 2 ≤ t)
    (R : Finset (Rows N₂ n)) (S : Finset (Columns d N₁))
    (p : Fin 4) (α : Fin d) (J : Finset (Fin N₁))
    (hJ : (1 + ε) * N₁ / 2 < (J.card : ℝ))
    (hcols : ∀ ℓ ∈ J, diagonal C₁ α ℓ ∈ S)
    (hprefix : ∀ u : Fin (prefixLength a), ∃ z : Fin N₂,
      Sum.inl (p, z) ∈ R ∧ duplicateLabel a ha (C₂ z α) = u)
    (i j k : Fin n) (hij : i ≠ j)
    (hi : v i α = true) (hj : v j α = true) (hk : v k α = false)
    (hiR : Sum.inr i ∈ R) (hjR : Sum.inr j ∈ R) (hkR : Sum.inr k ∈ R) :
    a + 2 ≤ D (fun (r : {r // r ∈ R}) (c : {c // c ∈ S}) =>
      matrix ha C₁ C₂ v cap r.val c.val) := by
  have hdim : prefixLength a + 3 = 2 ^ a + 1 := by
    have := Construction.qOne_add_two a (by omega : 1 ≤ a)
    change prefixLength a + 2 = 2 ^ a at this
    omega
  let e : Fin (2 ^ a + 1) → Fin (prefixLength a + 3) := Fin.cast hdim.symm
  have he : Function.Injective e := (finCongr hdim.symm).injective
  have hb := hC₁.projection e he
  have hindex := ExactIndexing.indexingThreshold (fun ℓ u => C₁ ℓ (e u)) hb ht J hJ
  have hreindex := ParameterizedNP.DenseStageFourOpening.D_precomp_le
    (fun u (ℓ : {ℓ // ℓ ∈ J}) => C₁ ℓ.val u) e id
  have hlocal := indexing_le_rectangle ha C₁ C₂ v cap R S α J
    (allCoordinates_present ha C₁ C₂ v cap R p α hprefix i j k hij hi hj hk hiR hjR hkR) hcols
  exact hindex.trans (hreindex.trans hlocal)

end EthInapproximability.CurrentPaper.ExactLowerBound
