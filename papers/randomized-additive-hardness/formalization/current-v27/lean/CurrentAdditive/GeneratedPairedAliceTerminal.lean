import CurrentAdditive.GeneratedPairedExactSelection
import Paper2.PairedSelectorCapacityFibre

/-! The actual Alice-query terminal of the generated paired-selector
obstruction.  The heavier child retains the original pair-source mass. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.PairedSelectorCapacityFibre
open CurrentAdditive.ArbitraryPrefix
open Workspace.Types.Protocol

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

/-- A genuine first Alice bit costs one more than the selected exact
amplification bound.  The query fibre is measured in the original product
law on the two complete selector labels. -/
theorem selected_paired_alice_cost
    (R₀ : X → Y → Bool) (d a n : ℕ) (x : ℝ)
    (hD : 8 ≤ D) (ha : 1 ≤ a) (hd : 2 ≤ d) (hx : 0 < x)
    (hscale : (2 : ℝ)^a * x ≤ 1)
    (hprofile : RestrictionProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
      x (d : ℤ))
    (e : Fin n → Bool × Fin q₂) (he : Function.Injective e)
    (hcount : 2^(a-1)+1 ≤ n)
    (Rows : Fin n → Set src.gamma.Label)
    (hrow : ∀ i : Fin n,
      (2 : ℝ)^a*x ≤ src.gamma.law.toFiniteLaw.prob (· ∈ Rows i))
    (K : Set (src.inner.Label × src.inner.Label))
    (hK : (49/64 : ℝ) ≤
      (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw).prob (· ∈ K))
    (C : Set ((Bool × Fin q₂) × src.gamma.Label))
    (hRows : ∀ i : Fin n, ∀ γ ∈ Rows i, (e i, γ) ∈ C)
    (query : K → Bool) (left right : Protocol K C Bool)
    (hP : (Protocol.aNode query left right).Computes
      (fun z c => pairedIndexed src R₀ z.val
        (c.val.1.1, (c.val.1.2, c.val.2)))) :
    d+a+1 ≤ (Protocol.aNode query left right).cost := by
  classical
  let M : (src.inner.Label × src.inner.Label) →
      ((Bool × Fin q₂) × src.gamma.Label) → Bool :=
    fun z c => pairedIndexed src R₀ z (c.1.1, (c.1.2, c.2))
  let b := heavyRowBit
    (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw) K query
  let K' := SourceSupportCapacity.rowFibre K query b
  have hK' : (9/25 : ℝ) ≤
      (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw).prob (· ∈ K') := by
    have ht := heavy_rowFibre_mass
      (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw)
      K query (49/128 : ℝ) (by linarith)
    change (49/128 : ℝ) ≤ _ at ht
    linarith
  have hl := selected_paired_exact_lower src R₀ d a n x hD ha hd hx
    hscale hprofile e he hcount Rows hrow K' hK'
  have hsel : Compression.restrictionD
      (fun (u : Fin n × src.gamma.Label) z =>
        pairedIndexed src R₀ z ((e u.1).1, ((e u.1).2, u.2)))
      (rowRectangle Finset.univ Rows) K' ≤
      Compression.restrictionD (fun c z => M z c) C K' := by
    simpa only [M] using SourceProjection.restrictionD_map_le
      (fun c z => M z c)
      (fun u : Fin n × src.gamma.Label => (e u.1, u.2))
      (fun z : src.inner.Label × src.inner.Label => z)
      C K' (rowRectangle Finset.univ Rows) K'
      (by
        intro u hu
        exact hRows u.1 u.2 (by simpa only [rowRectangle, Finset.mem_univ,
          true_and] using hu))
      (by intro z hz; exact hz)
  have htrans : Compression.restrictionD (fun c z => M z c) C K' =
      Compression.restrictionD M K' C :=
    SourceProjection.restrictionD_transpose M K' C
  have hchild : Compression.restrictionD M K' C + 1 ≤
      (Protocol.aNode query left right).cost :=
    rowFibre_restrictionD_add_one_le M K C query left right hP b
  omega

#print axioms selected_paired_alice_cost

end CurrentAdditive.DeterministicIndexedMatrix.Sources
