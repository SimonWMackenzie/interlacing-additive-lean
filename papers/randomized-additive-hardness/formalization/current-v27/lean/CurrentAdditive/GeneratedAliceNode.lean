import CurrentAdditive.GeneratedExactCapacity
import Paper2.SourceSupportCapacity

/-!
The Appendix I `det:near-full` Alice-node capacity argument on the literal
finite indexed matrix. The denser child retains a joint set of complete
inner-source labels. Every diagonal gamma support is unchanged by Alice's
query, so the source-specific exact boost applies below that actual bit.
-/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix Paper2.SourceProjection
open Paper2.SourceSupportCapacity
open CurrentAdditive.ArbitraryPrefix
open Workspace.Types.CommComplexity Workspace.Types.Protocol

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

def innerFibre (p : Fin s) (K : Set src.inner.Label)
    (V : Set (Row (I := I) src)) (query : V → Bool) (b : Bool) :
    Set src.inner.Label :=
  {z | z ∈ K ∧ rawQuery V query (.inl (p, z)) = b}

theorem dense_inner_child (p : Fin s) (K : Set src.inner.Label)
    (V : Set (Row (I := I) src)) (query : V → Bool)
    (hK : (998/1000 : ℝ) < src.inner.law.toFiniteLaw.prob (· ∈ K)) :
    ∃ b, (499/1000 : ℝ) < src.inner.law.toFiniteLaw.prob
      (· ∈ innerFibre src p K V query b) := by
  classical
  let law := src.inner.law.toFiniteLaw
  let f := fun z : src.inner.Label => rawQuery V query (.inl (p, z))
  let b := Paper2.SourceSupportStep.heavyBit law K.toFinset f
  have hp := Paper2.SourceSupportStep.mass_partition_heavy law K.toFinset f
  have hg := Paper2.SourceSupportStep.heavy_ge_other law K.toFinset f
  have he : ∀ c, Paper2.SourceSupportStep.mass law
      (Paper2.SourceSupportStep.fibre K.toFinset f c) =
      law.prob (· ∈ innerFibre src p K V query c) := by
    intro c
    simp only [Paper2.SourceSupportStep.mass,
      Paper2.SourceSupportStep.mem_fibre, Set.mem_toFinset]
    rfl
  have hm : Paper2.SourceSupportStep.mass law K.toFinset = law.prob (· ∈ K) := by
    simp [Paper2.SourceSupportStep.mass]
  rw [he, he, hm] at hp
  rw [he, he] at hg
  refine ⟨b, ?_⟩
  change (499/1000 : ℝ) < law.prob (· ∈ innerFibre src p K V query b)
  change (998/1000 : ℝ) < law.prob (· ∈ K) at hK
  dsimp only [b]
  linarith

theorem innerFibre_retained (p : Fin s) (K : Set src.inner.Label)
    (V : Set (Row (I := I) src)) (query : V → Bool) (b : Bool)
    (hK : ∀ z ∈ K, Sum.inl (p, z) ∈ V) :
    ∀ z ∈ innerFibre src p K V query b,
      Sum.inl (p, z) ∈ rowFibre V query b := by
  intro z hz
  exact ⟨hK z hz.1, hz.2⟩

theorem indexed_alice_exact_cost
    (hD : 8 ≤ D) (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (p : Fin s) (K : Set src.inner.Label)
    (Good : Finset (Fin q₂)) (Rows : Fin q₂ → Set src.gamma.Label)
    (U : Set (Column src)) (V : Set (Row (I := I) src))
    (d a : ℕ) (x : ℝ)
    (ha : 1 ≤ a) (hd : 2 ≤ d) (hx : 0 < x)
    (hscale : (2 : ℝ)^a * x ≤ 1)
    (hprofile : RestrictionProfile (A src R)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
      x (d : ℤ))
    (hcount : 2^(a-1)+1 ≤ Good.card)
    (hrow : ∀ i ∈ Good, (2 : ℝ)^a*x ≤
      src.gamma.law.toFiniteLaw.prob (· ∈ Rows i))
    (hKmass : (998/1000 : ℝ) < src.inner.law.toFiniteLaw.prob (· ∈ K))
    (hK : ∀ z ∈ K, Sum.inl (p, z) ∈ V)
    (hS : ∀ α ∈ rowRectangle Good Rows,
      Column.diagonal (α.1, α.2) ∈ U)
    (query : V → Bool) (left right : Protocol V U Bool)
    (hP : (Protocol.aNode query left right).Computes
      (fun v u => N src R activity ξ₀ u.val v.val)) :
    d+a+1 ≤ (Protocol.aNode query left right).cost := by
  classical
  obtain ⟨b, hb⟩ := dense_inner_child src p K V query hKmass
  let Vb := rowFibre V query b
  let Pb := childProtocol V query left right b
  have hbc : Pb.Computes
      (fun (v : Vb) (u : U) => N src R activity ξ₀ u.val v.val) :=
    childProtocol_computes (fun v (u : U) => N src R activity ξ₀ u.val v)
      V query left right hP b
  have hcost : Paper2.Compression.restrictionD (N src R activity ξ₀)
      U Vb ≤ Pb.cost := by
    have hup : Workspace.Types.CommComplexity.D (fun (v : Vb) (u : U) =>
        N src R activity ξ₀ u.val v.val) ≤ Pb.cost :=
      Nat.sInf_le ⟨Pb, rfl, hbc⟩
    have he := restrictionD_transpose (N src R activity ξ₀) U Vb
    exact he ▸ hup
  have hbK : (9/25 : ℝ) ≤ src.inner.law.toFiniteLaw.prob
      (· ∈ innerFibre src p K V query b) := by linarith
  have hlower := indexed_diagonal_exact_capacity src hD R activity ξ₀ p
    (innerFibre src p K V query b) Good Rows U Vb d a x
    ha hd hx hscale hprofile hcount hrow hbK
    (innerFibre_retained src p K V query b hK) hS
  have hstep := childProtocol_cost V query left right b
  dsimp only [Pb] at hcost hstep
  omega

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.dense_inner_child
#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.indexed_alice_exact_cost
