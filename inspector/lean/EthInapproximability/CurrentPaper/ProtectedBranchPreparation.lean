import EthInapproximability.CurrentPaper.ProtectedLocalCopies

/-!
# One prepared physical branch

Source: frozen replacement v8 `A-stage4-details.tex`,
`lem:paper-protected-preparation`, the graph-item assignment, defect count,
and final branch selection. The primitive inputs below are the actual
physical deletion bounds, the source NO promise, balancedness of the same
indexed family, and its retained physical representatives. Neither witness
supply nor the aggregate defect estimate is a premise.
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.ProtectedBranchPreparation

open scoped Classical BigOperators
open Construction JointTransfer ProtectedGraphItems ProtectedDefects ProtectedLocalCopies
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open EthInapproximability.ParameterizedNP.GuardedSourceSlab
open EthInapproximability.ParameterizedNP.DenseSourceOwners

universe u v w

variable {V : Type u} {E : Type v} {X Y : Type w}
  [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [Nonempty Y]

/-- Source overload and inactivity on one assigned bin give the three
literal physical representative sets needed by the local-copy theorem. -/
theorem three_items_of_witness {s L nv nb t q : ℕ}
    (order : ItemOrder nv nb) (vectors : Fin (nv + nb) → Fin q → Bool)
    (B : Finset (ProtectedRows s L nv nb X))
    (branch : ProtectedRows s L nv nb X → Fin s)
    (badV : Finset (Fin nv)) (badB : Finset (Fin nb))
    (φ : Fin (nv + nb) → Fin s)
    (hv : ∀ i ∉ badV, HasRowRepresentatives (vertexEmbedding s L nv nb) B branch t i
      (φ (vertexIndex order i)))
    (hb : ∀ i ∉ badB, HasRowRepresentatives (auxiliaryEmbedding s L nv nb) B branch t i
      (φ (auxiliaryIndex order i))) (p : Fin s) (α : Fin q)
    (hactive : 2 ≤ (activeSet vectors (retainedIndices order badV badB) φ p α).card)
    (hinactive : ∃ k ∈ binOf (retainedIndices order badV badB) φ p, vectors k α = false) :
    ∃ i j k : Fin (nv + nb), i ≠ j ∧ vectors i α = true ∧ vectors j α = true ∧
      vectors k α = false ∧
      ItemRepresentatives (t := t) order B branch p i ∧
      ItemRepresentatives (t := t) order B branch p j ∧
      ItemRepresentatives (t := t) order B branch p k := by
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega : 1 <
    (activeSet vectors (retainedIndices order badV badB) φ p α).card)
  obtain ⟨k, hk, hkfalse⟩ := hinactive
  obtain ⟨⟨hiJ, hip⟩, hitrue⟩ := (mem_activeSet ..).mp hi
  obtain ⟨⟨hjJ, hjp⟩, hjtrue⟩ := (mem_activeSet ..).mp hj
  obtain ⟨hkJ, hkp⟩ := (mem_binOf ..).mp hk
  refine ⟨i, j, k, hij, hitrue, hjtrue, hkfalse, ?_, ?_, ?_⟩
  · simpa only [hip] using item_representatives_of_retained order B branch badV badB φ hv hb i hiJ
  · simpa only [hjp] using item_representatives_of_retained order B branch badV badB φ hv hb j hjJ
  · simpa only [hkp] using item_representatives_of_retained order B branch badV badB φ hv hb k hkJ

/-- The full protocol-free preparation step. All sets are constructed from
the actual retained physical domains and the same branch function. -/
theorem prepare_branch (G : EndpointGraph V E) {a s L t t2 : ℕ}
    (hs : 4 ≤ s) (hL : 0 < L) (ht : 0 < t) (hq1 : 1 ≤ qOne a)
    {Δ : ℕ} (hΔ : 0 < Δ) {γ : ℚ} (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hdeg : ∀ v : V, G.degree v ≤ Δ) (hno : G.SourceNO γ)
    (family : SecondFamily a (q2 G s) L X)
    (K : Fin s → Finset (Fin L)) (bin : Fin s → Fin s)
    (A : Finset (ProtectedColumns a s (q2 G s) Y))
    (B : Finset (ProtectedRows s L (GraphVectors.vertexCount V s)
      (GraphVectors.auxiliaryCount s) X))
    (branch : ProtectedRows s L (GraphVectors.vertexCount V s)
      (GraphVectors.auxiliaryCount s) X → Fin s)
    (hKphysical : ∀ p, ∀ ℓ ∈ K p, ∃ k : TemplateLabels s L
        (GraphVectors.vertexCount V s) (GraphVectors.auxiliaryCount s) X,
      templateEmbedding s L (GraphVectors.vertexCount V s) (GraphVectors.auxiliaryCount s)
        (bin p) (ℓ, k) ∈ B ∧
      branch (templateEmbedding s L (GraphVectors.vertexCount V s)
        (GraphVectors.auxiliaryCount s) (bin p) (ℓ, k)) = p)
    (hhalf : 2 * (s * (t - 1)) ≤ Fintype.card X)
    (hdelV : 2 * ((Finset.univ \ B).card : ℚ) <
      ((s : ℚ) / 2 * (G.deltaV γ Δ * Fintype.card V)) *
        (Fintype.card X * vertexMultiplicity (X := X) s L
          (GraphVectors.vertexCount V s) (GraphVectors.auxiliaryCount s) : ℕ))
    (hdelB : 2 * ((Finset.univ \ B).card : ℚ) <
      ((s : ℚ) / 2) *
        (Fintype.card X * auxiliaryMultiplicity (X := X) s L
          (GraphVectors.vertexCount V s) (GraphVectors.auxiliaryCount s) : ℕ))
    {ε xdom η : ℝ} (hε : 0 ≤ ε) (hbal : NPCC.IsBalancedFamily t2 family ε)
    (ht8 : (t : ℝ) - 1 < (Fintype.card X : ℝ) / 8)
    (hwidth : 8 * qOne a ≤ t2) (hK : ∀ p, xdom * L ≤ (K p).card)
    (hxdom : 98 / 100 ≤ xdom / (1 + ε))
    (hdelete : (((Finset.univ : Finset (ProtectedColumns a s (q2 G s) Y)) \ A).card : ℝ) ≤
      η * Fintype.card (ProtectedColumns a s (q2 G s) Y))
    (hscale : 64 * (s : ℝ) * qOne a ≤ ((γ : ℝ) / 24) * q2 G s)
    (hη : η < (1 / 184 : ℝ) * ((γ : ℝ) / 24) / (32 * s)) :
    let bad := fun p => templateBadSet t (coordinateSupport family (K p)) ∪
      diagonalDefects a s (q2 G s) A
    ∃ p : Fin s, ∃ U H W : Finset (Fin (q2 G s)),
      H = Finset.univ \ bad p ∧ W = U \ bad p ∧ W ⊆ H ∧
      q2 G s ≤ H.card + (bad p).card ∧
      U.card ≤ W.card + (bad p).card ∧ 4 * (bad p).card < U.card ∧
      (∀ ℓ ∈ K p, ∃ k : TemplateLabels s L
          (GraphVectors.vertexCount V s) (GraphVectors.auxiliaryCount s) X,
        templateEmbedding s L (GraphVectors.vertexCount V s) (GraphVectors.auxiliaryCount s)
          (bin p) (ℓ, k) ∈ B ∧
        branch (templateEmbedding s L (GraphVectors.vertexCount V s)
          (GraphVectors.auxiliaryCount s) (bin p) (ℓ, k)) = p) ∧
      (∀ α ∈ H, α ∉ templateBadSet t (coordinateSupport family (K p)) ∧
        α ∉ diagonalDefects a s (q2 G s) A) ∧
      (∀ α ∈ W, ∃ i j k : Fin (GraphVectors.vertexCount V s + GraphVectors.auxiliaryCount s),
        i ≠ j ∧ GraphVectors.vectors G s i α = true ∧ GraphVectors.vectors G s j α = true ∧
        GraphVectors.vectors G s k α = false ∧
        ItemRepresentatives (t := t) (GraphVectors.itemOrder G s) B branch p i ∧
        ItemRepresentatives (t := t) (GraphVectors.itemOrder G s) B branch p j ∧
        ItemRepresentatives (t := t) (GraphVectors.itemOrder G s) B branch p k) := by
  dsimp only
  let badV := badItems (vertexEmbedding s L (GraphVectors.vertexCount V s)
    (GraphVectors.auxiliaryCount s)) B (s * (t - 1) + 1)
  let badB := badItems (auxiliaryEmbedding s L (GraphVectors.vertexCount V s)
    (GraphVectors.auxiliaryCount s)) B (s * (t - 1) + 1)
  let J := retainedIndices (GraphVectors.itemOrder G s) badV badB
  obtain ⟨φ, hsource, hφV, hφB⟩ := physical_witness_supply G hs hΔ hγ hγone hdeg hno
    L hL ht hhalf B branch hdelV hdelB
  obtain ⟨U, hU, _, hsum⟩ := disjoint_witness_partition (GraphVectors.vectors G s)
    J φ (by omega)
  let bad := fun p => templateBadSet t (coordinateSupport family (K p)) ∪
    diagonalDefects a s (q2 G s) A
  have hsupply : ((γ : ℝ) / 24) * q2 G s ≤ ∑ p : Fin s, ((U p).card : ℝ) := by
    have hcast := (Rat.cast_le (K := ℝ)).mpr hsource
    simp only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast] at hcast
    rw [← hsum] at hcast
    simpa only [Nat.cast_sum] using hcast
  have hdefect : (∑ p : Fin s, ((bad p).card : ℝ)) < ((γ : ℝ) / 24) * q2 G s / 4 :=
    aggregate_defects_lt (by omega) (q2_pos G s) hq1 family K A hε hbal ht8 hwidth hK hxdom
      hdelete (div_pos (Rat.cast_pos.mpr hγ) (by norm_num)) hscale hη
  obtain ⟨p, hH, hW, hfour⟩ := select_prepared_branch U bad hsupply hdefect
  refine ⟨p, U p, Finset.univ \ bad p, U p \ bad p, rfl, rfl,
    Finset.sdiff_subset_sdiff (Finset.subset_univ _) (Finset.Subset.refl _),
    hH, hW, hfour, hKphysical p, ?_, ?_⟩
  · intro α hα
    have hn := (Finset.mem_sdiff.mp hα).2
    exact ⟨fun h => hn (Finset.mem_union_left _ h), fun h => hn (Finset.mem_union_right _ h)⟩
  · intro α hα
    have hαU := (Finset.mem_sdiff.mp hα).1
    obtain ⟨hactive, hinactive⟩ := hU p α hαU
    exact three_items_of_witness (GraphVectors.itemOrder G s) (GraphVectors.vectors G s)
      B branch badV badB φ hφV hφB p α hactive hinactive

end EthInapproximability.CurrentPaper.ProtectedBranchPreparation
