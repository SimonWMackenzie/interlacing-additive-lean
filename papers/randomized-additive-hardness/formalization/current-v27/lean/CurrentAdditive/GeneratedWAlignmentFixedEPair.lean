import CurrentAdditive.GeneratedWAlignmentPairSchedule
import CurrentAdditive.IndexedOwnerFixedEReceipt

/-! Apply the shared exceptional set to two genuine owner origins in the
same indexed W run. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.ReferenceCertificateTree Paper2.ReferenceOwners
  CurrentAdditive.DeterministicParameters

variable {G V Aux X Y : Type*}
  [Fintype G] [Fintype V] [Fintype Aux] [Fintype X] [Fintype Y]
  [DecidableEq G] [DecidableEq V] [DecidableEq Aux]
  [DecidableEq X] [DecidableEq Y]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}

theorem indexed_initial_owner_pair_receipt
    (L Δ n m d : ℕ) (γ : ℚ)
    (hL : 2004 ≤ L) (hΔ : 0 < Δ) (hγ : 0 < γ) (hd : 3 ≤ d)
    [NeZero (q₁ L)] [NeZero (q₂ L)] [NeZero (s L)] [NeZero (w L)]
    (src : Sources (D := 8192) (q₁ := q₁ L) (q₂ := q₂ L)
      (s := s L) μX μY)
    (μI : PositiveRationalLaw (G × (V ⊕ Aux)))
    (streams : InternalStreams src μI (w L))
    (R₀ : X → Y → Bool)
    (activity : G × (V ⊕ Aux) → Fin (q₂ L) → Option (Fin (s L)))
    (ξ₀ : Paper2.SourceMatrix.Tail (s L) Y)
    (R : Set (Fin (w L) × Column src))
    (Yevent : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (row0 : R) (col0 : Yevent)
    (P : Workspace.Types.Protocol.Protocol Yevent R Bool)
    (E : Finset (Fin (w L)))
    (hadm : Admissible L Δ n m
      (d+(L+3)/4+4*L+(L+3)/4+1) γ)
    (hA : RestrictionProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin (q₁ L))).prod μX).toFiniteLaw
      (x L : ℝ) ((d+(L+3)/4 : ℕ) : ℤ))
    (hT : RestrictionProfile (T src R₀)
      src.inner.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin (q₂ L))).prod
        src.gamma.law).toFiniteLaw
      (x L : ℝ) ((d+(L+3)/4+4*L : ℕ) : ℤ))
    (hY : (θ L : ℝ) ≤ streams.law.toFiniteLaw.prob (· ∈ Yevent))
    (hTV : ∀ J : Finset (Fin (w L)),
      J ⊆ Finset.univ \ E → J.card ≤ 8 →
      projectionTV
        (condition streams.law.toFiniteLaw (· ∈ Yevent)
          (lt_of_lt_of_le (by exact_mod_cast theta_pos L) hY))
        (rowLaw src μI).toFiniteLaw
        (InternalStreams.decode src streams) J ≤
          CurrentAdditive.conditioningEpsilonR 1024
            (θ L : ℝ) ((η L Δ γ : ℝ)/2))
    (hcost :
      let st := indexedInitialState src streams R Yevent row0 col0 P E (2*L)
      let T := run (ordinaryLaw src).toFiniteLaw (referenceInput src)
        (Paper2.ReferenceSchedule.floor (w L) (x L : ℝ)) 0 (2*L) st
      let F := fun z : T.Leaves => (T.state z).family
      let final := fun z : T.Leaves => (T.route z).length = 2*L
      ∀ u : {z // z ∈ ownerNodes F final},
        Paper2.Compression.restrictionD (W src streams R₀ activity ξ₀)
          Yevent (T.state u.val).rows <
            d+(L+3)/4+4*L+(L+3)/4+1) :
    let st := indexedInitialState src streams R Yevent row0 col0 P E (2*L)
    let T := run (ordinaryLaw src).toFiniteLaw (referenceInput src)
      (Paper2.ReferenceSchedule.floor (w L) (x L : ℝ)) 0 (2*L) st
    let F := fun z : T.Leaves => (T.state z).family
    let final := fun z : T.Leaves => (T.route z).length = 2*L
    ∀ v u : {z // z ∈ ownerNodes F final}, u ≠ v →
      protectedReceipt src (w L) (T.state v.val).rows (origin F final u) ≤
        2 * (1/256 : ℝ) *
          (2 * q₂ L * (x L : ℝ) +
            5 * (1 - (ordinaryLaw src).toFiniteLaw.prob
              (fun z => (origin F final v, Column.ordinary z) ∈
                (T.state v.val).rows)) + 2 / q₂ L) := by
  classical
  intro st T F final v u huv
  let a := (L+3)/4
  let H₁ := d+a
  have hθ : (0 : ℝ) < (θ L : ℝ) := by exact_mod_cast theta_pos L
  have hη : (0 : ℝ) < (η L Δ γ : ℝ) := by
    exact_mod_cast eta_pos L Δ γ hΔ hγ
  have hnum := indexed_pair_public_numeric L Δ n m
    (d+a+4*L+a+1) γ hΔ hγ hadm
  have hpair := owner_to_owner_receipt_from_same_E src μI
    streams R₀ activity ξ₀ Yevent (T.state v.val).rows E
    H₁ (4*L) a (by omega : 2 ≤ H₁)
    (q₂_eq_pow L) (by rfl : s L = 2^a)
    (x L : ℝ) (x_real_pos L) hA hT
    (θ L : ℝ) (η L Δ γ : ℝ) hθ hY hη hTV
    hnum.1 hnum.2.1
    (1 - (ordinaryLaw src).toFiniteLaw.prob
      (fun z => (origin F final v, Column.ordinary z) ∈
        (T.state v.val).rows))
    (2 * q₂ L * (x L : ℝ) +
      5 * (1 - (ordinaryLaw src).toFiniteLaw.prob
        (fun z => (origin F final v, Column.ordinary z) ∈
          (T.state v.val).rows)) + 2 / q₂ L)
    (by rfl) hnum.2.2.1 hnum.2.2.2
  have hinj : Function.Injective (origin F final) := by
    exact run_origin_injective (ordinaryLaw src).toFiniteLaw
      (referenceInput src) (Paper2.ReferenceSchedule.floor (w L) (x L : ℝ))
      (2*L) st
  have hneq : origin F final v ≠ origin F final u := by
    intro heq
    exact huv (hinj heq).symm
  have hvE := indexed_initial_owner_origin_not_exception src streams
    R Yevent row0 col0 P E (2*L) (x L : ℝ) st rfl v
  have huE := indexed_initial_owner_origin_not_exception src streams
    R Yevent row0 col0 P E (2*L) (x L : ℝ) st rfl u
  have hupper : Paper2.Compression.restrictionD
      (W src streams R₀ activity ξ₀) Yevent (T.state v.val).rows ≤
      H₁+4*L+a := by
    have hc := hcost v
    change Paper2.Compression.restrictionD
      (W src streams R₀ activity ξ₀) Yevent (T.state v.val).rows <
        d+a+4*L+a+1 at hc
    dsimp [H₁]
    omega
  exact hpair (origin F final v) (origin F final u)
    hneq hvE huE (by linarith) hupper

#print axioms indexed_initial_owner_pair_receipt

end CurrentAdditive.DeterministicIndexedMatrix.Sources
