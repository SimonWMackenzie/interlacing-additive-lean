import CurrentAdditive.GeneratedWAlignmentRunV2
import CurrentAdditive.GeneratedWAlignmentFixedEPairV2
import CurrentAdditive.GeneratedWAlignmentOwnerCost
import CurrentAdditive.GeneratedWAlignmentProfiles
import CurrentAdditive.IndexedOwnerScheduleProd

/-! Bind the same source profiles, one conditioning set, and actual padded
reference run. The only remaining physical local bound is incoming mass at
nonowner nodes, supplied separately by the first-Bob contradiction. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.ReferenceCertificateTree Paper2.ReferenceOwners
  CurrentAdditive.DeterministicParameters
open Workspace.Types.Protocol Workspace.Types.CommComplexity
open scoped BigOperators

variable {G V Aux X Y : Type*}
  [Fintype G] [Fintype V] [Fintype Aux] [Fintype X] [Fintype Y]
  [DecidableEq G] [DecidableEq V] [DecidableEq Aux]
  [DecidableEq X] [DecidableEq Y]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}

theorem indexed_W_short_impossible_of_incoming_v2
    (L Δ n m Caux d : ℕ) (γ : ℚ)
    (hL : 2004 ≤ L) (hΔ : 0 < Δ) (hγ : 0 < γ) (hd : 3 ≤ d)
    [NeZero (q₁ L)] [NeZero (q₂ L)] [NeZero (s L)] [NeZero (w L)]
    (src : Sources (D := 8192) (q₁ := q₁ L) (q₂ := q₂ L)
      (s := s L) μX μY)
    (μI : PositiveRationalLaw (G × (V ⊕ Aux)))
    (streams : InternalStreams src μI (w L))
    (R₀ : X → Y → Bool)
    (activity : G × (V ⊕ Aux) → Fin (q₂ L) → Option (Fin (s L)))
    (ξ₀ : Paper2.SourceMatrix.Tail (s L) Y)
    (hD : D R₀ = d)
    (hp : RestrictionProfile R₀ μX.toFiniteLaw μY.toFiniteLaw
      (ρ L : ℝ) (d : ℤ))
    (hadm : Admissible L Δ n m Caux γ)
    (hnear : ∀ (U : Set (Column src))
      (Vrows : Set (Row (I := G × (V ⊕ Aux)) src)),
      1-(η L Δ γ : ℝ) ≤ (columnLaw src).toFiniteLaw.prob (· ∈ U) →
      1-(η L Δ γ : ℝ) ≤ (rowLaw src μI).toFiniteLaw.prob (· ∈ Vrows) →
      d+(L+3)/4+4*L+(L+3)/4+1 ≤
        Paper2.Compression.restrictionD (N src R₀ activity ξ₀) U Vrows)
    (R : Set (Fin (w L) × Column src))
    (Yevent : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (hR : 1 - (δU L Δ γ : ℝ) ≤
      (indexedFirstRowLaw src (w_pos L)).prob (· ∈ R))
    (hY : (θ L : ℝ) ≤ streams.law.toFiniteLaw.prob (· ∈ Yevent))
    (P : Protocol Yevent R Bool)
    (hP : P.Computes (fun t row => W src streams R₀ activity ξ₀ t.val row.val))
    (hPcost : P.cost ≤
      d+(L+3)/4+4*L+(L+3)/4+2*L)
    (hremote : ∀ (E : Finset (Fin (w L)))
      (row0 : R) (col0 : Yevent),
      let st := indexedInitialState src streams R Yevent row0 col0 P E (2*L)
      let T := run (ordinaryLaw src).toFiniteLaw (referenceInput src)
        (Paper2.ReferenceSchedule.floor (w L) (x L : ℝ)) 0 (2*L) st
      let F := fun z : T.Leaves => (T.state z).family
      let final := fun z : T.Leaves => (T.route z).length = 2*L
      let O := ownerNodes F final
      ∀ v ∈ Finset.univ \ O,
        (Finset.univ.sum (fun u : ↥O =>
          protectedReceipt src (w L) (T.state v).rows (origin F final u))) ≤
          (Kstar L : ℝ) * (2^((2*L)-(T.route v).length) : ℕ)) : False := by
  classical
  let a := (L+3)/4
  let H₀ := d+a+4*L+a
  let C := H₀+1
  have hprof := indexed_alignment_source_profiles L hL src μI R₀
    activity ξ₀ d hd hD hp
  have hcount := indexed_owner_scheduled_conditioned_run src μI
    L Δ n m Caux γ (by omega : 1 ≤ L) hΔ hγ
    hadm streams R₀ activity ξ₀
    R Yevent P H₀ (by dsimp [H₀,a]; omega)
    (by simpa [H₀,a] using hprof.2.2)
    hR hY hP (by simpa [H₀,a] using hPcost)
  obtain ⟨E, _hEcard, hEbudget, hTV,
    row0, col0, st, hst, hrun⟩ := hcount
  have hcost :
      let st := indexedInitialState src streams R Yevent row0 col0 P E (2*L)
      let T := run (ordinaryLaw src).toFiniteLaw (referenceInput src)
        (Paper2.ReferenceSchedule.floor (w L) (x L : ℝ)) 0 (2*L) st
      let F := fun z : T.Leaves => (T.state z).family
      let final := fun z : T.Leaves => (T.route z).length = 2*L
      ∀ u : {z // z ∈ ownerNodes F final},
        Paper2.Compression.restrictionD (W src streams R₀ activity ξ₀)
          Yevent (T.state u.val).rows < C := by
    have hc := indexed_initial_final_restriction_le src streams
      R₀ activity ξ₀ R Yevent row0 col0 P E (2*L) H₀
      (x L : ℝ) hP (by simpa [H₀,a] using hPcost)
    dsimp
    intro u
    have hh := hc u
    change Paper2.Compression.restrictionD (W src streams R₀ activity ξ₀)
      Yevent _ ≤ H₀ at hh
    dsimp [C]
    omega
  have hpair := indexed_initial_owner_pair_receipt_v2 L Δ n m Caux d γ
    hL hΔ hγ hd src μI streams R₀ activity ξ₀ R Yevent row0 col0
    P E hadm hprof.1 hprof.2.1
    hY hTV (by simpa [C,H₀,a] using hcost)
  have hrun' :
      let st := indexedInitialState src streams R Yevent row0 col0 P E (2*L)
      let T := run (ordinaryLaw src).toFiniteLaw (referenceInput src)
        (Paper2.ReferenceSchedule.floor (w L) (x L : ℝ)) 0 (2*L) st
      let F := fun z : T.Leaves => (T.state z).family
      let final := fun z : T.Leaves => (T.route z).length = 2*L
      2^(2*L) - exceptionBudget E.card ≤ (ownerNodes F final).card ∧
        exceptionalCapacity F final
          (fun z => 2^((2*L)-(T.route z).length)) ≤ exceptionBudget E.card := by
    rw [hst] at hrun
    simpa using hrun
  exact indexed_initial_run_mass_contradiction_v2 L Δ n m Caux C γ
    (by omega : 1 ≤ L) hΔ hγ src μI streams R₀ activity ξ₀
    R Yevent row0 col0 P E hadm
    hR hY hTV hEbudget (by simpa [C,H₀,a] using hnear)
    hrun' hcost (by simpa [C,H₀,a] using hpair)
    (hremote E row0 col0)

#print axioms indexed_W_short_impossible_of_incoming_v2

end CurrentAdditive.DeterministicIndexedMatrix.Sources
