import CurrentAdditive.IndexedIncomingExceptionSchedule
import CurrentAdditive.IndexedIncomingExactRun
import CurrentAdditive.IndexedOwnerScheduleProd
import CurrentAdditive.DeterministicAdmissibility
import CurrentAdditive.IndexedProfileSchedule

namespace CurrentAdditive.DeterministicParameters

private theorem incoming_x_real_eq_pow (L : ℕ) :
    (x L : ℝ) = 1 / (2 : ℝ)^(16*L) := by
  norm_num [x, N]
  rw [Nat.mul_comm 16 L]
  exact (pow_mul (2 : ℝ) L 16).symm

private theorem incoming_scale_general (L α β : ℕ)
    (h : α+β ≤ 16*L) :
    (2 : ℝ)^α * (x L : ℝ) ≤ 1 / (2 : ℝ)^β := by
  rw [incoming_x_real_eq_pow]
  have hpow : (2 : ℝ)^(α+β) ≤ (2 : ℝ)^(16*L) := by
    exact_mod_cast Nat.pow_le_pow_right (by decide : 0 < 2) h
  calc
    (2 : ℝ)^α * (1 / (2 : ℝ)^(16*L)) =
        (2 : ℝ)^α / (2 : ℝ)^(16*L) := by ring
    _ ≤ 1 / (2 : ℝ)^β := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      simpa [pow_add] using hpow

theorem incoming_public_scale (L : ℕ) (hL : 2004 ≤ L)
    (k : ℕ) (hk : k ≤ 2*L) :
    (2 : ℝ)^(1+(L+3)/4+4*L+k) * (x L : ℝ) ≤ 1 := by
  let b := (L+3)/4
  have hb : b ≤ L := by dsimp [b]; omega
  have hsum : (1+b+4*L+k)+0 ≤ 16*L := by omega
  have hh := incoming_scale_general L (1+b+4*L+k) 0 hsum
  simpa [b] using hh

theorem incoming_public_dyadic_scale (L : ℕ) (hL : 2004 ≤ L)
    (k : ℕ) (hk : k ≤ 2*L) (j : Fin (2*L+2)) :
    (2 : ℝ)^(1+(L+3)/4+4*L+k) * (x L : ℝ) ≤
      ((1/2 : ℝ)^j.val)/4 := by
  let b := (L+3)/4
  have hb : b ≤ L := by dsimp [b]; omega
  have hj : j.val ≤ 2*L+1 := by omega
  have hsum : (1+b+4*L+k)+(j.val+2) ≤ 16*L := by omega
  have hh := incoming_scale_general L (1+b+4*L+k) (j.val+2) hsum
  have heq : 1 / (2 : ℝ)^(j.val+2) = ((1/2 : ℝ)^j.val)/4 := by
    rw [pow_add]
    rw [show ((1/2 : ℝ)^j.val) = ((2 : ℝ)^j.val)⁻¹ by
      rw [one_div, inv_pow]]
    norm_num [mul_inv_rev, div_eq_mul_inv, mul_comm]
  simpa only [b, heq] using hh

theorem incoming_public_blocks (L k : ℕ) :
    2^(1+(L+3)/4+4*L+k-1) ≤ (s L) * 2^k * (q₂ L) := by
  have heq : 1+(L+3)/4+4*L+k-1 = (L+3)/4+k+4*L := by omega
  rw [heq, show s L = 2^((L+3)/4) by rfl, q₂_eq_pow]
  simp only [← pow_add]
  omega

#print axioms incoming_public_scale
#print axioms incoming_public_dyadic_scale
#print axioms incoming_public_blocks

end CurrentAdditive.DeterministicParameters

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open CurrentAdditive.DeterministicParameters
open CurrentAdditive.DeterministicAdmissibility
open Paper2 Paper2.ReferenceCertificates Paper2.ReferenceCertificateTree
  Paper2.ReferenceOwners Workspace.Types.Protocol
open scoped BigOperators

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}

theorem indexed_incoming_A_profile_at_parameters
    {G V Aux : Type*} [Fintype G] [Fintype V] [Fintype Aux]
    (L : ℕ) (hL : 2004 ≤ L)
    [NeZero (q₁ L)] [NeZero (q₂ L)] [NeZero (s L)]
    (src : Sources (D := 8192) (q₁ := q₁ L)
      (q₂ := q₂ L) (s := s L) μX μY)
    (μI : PositiveRationalLaw (G × (V ⊕ Aux)))
    (R₀ : X → Y → Bool)
    (activity : (G × (V ⊕ Aux)) → Fin (q₂ L) → Option (Fin (s L)))
    (ξ₀ : Paper2.SourceMatrix.Tail (s L) Y)
    (d : ℕ) (hd : 3 ≤ d)
    (hD : Workspace.Types.CommComplexity.D R₀ = d)
    (hp : RestrictionProfile R₀ μX.toFiniteLaw μY.toFiniteLaw
      (ρ L : ℝ) (d : ℤ)) :
    RestrictionProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      (((PositiveRationalLaw.uniform (Fin (q₁ L))).prod μX).toFiniteLaw)
      (x L : ℝ) ((d+(L+3)/4 : ℕ) : ℤ) := by
  exact (generated_profiles_at_parameters L hL src μI R₀ activity ξ₀
    d hd hD hp).2.1

#print axioms indexed_incoming_A_profile_at_parameters

/-- Appendix I incoming mass on the exact initialized W run.  The source
profile of A and the actual short protocol are the only mathematical inputs;
all incoming numerical tests are discharged by the public schedule. -/
theorem indexed_incoming_scheduled_initialised_run
    (L Δ n edges : ℕ) (γ : ℚ) (hL : 2004 ≤ L)
    (hadm : Admissible L Δ n edges sourceC128Ceil γ)
    [NeZero (q₁ L)] [NeZero (q₂ L)] [NeZero (s L)]
    (src : Sources (D := 8192) (q₁ := q₁ L)
      (q₂ := q₂ L) (s := s L) μX μY)
    (μI : PositiveRationalLaw I)
    (streams : InternalStreams src μI (w L))
    (R₀ : X → Y → Bool)
    (activity : I → Fin (q₂ L) → Option (Fin (s L)))
    (ξ₀ : Paper2.SourceMatrix.Tail (s L) Y)
    (d : ℕ) (hd : 3 ≤ d)
    (hprofileA : RestrictionProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      (((PositiveRationalLaw.uniform (Fin (q₁ L))).prod μX).toFiniteLaw)
      (x L : ℝ) ((d+(L+3)/4 : ℕ) : ℤ))
    (R : Set (Fin (w L) × Column src))
    (Yevent : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (row0 : R) (col0 : Yevent) (P : Protocol Yevent R Bool)
    (E : Finset (Fin (w L)))
    (hY : (θ L : ℝ) ≤ streams.law.toFiniteLaw.prob (· ∈ Yevent))
    (hP : P.Computes (fun t row => W src streams R₀ activity ξ₀ t.val row.val))
    (hPcost : P.cost ≤ d + 2*((L+3)/4) + 6*L) :
    let st := indexedInitialState src streams R Yevent row0 col0 P E (2*L)
    let T := run (ordinaryLaw src).toFiniteLaw
      (referenceInput src) (Paper2.ReferenceSchedule.floor (w L) (x L : ℝ))
      0 (2*L) st
    ∀ v : T.Leaves,
      (∑ i : Fin (w L), protectedReceipt src (w L) (T.state v).rows i) <
        (Kstar L : ℝ) * (2^((2*L)-(T.route v).length) : ℕ) := by
  have hθ : (0 : ℝ) < (θ L : ℝ) := by exact_mod_cast theta_pos L
  have hguard : ∀ k ≤ 2*L, ∀ m : ℕ,
      256 * (s L : ℝ) * (2^k : ℕ) ≤ m →
      2 * ((64 : ℝ) * m) ^ 128 /
        (((255 / 256 : ℝ) - 1/2) * m) ^ 256 ≤ (θ L : ℝ)/4 := by
    intro k hk m hm
    have hspos : (0 : ℝ) < (s L : ℝ) := by
      exact_mod_cast s_pos L
    have hkpow : (1 : ℝ) ≤ (2^k : ℕ) := by
      have hp : 0 < 2^k := by positivity
      exact_mod_cast (Nat.succ_le_of_lt hp)
    have hsmR : (s L : ℝ) ≤ m := by nlinarith
    have hsm : s L ≤ m := by exact_mod_cast hsmR
    exact source_flag_tail_guard L Δ n edges m γ hadm hsm
  have hbase := indexed_incoming_each_initialised_node src streams
    R₀ activity ξ₀ R Yevent row0 col0 P E (2*L)
    (d + 2*((L+3)/4) + 4*L) (d+(L+3)/4)
    (1+(L+3)/4+4*L) (x L : ℝ) (θ L : ℝ)
    (w_eq_pow L) (s_pos L) (by omega) (by omega) (x_real_pos L)
    (by omega) hprofileA
    (fun k hk => incoming_public_scale L hL k hk)
    (fun k hk => incoming_public_blocks L k)
    (fun k hk j => incoming_public_dyadic_scale L hL k hk j)
    hθ hY hguard
    (fun j => incoming_exception_theta_quarter_all_groups L hL j)
    hP (by omega)
  have hK : 1024 * (1/256 : ℝ) * (2*L+2) * s L =
      (Kstar L : ℝ) := by
    simp only [Kstar, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
    ring
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, hK] using hbase

#print axioms indexed_incoming_scheduled_initialised_run

/-- The same physical-run estimate restricted to the origins of its actual
final owners.  No exceptional set or protocol is chosen a second time. -/
theorem indexed_incoming_owner_origins_scheduled_run
    (L Δ n edges : ℕ) (γ : ℚ) (hL : 2004 ≤ L)
    (hadm : Admissible L Δ n edges sourceC128Ceil γ)
    [NeZero (q₁ L)] [NeZero (q₂ L)] [NeZero (s L)]
    (src : Sources (D := 8192) (q₁ := q₁ L)
      (q₂ := q₂ L) (s := s L) μX μY)
    (μI : PositiveRationalLaw I)
    (streams : InternalStreams src μI (w L))
    (R₀ : X → Y → Bool)
    (activity : I → Fin (q₂ L) → Option (Fin (s L)))
    (ξ₀ : Paper2.SourceMatrix.Tail (s L) Y)
    (d : ℕ) (hd : 3 ≤ d)
    (hprofileA : RestrictionProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      (((PositiveRationalLaw.uniform (Fin (q₁ L))).prod μX).toFiniteLaw)
      (x L : ℝ) ((d+(L+3)/4 : ℕ) : ℤ))
    (R : Set (Fin (w L) × Column src))
    (Yevent : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (row0 : R) (col0 : Yevent) (P : Protocol Yevent R Bool)
    (E : Finset (Fin (w L)))
    (hY : (θ L : ℝ) ≤ streams.law.toFiniteLaw.prob (· ∈ Yevent))
    (hP : P.Computes (fun t row => W src streams R₀ activity ξ₀ t.val row.val))
    (hPcost : P.cost ≤ d + 2*((L+3)/4) + 6*L) :
    let st := indexedInitialState src streams R Yevent row0 col0 P E (2*L)
    let T := run (ordinaryLaw src).toFiniteLaw
      (referenceInput src) (Paper2.ReferenceSchedule.floor (w L) (x L : ℝ))
      0 (2*L) st
    let F := fun u : T.Leaves => (T.state u).family
    let final := fun u : T.Leaves => (T.route u).length = 2*L
    let O := ownerNodes F final
    ∀ v : T.Leaves,
      (∑ u : {u : T.Leaves // u ∈ O},
        protectedReceipt src (w L) (T.state v).rows (origin F final u)) <
        (Kstar L : ℝ) * (2^((2*L)-(T.route v).length) : ℕ) := by
  classical
  let st := indexedInitialState src streams R Yevent row0 col0 P E (2*L)
  let T := run (ordinaryLaw src).toFiniteLaw
    (referenceInput src) (Paper2.ReferenceSchedule.floor (w L) (x L : ℝ))
    0 (2*L) st
  let F := fun u : T.Leaves => (T.state u).family
  let final := fun u : T.Leaves => (T.route u).length = 2*L
  let O := ownerNodes F final
  have hall := indexed_incoming_scheduled_initialised_run L Δ n edges γ
    hL hadm src μI streams R₀ activity ξ₀ d hd hprofileA
    R Yevent row0 col0 P E hY hP hPcost
  have hsub := indexed_incoming_owner_origins_le_all src streams
    R₀ activity ξ₀ (x L : ℝ) (2*L) st
  change ∀ v : T.Leaves,
    (∑ u : {u : T.Leaves // u ∈ O},
      protectedReceipt src (w L) (T.state v).rows (origin F final u)) <
      (Kstar L : ℝ) * (2^((2*L)-(T.route v).length) : ℕ)
  intro v
  exact lt_of_le_of_lt (hsub v) (hall v)

#print axioms indexed_incoming_owner_origins_scheduled_run

/-- One common conditioned exceptional set supplies both the owner-capacity
certificate and the incoming bound on its exact initialized run. -/
theorem indexed_owner_and_incoming_same_E
    {G V Aux : Type*} [Fintype G] [Fintype V] [Fintype Aux]
    [DecidableEq G] [DecidableEq V] [DecidableEq Aux]
    (L Δ n edges : ℕ) (γ : ℚ)
    (hL : 2004 ≤ L) (hΔ : 0 < Δ) (hγ : 0 < γ)
    (hadm : Admissible L Δ n edges sourceC128Ceil γ)
    [NeZero (q₁ L)] [NeZero (q₂ L)] [NeZero (s L)]
    (src : Sources (D := 8192) (q₁ := q₁ L)
      (q₂ := q₂ L) (s := s L) μX μY)
    (μI : PositiveRationalLaw (G × (V ⊕ Aux)))
    (streams : InternalStreams src μI (w L))
    (R₀ : X → Y → Bool)
    (activity : (G × (V ⊕ Aux)) → Fin (q₂ L) → Option (Fin (s L)))
    (ξ₀ : Paper2.SourceMatrix.Tail (s L) Y)
    (d : ℕ) (hd : 3 ≤ d)
    (hprofileA : RestrictionProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      (((PositiveRationalLaw.uniform (Fin (q₁ L))).prod μX).toFiniteLaw)
      (x L : ℝ) ((d+(L+3)/4 : ℕ) : ℤ))
    (hprofileN : RestrictionProfile (Nref src R₀ activity ξ₀)
      (ordinaryLaw src).toFiniteLaw (rowLaw src μI).toFiniteLaw
      (x L : ℝ) ((d+2*((L+3)/4)+4*L : ℕ) : ℤ))
    (R : Set (Fin (w L) × Column src))
    (Yevent : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (P : Protocol Yevent R Bool)
    (hR : 1 - (δU L Δ γ : ℝ) ≤
      (indexedFirstRowLaw src (w_pos L)).prob (· ∈ R))
    (hY : (θ L : ℝ) ≤ streams.law.toFiniteLaw.prob (· ∈ Yevent))
    (hP : P.Computes (fun t row => W src streams R₀ activity ξ₀ t.val row.val))
    (hPcost : P.cost ≤ d+2*((L+3)/4)+6*L) :
    ∃ E : Finset (Fin (w L)),
      E.card ≤ CurrentAdditive.conditioningExceptionCountR 1024
        (θ L : ℝ) ((η L Δ γ : ℝ)/2) ∧
      exceptionBudget E.card ≤ ownerException L Δ γ ∧
      (∀ J : Finset (Fin (w L)),
        J ⊆ Finset.univ \ E → J.card ≤ 8 →
        projectionTV
          (condition streams.law.toFiniteLaw (· ∈ Yevent)
            (lt_of_lt_of_le (by exact_mod_cast theta_pos L) hY))
          (rowLaw src μI).toFiniteLaw
          (InternalStreams.decode src streams) J ≤
            CurrentAdditive.conditioningEpsilonR 1024
              (θ L : ℝ) ((η L Δ γ : ℝ)/2)) ∧
      ∃ row0 : R, ∃ col0 : Yevent,
      ∃ st : State (Fin (w L) × Column src)
        (streams.metadataStream.Label ×
          (streams.baseStream.Label × streams.selectorStream.Label))
        (Fin (w L)) (src.outer.Label × src.gamma.Label),
        st = indexedInitialState src streams R Yevent row0 col0 P E (2*L) ∧
        (let T := run (ordinaryLaw src).toFiniteLaw
          (referenceInput src)
          (Paper2.ReferenceSchedule.floor (w L) (x L : ℝ)) 0 (2*L) st
         let F := fun z : T.Leaves => (T.state z).family
         let final := fun z : T.Leaves => (T.route z).length = 2*L
         let O := ownerNodes F final
         2^(2*L) - exceptionBudget E.card ≤ O.card ∧
         exceptionalCapacity F final
           (fun z => 2^((2*L)-(T.route z).length)) ≤
             exceptionBudget E.card ∧
         ∀ v : T.Leaves,
           (∑ u : {u : T.Leaves // u ∈ O},
             protectedReceipt src (w L) (T.state v).rows
               (origin F final u)) <
             (Kstar L : ℝ) * (2^((2*L)-(T.route v).length) : ℕ)) := by
  obtain ⟨E, hE, hbudget, hTV, row0, col0, st, hst, hcapacity⟩ :=
    indexed_owner_scheduled_conditioned_run src μI L Δ n edges
      sourceC128Ceil γ (by omega) hΔ hγ hadm streams
      R₀ activity ξ₀ R Yevent P (d+2*((L+3)/4)+4*L)
      (by omega) hprofileN hR hY hP (by omega)
  subst st
  have hremote := indexed_incoming_owner_origins_scheduled_run
    L Δ n edges γ hL hadm src μI streams R₀ activity ξ₀
    d hd hprofileA R Yevent row0 col0 P E hY hP hPcost
  refine ⟨E, hE, hbudget, hTV, row0, col0,
    indexedInitialState src streams R Yevent row0 col0 P E (2*L), rfl, ?_⟩
  exact ⟨hcapacity.1, hcapacity.2, hremote⟩

#print axioms indexed_owner_and_incoming_same_E

end CurrentAdditive.DeterministicIndexedMatrix.Sources
