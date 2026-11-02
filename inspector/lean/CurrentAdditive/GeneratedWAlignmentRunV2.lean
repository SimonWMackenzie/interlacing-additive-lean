import CurrentAdditive.GeneratedWAlignmentSchedule
import CurrentAdditive.GeneratedWAlignmentInitialDeletion
import CurrentAdditive.GeneratedWReferenceLossV2
import CurrentAdditive.IndexedOwnerGoodOriginsProd
import CurrentAdditive.IndexedOwnerGlobalInitialLoss

/-! Assemble the original indexed-W physical run.  The remaining local cost
and receipt estimates refer to nodes of this exact run and the same retained
tuple event and conditioning exception set. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.ReferenceCertificateTree Paper2.ReferenceOwners
  CurrentAdditive.DeterministicParameters
open scoped BigOperators

variable {G V Aux X Y : Type*}
  [Fintype G] [Fintype V] [Fintype Aux] [Fintype X] [Fintype Y]
  [DecidableEq G] [DecidableEq V] [DecidableEq Aux]
  [DecidableEq X] [DecidableEq Y]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}

theorem indexed_initial_run_mass_contradiction_v2
    (L Δ n m Caux H : ℕ) (γ : ℚ)
    (hL : 1 ≤ L) (hΔ : 0 < Δ) (hγ : 0 < γ)
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
    (row0 : R) (col0 : Yevent) (P : Workspace.Types.Protocol.Protocol Yevent R Bool)
    (E : Finset (Fin (w L)))
    (hadm : Admissible L Δ n m Caux γ)
    (hR : 1 - (δU L Δ γ : ℝ) ≤
      (indexedFirstRowLaw src (w_pos L)).prob (· ∈ R))
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
    (hE : exceptionBudget E.card ≤ ownerException L Δ γ)
    (hnear : ∀ (U : Set (Column src))
      (Vrows : Set (Row (I := G × (V ⊕ Aux)) src)),
      1-(η L Δ γ : ℝ) ≤ (columnLaw src).toFiniteLaw.prob (· ∈ U) →
      1-(η L Δ γ : ℝ) ≤ (rowLaw src μI).toFiniteLaw.prob (· ∈ Vrows) →
      H ≤ Paper2.Compression.restrictionD (N src R₀ activity ξ₀) U Vrows)
    (hcount :
      let st := indexedInitialState src streams R Yevent row0 col0 P E (2*L)
      let T := run (ordinaryLaw src).toFiniteLaw (referenceInput src)
        (Paper2.ReferenceSchedule.floor (w L) (x L : ℝ)) 0 (2*L) st
      let F := fun z : T.Leaves => (T.state z).family
      let final := fun z : T.Leaves => (T.route z).length = 2*L
      2^(2*L) - exceptionBudget E.card ≤ (ownerNodes F final).card ∧
        exceptionalCapacity F final
          (fun z => 2^((2*L)-(T.route z).length)) ≤ exceptionBudget E.card)
    (hcost :
      let st := indexedInitialState src streams R Yevent row0 col0 P E (2*L)
      let T := run (ordinaryLaw src).toFiniteLaw (referenceInput src)
        (Paper2.ReferenceSchedule.floor (w L) (x L : ℝ)) 0 (2*L) st
      let F := fun z : T.Leaves => (T.state z).family
      let final := fun z : T.Leaves => (T.route z).length = 2*L
      ∀ u : {z // z ∈ ownerNodes F final},
        Paper2.Compression.restrictionD (W src streams R₀ activity ξ₀)
          Yevent (T.state u.val).rows < H)
    (hpair :
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
                 (T.state v.val).rows)) + 2 / q₂ L))
    (hremote :
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
  let st := indexedInitialState src streams R Yevent row0 col0 P E (2*L)
  let T := run (ordinaryLaw src).toFiniteLaw (referenceInput src)
    (Paper2.ReferenceSchedule.floor (w L) (x L : ℝ)) 0 (2*L) st
  let F := fun z : T.Leaves => (T.state z).family
  let final := fun z : T.Leaves => (T.route z).length = 2*L
  let O := ownerNodes F final
  let orig : O → Fin (w L) := origin F final
  let defect : O → ℝ := fun v =>
    1 - (ordinaryLaw src).toFiniteLaw.prob
      (fun z => (orig v, Column.ordinary z) ∈ (T.state v.val).rows)
  let delta : O → ℝ := fun v =>
    2 * q₂ L * (x L : ℝ) + 5 * defect v + 2 / q₂ L
  have hη : (0 : ℝ) < (η L Δ γ : ℝ) := by
    exact_mod_cast eta_pos L Δ γ hΔ hγ
  have hθpos : (0 : ℝ) < (θ L : ℝ) := by
    exact_mod_cast theta_pos L
  have hYpos : 0 < streams.law.toFiniteLaw.prob (· ∈ Yevent) :=
    hθpos.trans_le hY
  have hw : w L = 2^(2*L) := w_eq_pow L
  have hw2 : 2 ≤ w L := by
    rw [hw]
    have he : 1 ≤ 2*L := by omega
    exact (by decide : 2 ≤ 2^1).trans
      (Nat.pow_le_pow_right (by decide) he)
  have hcount' : w L - exceptionBudget E.card ≤ O.card := by
    simpa [st, T, F, final, O, hw] using hcount.1
  have hcap' : (∑ v ∈ Finset.univ \ O,
      2^((2*L)-(T.route v).length)) ≤ exceptionBudget E.card := by
    have hc := hcount.2
    change (∑ v : T.Leaves,
      if v ∈ O then 0 else 2^((2*L)-(T.route v).length)) ≤
        exceptionBudget E.card at hc
    simpa only [Finset.sum_ite, Finset.sum_const_zero, zero_add,
      Finset.filter_notMem_eq_sdiff] using hc
  have hE4 : 4 * exceptionBudget E.card ≤ w L := by
    exact (Nat.mul_le_mul_left 4 hE).trans hadm.owner_reserve
  have hinj : Function.Injective orig := by
    exact run_origin_injective (ordinaryLaw src).toFiniteLaw
      (referenceInput src) (Paper2.ReferenceSchedule.floor (w L) (x L : ℝ))
      (2*L) st
  have hR' : 1 - (η L Δ γ : ℝ) / (16 * (w L : ℝ)) ≤
      (indexedFirstRowLaw src (w_pos L)).prob (· ∈ R) := by
    simpa [indexed_owner_public_row_threshold L Δ γ] using hR
  have hinit := indexed_initial_ordinary_loss_sum src (w_pos L)
    R E (η L Δ γ : ℝ) hR'
  have hvalid : st.family.unsplit ⊆ st.family.active :=
    indexedInitialFamily_valid src R E
  have hreach : ∀ i ∈ st.family.active, ∀ z ∈ st.family.support i,
      (i,Column.ordinary z) ∈ st.rows :=
    indexedInitialFamily_reaches src R E
  have hsquare : 2 * (w L : ℝ)^2 * (x L : ℝ) ≤
      (η L Δ γ : ℝ) / (16 * (127/128 : ℝ)) := by
    have h : (((2 * (w L : ℚ)^2 * x L : ℚ) : ℝ)) ≤
        ((η L Δ γ / (16 * (127/128 : ℚ)) : ℚ) : ℝ) :=
      Rat.cast_le.mpr hadm.square_x
    norm_num at h ⊢
    exact h
  have hdefect : Finset.univ.sum defect ≤
      (η L Δ γ : ℝ) / (8 * (127/128 : ℝ)) := by
    have h := indexed_run_owner_ordinary_loss src st (2*L)
      (x L : ℝ) (η L Δ γ : ℝ) hw (x_real_pos L).le
      hsquare hvalid hreach hinit
    simpa [st, T, F, final, O, orig, defect, referenceInput] using h
  have hdelete : Finset.univ.sum (fun u : O =>
      protectedDeleted src st.rows (orig u)) ≤ (η L Δ γ : ℝ)/16 := by
    have hRuniform : 1 - (η L Δ γ : ℝ)/(16*(w L : ℝ)) ≤
        (((PositiveRationalLaw.uniform (Fin (w L))).prod
          (columnLaw src)).toFiniteLaw).prob (· ∈ st.rows) := by
      simpa [st, indexedFirstRowLaw] using hR'
    exact indexed_owner_protected_deleted_le src
      (ordinaryLaw src).toFiniteLaw (referenceInput src)
      (Paper2.ReferenceSchedule.floor (w L) (x L : ℝ)) 0 (2*L)
      st O orig hinj (η L Δ γ : ℝ) hRuniform
  have hscalar := indexed_alignment_public_scalar_bounds L Δ n m Caux γ
    hΔ hγ hadm defect (by simpa [O] using
      (Fintype.card_le_of_injective orig hinj)) hdefect
  have hTVowner : ∀ u : O,
      projectionTV
        (condition streams.law.toFiniteLaw (· ∈ Yevent) hYpos)
        (rowLaw src μI).toFiniteLaw (InternalStreams.decode src streams)
        (Finset.univ.image (fun _ : Fin 1 => orig u)) ≤
          CurrentAdditive.conditioningEpsilonR 1024
            (θ L : ℝ) ((η L Δ γ : ℝ)/2) := by
    intro u
    have hh := indexed_initial_owner_singletonTV src streams
      (rowLaw src μI) R Yevent row0 col0 P E (2*L) (x L : ℝ)
      (CurrentAdditive.conditioningEpsilonR 1024
        (θ L : ℝ) ((η L Δ γ : ℝ)/2)) hYpos hTV st rfl u
    simpa [st, T, F, final, O, orig] using hh
  have hε : CurrentAdditive.conditioningEpsilonR 1024
      (θ L : ℝ) ((η L Δ γ : ℝ)/2) ≤ (η L Δ γ : ℝ)/2 := by
    exact owner_conditioning_epsilon_le_eta_half
      (θ L : ℝ) (η L Δ γ : ℝ)
  have hδpoint : ∀ v : O, 0 ≤ delta v := by
    intro v
    have hp := (ordinaryLaw src).toFiniteLaw.prob_le_one
      (fun z => (orig v, Column.ordinary z) ∈ (T.state v.val).rows)
    dsimp [delta, defect]
    have hq : (0 : ℝ) < q₂ L := by exact_mod_cast NeZero.pos (q₂ L)
    have hd : 0 ≤ 1 - (ordinaryLaw src).toFiniteLaw.prob
        (fun z => (orig v, Column.ordinary z) ∈ (T.state v.val).rows) := by
      linarith
    have hx : (0 : ℝ) ≤ (x L : ℝ) := (x_real_pos L).le
    have hqR : (0 : ℝ) < (q₂ L : ℝ) := by exact_mod_cast hq
    have hratio : (0 : ℝ) ≤ 2 / q₂ L := by positivity
    have hterm : (0 : ℝ) ≤ 2 * q₂ L * (x L : ℝ) := by positivity
    nlinarith
  have hδ : 0 ≤ Finset.univ.sum delta :=
    Finset.sum_nonneg (fun v _ => hδpoint v)
  have hK : 0 ≤ (Kstar L : ℝ) := by unfold Kstar; positivity
  have hEreal : (exceptionBudget E.card : ℝ) ≤
      (ownerException L Δ γ : ℝ) := by exact_mod_cast hE
  have hcapscalar : (Kstar L : ℝ) * exceptionBudget E.card ≤
      (η L Δ γ : ℝ) * w L / 16 :=
    (mul_le_mul_of_nonneg_left hEreal hK).trans hscalar.2.1
  exact indexed_run_mass_contradiction src
    (ordinaryLaw src).toFiniteLaw (referenceInput src)
    (Paper2.ReferenceSchedule.floor (w L) (x L : ℝ)) 0 (2*L) st
    μI streams R₀ activity ξ₀ H Yevent O orig
    (η L Δ γ : ℝ) (1/256 : ℝ) (Kstar L : ℝ)
    (exceptionBudget E.card)
    (fun v => 2^((2*L)-(T.route v).length)) delta
    hη hw2 hE4 hcount' hinj hnear hYpos
    _ hε hTVowner hcost hdefect hdelete hpair hδpoint hδ
    (by norm_num) hscalar.2.2 hremote hK hcap'
    hcapscalar

#print axioms indexed_initial_run_mass_contradiction_v2

end CurrentAdditive.DeterministicIndexedMatrix.Sources
