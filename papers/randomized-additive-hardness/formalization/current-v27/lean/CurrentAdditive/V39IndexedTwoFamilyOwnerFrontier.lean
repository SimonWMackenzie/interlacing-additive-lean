import CurrentAdditive.V39IndexedTwoFamilyRun
import CurrentAdditive.V39OwnerSourceCost

/-! The current owner and loss conclusions are derived on one computed
protocol frontier. The source near-full input is the source theorem, not
the desired internal-interlace conclusion. Local support obstructions are
kept explicit pending the current Fin-2/source-law adapters. -/

namespace CurrentAdditive.V39IndexedTwoFamilyOwnerFrontier

open Paper2 Paper2.SourceMatrix Paper2.ReferenceCertificates
open Paper2.ReferenceCertificateTree Paper2.ReferenceCertificateProtocol
open Paper2.ReferenceOwners CurrentAdditive.V39IndexedTwoFamilyRun
open scoped BigOperators Classical

variable {X Y I T : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I]
  {q₁ q₂ s w : ℕ} [NeZero q₁] [NeZero s] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : CurrentAdditive.DeterministicIndexedMatrix.Sources
    (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

variable {A : Type*} [Fintype T] [Fintype A]


theorem owner_frontier  (rawLaw : FiniteLaw A)
    (source : Columns src → A → Bool)
    (decode : T → Fin w → A) (Yevent : Set T)
    (R : Set (Rows src (w := w)))
    (P : Workspace.Types.Protocol.Protocol
      (Rows src (w := w)) T Bool)
    (E : Finset (Fin w)) (r e0 H : ℕ) (η x : ℝ)
    (hw : 0 < w) (hwr : w=2^r) (hH : 1 ≤ H) (hE : E.card ≤ e0)
    (hsmallE : 4*(2*e0) ≤ w) (hx : 0 ≤ x)
    (hR : 1-η/(16*w) ≤ (firstRowLaw src hw).prob (· ∈ R))
    (hsmall : 2*(w : ℝ)^2*x ≤ η/(16*(255/256 : ℝ)))
    (hnearfull : ∀ (U : Set (Columns src))
      (V : Set A), 1-η ≤ (V38IndexedTwoTag.law src).toFiniteLaw.prob (· ∈ U) →
      1-η ≤ rawLaw.prob (· ∈ V) → H ≤ Compression.restrictionD source U V)
    (hprojection : ∀ i ∉ E,
      1-η ≤ rawLaw.prob (· ∈ V39OwnerSourceCost.projection decode Yevent i))
    (hcompute : ∀ row ∈ R, ∀ t ∈ Yevent, P.eval row t=source row.2 (decode t row.1))
    (hbudget : P.cost ≤ H+r-1)
    (hfinal : ∀ v : (run (CurrentAdditive.DeterministicIndexedMatrix.Sources.ordinaryLaw src).toFiniteLaw (input src)
      (Paper2.ReferenceSchedule.floor w x) 0 r (initialState src R P E r)).Leaves,
      ((run (CurrentAdditive.DeterministicIndexedMatrix.Sources.ordinaryLaw src).toFiniteLaw (input src)
        (Paper2.ReferenceSchedule.floor w x) 0 r (initialState src R P E r)).route v).length=r →
      ((run (CurrentAdditive.DeterministicIndexedMatrix.Sources.ordinaryLaw src).toFiniteLaw (input src)
        (Paper2.ReferenceSchedule.floor w x) 0 r (initialState src R P E r)).state v).family.active.card ≤ 1)
    (hbob : ∀ v : (run (CurrentAdditive.DeterministicIndexedMatrix.Sources.ordinaryLaw src).toFiniteLaw (input src)
      (Paper2.ReferenceSchedule.floor w x) 0 r (initialState src R P E r)).Leaves,
      ((run (CurrentAdditive.DeterministicIndexedMatrix.Sources.ordinaryLaw src).toFiniteLaw (input src)
        (Paper2.ReferenceSchedule.floor w x) 0 r (initialState src R P E r)).route v).length≠r →
      units ((run (CurrentAdditive.DeterministicIndexedMatrix.Sources.ordinaryLaw src).toFiniteLaw (input src)
        (Paper2.ReferenceSchedule.floor w x) 0 r (initialState src R P E r)).state v).family ≤
      2^(r-((run (CurrentAdditive.DeterministicIndexedMatrix.Sources.ordinaryLaw src).toFiniteLaw (input src)
        (Paper2.ReferenceSchedule.floor w x) 0 r (initialState src R P E r)).route v).length)) :
    let st := initialState src R P E r
    let μ := (CurrentAdditive.DeterministicIndexedMatrix.Sources.ordinaryLaw src).toFiniteLaw
    let tr := run μ (input src) (Paper2.ReferenceSchedule.floor w x) 0 r st
    let F := fun v : tr.Leaves => (tr.state v).family
    let final := fun v : tr.Leaves => (tr.route v).length=r
    let O := ownerNodes F final
    let Owners := {v : tr.Leaves // v ∈ O}
    (3/4 : ℝ)*w ≤ O.card ∧ O.card ≤ w ∧
      exceptionalCapacity F final (fun v => 2^(r-(tr.route v).length)) ≤ 2*e0 ∧
      (∑ v : Owners, (1-μ.prob
        (fun Z => input src (origin F final v) Z ∈ (tr.state v.val).rows))) ≤ η/(8*(255/256 : ℝ)) ∧
      ∀ v : Owners, η < 1-(V38IndexedTwoTag.law src).toFiniteLaw.prob
        (fun c => (origin F final v,c) ∈ (tr.state v.val).rows) := by
  classical
  dsimp only
  let st := initialState src R P E r
  let μ := (CurrentAdditive.DeterministicIndexedMatrix.Sources.ordinaryLaw src).toFiniteLaw
  let tr := run μ (input src) (Paper2.ReferenceSchedule.floor w x) 0 r st
  let F := fun v : tr.Leaves => (tr.state v).family
  let final := fun v : tr.Leaves => (tr.route v).length=r
  let O := ownerNodes F final
  let Owners := {v : tr.Leaves // v ∈ O}
  have hvalid : st.family.unsplit ⊆ st.family.active := initial_valid src R E
  have hprefix : Paper2.ReferencePrefix.NoEarlyLeaf r st.protocol :=
    Paper2.ReferencePrefix.padAlicePrefix_noEarlyLeaf r P
  have hEw : E.card ≤ w := by simpa using Finset.card_le_card (Finset.subset_univ E)
  have hinit : 2^r ≤ w-E.card+e0 := by rw [← hwr]; omega
  have hu : 2*(w-E.card) ≤ units st.family := by
    change 2*(w-E.card) ≤ units (initialFamily src R E)
    rw [V39IndexedTwoFamilyRun.initial_units]
  obtain ⟨hcount,hexcept⟩ := V39ReferenceOwnersSharp.run_owner_count μ (input src)
    (Paper2.ReferenceSchedule.floor w x) r st (w-E.card) e0
    hvalid hprefix hinit hu hfinal hbob
  have hcount' : (3/4 : ℝ)*w ≤ O.card := by
    change 2^r-2*e0 ≤ O.card at hcount
    rw [← hwr] at hcount
    have hn : 3*w ≤ 4*O.card := by omega
    have hnR : (3 : ℝ)*(w : ℝ) ≤ 4*(O.card : ℝ) := by exact_mod_cast hn
    simp only [CurrentAdditive.DeterministicIndexedMatrix.Sources.ordinaryLaw, CurrentAdditive.DeterministicIndexedMatrix.Sources.diagonalLaw] at *
    linarith
  have hcard : O.card ≤ w := by
    have hh := Fintype.card_le_of_injective (origin F final)
      (run_origin_injective μ (input src) (Paper2.ReferenceSchedule.floor w x) r st)
    change Fintype.card Owners ≤ Fintype.card (Fin w) at hh
    simpa only [Owners, Fintype.card_coe, Fintype.card_fin] using hh
  have hloss := run_reference_loss src hw r hwr R P E η x hx hR hsmall
  refine ⟨hcount',hcard,hexcept,hloss,?_⟩
  intro v
  have hmem := run_origin_mem_initial μ (input src) (Paper2.ReferenceSchedule.floor w x) r st v
  have hout : origin F final v ∉ E := by
    change origin F final v ∈ Finset.univ \ E at hmem
    exact (Finset.mem_sdiff.mp hmem).2
  have hcomp : ∀ row ∈ (tr.state v.val).rows, ∀ t ∈ Yevent,
      (tr.state v.val).protocol.eval row t=source row.2 (decode t row.1) := by
    apply Paper2.ReferenceRunCorrectness.computes_on_original_rectangle
      μ (input src) (Paper2.ReferenceSchedule.floor w x) 0 r st
      (fun row t => source row.2 (decode t row.1)) Yevent _ v.val
    intro row hr t ht
    rw [show st.protocol=Paper2.ReferencePrefix.padAlicePrefix r P by rfl,
      Paper2.ReferencePrefix.padAlicePrefix_eval]
    exact hcompute row hr t ht
  have hnodecost : (tr.state v.val).protocol.cost < H := by
    have hc := run_cost_add_length μ (input src) (Paper2.ReferenceSchedule.floor w x) 0 r st v.val
    have hpad := Paper2.ReferencePrefix.padAlicePrefix_cost_le r P
    have hf := ((mem_ownerNodes F final v.val).mp v.property).1
    change (tr.route v.val).length=r at hf
    change (tr.state v.val).protocol.cost+(tr.route v.val).length ≤
      (Paper2.ReferencePrefix.padAlicePrefix r P).cost at hc
    rw [hf] at hc
    omega
  exact V39OwnerSourceCost.owner_misses_source_mass
    (V38IndexedTwoTag.law src).toFiniteLaw rawLaw source decode Yevent (tr.state v.val).rows
    (origin F final v) (tr.state v.val).protocol η H hnearfull
    (hprojection _ hout) (fun c hc t ht => hcomp _ hc t ht) hnodecost

end CurrentAdditive.V39IndexedTwoFamilyOwnerFrontier

#print axioms CurrentAdditive.V39IndexedTwoFamilyOwnerFrontier.owner_frontier
