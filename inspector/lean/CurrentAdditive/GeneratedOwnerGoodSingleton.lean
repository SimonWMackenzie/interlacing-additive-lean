import CurrentAdditive.GeneratedOwnerGoodPair

/-! Appendix I:501--511 and 683--685: a good conditioned singleton
projection controls deletion in the original one-coordinate row law, even
when the retained complete tuple event has only small mass. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix

variable {G V Aux X Y : Type*}
  [Fintype G] [Fintype V] [Fintype Aux]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  [DecidableEq G] [DecidableEq V] [DecidableEq Aux]
  {D q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  (μI : PositiveRationalLaw (G × (V ⊕ Aux)))

/-- Conditional TV at one good physical coordinate implies that the
original row-law singleton image of the actual retained tuple set loses
at most ε. The full retained tuple set need not have high source mass. -/
theorem owner_singleton_loss_of_projectionTV
    {w : ℕ} (streams : InternalStreams src μI w)
    (U Yevent : Set (InternalLabel src streams))
    (hYU : Yevent ⊆ U)
    (hY : 0 < streams.law.toFiniteLaw.prob (· ∈ Yevent))
    (i : Fin w) (ε : ℝ)
    (hTV : CurrentAdditive.projectionTV
      (CurrentAdditive.condition streams.law.toFiniteLaw
        (· ∈ Yevent) hY)
      (rowLaw src μI).toFiniteLaw
      (InternalStreams.decode src streams)
      (Finset.univ.image (fun _ : Fin 1 => i)) ≤ ε) :
    (rowLaw src μI).toFiniteLaw.prob
      (fun k => k ∉ (InternalStreams.decode src streams · i) '' U) ≤ ε := by
  classical
  let ν := streams.law.toFiniteLaw
  let μ := (rowLaw src μI).toFiniteLaw
  let B : Set (Row (I := G × (V ⊕ Aux)) src) :=
    (InternalStreams.decode src streams · i) '' U
  let e : Fin 1 → Fin w := fun _ => i
  have he : Function.Injective e := by
    intro a b _
    exact Subsingleton.elim a b
  have hcontain (t : InternalLabel src streams) (ht : t ∈ Yevent) :
      InternalStreams.decode src streams t i ∈ B :=
    ⟨t, hYU ht, rfl⟩
  have hconditional :
      (CurrentAdditive.condition ν (· ∈ Yevent) hY).prob
        (fun t => B (InternalStreams.decode src streams t i)) = 1 := by
    rw [CurrentAdditive.condition_prob_event_eq_div]
    have heq : ν.prob (fun t => t ∈ Yevent ∧
        B (InternalStreams.decode src streams t i)) =
        ν.prob (· ∈ Yevent) := by
      congr 1
      funext t
      apply propext
      exact ⟨And.left, fun ht => ⟨ht, hcontain t ht⟩⟩
    rw [heq]
    exact div_self (ne_of_gt hY)
  have htv := CurrentAdditive.injective_projectionTV_event_abs
    (CurrentAdditive.condition ν (· ∈ Yevent) hY) μ
    (InternalStreams.decode src streams) e he ε hTV
    (fun v => B (v 0))
  have hpoint : (fun t => B (InternalStreams.decode src streams t (e 0))) =
      (fun t => B (InternalStreams.decode src streams t i)) := rfl
  simp only [e] at htv
  rw [hconditional] at htv
  have hiid : (μ.iid 1).prob (fun v => B (v 0)) = μ.prob (· ∈ B) := by
    exact Paper2.ReferenceProjectionMass.iid_one_coordinate_prob μ (· ∈ B)
  rw [hiid] at htv
  have hcomp : μ.prob (fun k => k ∉ B) = 1 - μ.prob (· ∈ B) := by
    exact Paper2.SourceProjectionRetention.probability_complement μ (· ∈ B)
  have hh := (abs_le.mp htv).2
  change μ.prob (fun k => k ∉ B) ≤ ε
  rw [hcomp]
  linarith

#print axioms owner_singleton_loss_of_projectionTV

end CurrentAdditive.DeterministicIndexedMatrix.Sources
