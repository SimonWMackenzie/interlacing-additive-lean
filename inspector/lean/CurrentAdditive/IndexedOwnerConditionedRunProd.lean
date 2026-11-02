import CurrentAdditive.IndexedOwnerInitializedRun
import CurrentAdditive.GeneratedOwnerConditionedProjectionsClean
import CurrentAdditive.ConditioningGeneralComplete

/-! The actual original-row and complete-stream conditioning inputs to the
Appendix I owner initializer.  One exceptional set is used by both the
owner count and later incoming/protected mass arguments. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix Paper2.ReferenceCertificates Paper2.ReferenceCertificateTree
  Paper2.ReferenceOwners Workspace.Types.Protocol

variable {G V Aux X Y : Type*}
  [Fintype G] [Fintype V] [Fintype Aux]
  [Fintype X] [Fintype Y]
  [DecidableEq G] [DecidableEq V] [DecidableEq Aux]
  [DecidableEq X] [DecidableEq Y]
  {q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  (μI : PositiveRationalLaw (G × (V ⊕ Aux)))
  {w : ℕ} (streams : InternalStreams src μI w)

theorem indexed_owner_conditioned_run
    (R₀ : X → Y → Bool)
    (activity : (G × (V ⊕ Aux)) → Fin q₂ → Option (Fin s))
    (ξ₀ : Paper2.SourceMatrix.Tail s Y)
    (R : Set (Fin w × Column src))
    (Yevent : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (P : Protocol Yevent R Bool)
    (r H : ℕ) (η x θ : ℝ)
    (hw : w = 2^r) (hrpos : 1 ≤ r) (hd : 2 ≤ H)
    (hx : 0 < x) (hη : 0 < η) (hθ : 0 < θ)
    (hscale : ∀ a ≤ r, (2 : ℝ)^a * x ≤ 1)
    (hprofile : RestrictionProfile
      (Nref src R₀ activity ξ₀)
      (ordinaryLaw src).toFiniteLaw (rowLaw src μI).toFiniteLaw x (H : ℤ))
    (hR : 1 - η / (16 * w) ≤
      (indexedFirstRowLaw src (by rw [hw]; positivity)).prob (· ∈ R))
    (hmargin : 2*w*x + η / (16 * (127 / 128 : ℝ)) < 1)
    (hY : θ ≤ streams.law.toFiniteLaw.prob (· ∈ Yevent))
    (hP : P.Computes (fun t row => W src streams R₀ activity ξ₀ t.val row.val))
    (hPcost : P.cost ≤ H+r) :
    ∃ E : Finset (Fin w),
      E.card ≤ CurrentAdditive.conditioningExceptionCountR 1024 θ (η/2) ∧
      (∀ J : Finset (Fin w),
        J ⊆ Finset.univ \ E → J.card ≤ 8 →
        projectionTV
          (condition streams.law.toFiniteLaw (· ∈ Yevent)
            (hθ.trans_le hY)) (rowLaw src μI).toFiniteLaw
          (InternalStreams.decode src streams) J ≤
            CurrentAdditive.conditioningEpsilonR 1024 θ (η/2)) ∧
      ∃ row0 : R, ∃ col0 : Yevent,
        ∃ st : State (Fin w × Column src)
          (streams.metadataStream.Label ×
            (streams.baseStream.Label × streams.selectorStream.Label))
          (Fin w) (src.outer.Label × src.gamma.Label),
          st = indexedInitialState src streams R Yevent row0 col0 P E r ∧
          (let T := run (ordinaryLaw src).toFiniteLaw
            (referenceInput src) (Paper2.ReferenceSchedule.floor w x) 0 r st
          let F := fun z : T.Leaves => (T.state z).family
          let final := fun z : T.Leaves => (T.route z).length = r
          2^r - exceptionBudget E.card ≤ (ownerNodes F final).card ∧
            exceptionalCapacity F final
              (fun z => 2^(r-(T.route z).length)) ≤
              exceptionBudget E.card) := by
  classical
  have hwise : IsDWise (8 * 1024) streams.law.toFiniteLaw
      (InternalStreams.decode src streams) (rowLaw src μI).toFiniteLaw := by
    simpa using internal_streams_row_dwise src μI streams
  obtain ⟨E, hEcard, hTV⟩ :=
    CurrentAdditive.conditioning_exceptional_coordinates_R
      (by decide : Even 1024) (by decide : 8 ≤ 1024)
      streams.law.toFiniteLaw (rowLaw src μI).toFiniteLaw
      (InternalStreams.decode src streams) (· ∈ Yevent)
      θ (η/2) hθ hY (by linarith) hwise
  have hεpos : 0 < CurrentAdditive.conditioningEpsilonR 1024 θ (η/2) :=
    CurrentAdditive.conditioningEpsilonR_pos (by decide : 8 ≤ 1024)
      hθ (by linarith)
  have hεcap : CurrentAdditive.conditioningEpsilonR 1024 θ (η/2) ≤
      (2 : ℝ)^(-20 : ℤ) / 1024 * θ^((1 : ℝ)/256) := by
    unfold CurrentAdditive.conditioningEpsilonR
    convert min_le_right (η/2)
      ((2 : ℝ)^(-(20 : ℝ)) / 1024 * θ^((4 : ℝ)/1024)) using 1 <;>
      norm_num
  obtain ⟨row0, col0, st, hst, hcount⟩ :=
    indexed_initialised_owner_capacity src streams (rowLaw src μI)
      R₀ activity ξ₀ R Yevent P E r H η x θ
      (CurrentAdditive.conditioningEpsilonR 1024 θ (η/2))
      hw hrpos hd hx hscale hprofile hwise hR hmargin hθ hY
      hεpos hεcap hTV hP hPcost
  exact ⟨E, hEcard, hTV, row0, col0, st, hst, hcount⟩

#print axioms indexed_owner_conditioned_run

end CurrentAdditive.DeterministicIndexedMatrix.Sources
