import CurrentAdditive.IndexedOwnerInitialState
import Paper2.ReferenceRunCorrectness
import Paper2.PairedSelectorCapacityFibre
import Paper2.SourceProjection
import Paper2.ReferenceOwners

/-! At a final owner of the actual padded Alice-prefix run, the remaining
protocol has paid the full index-address cost. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.ReferenceCertificateTree Paper2.ReferenceOwners
  Paper2.ReferenceCertificateProtocol

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  {μI : PositiveRationalLaw I} {w : ℕ}
  (streams : InternalStreams src μI w)

theorem indexed_initial_final_restriction_le
    (R₀ : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Paper2.SourceMatrix.Tail s Y)
    (R : Set (Fin w × Column src))
    (Yevent : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (row0 : R) (col0 : Yevent)
    (P : Workspace.Types.Protocol.Protocol Yevent R Bool)
    (E : Finset (Fin w)) (r H : ℕ) (x : ℝ)
    (hP : P.Computes (fun t row => W src streams R₀ activity ξ₀ t.val row.val))
    (hPcost : P.cost ≤ H+r) :
    let st := indexedInitialState src streams R Yevent row0 col0 P E r
    let T := run (ordinaryLaw src).toFiniteLaw (referenceInput src)
      (Paper2.ReferenceSchedule.floor w x) 0 r st
    let F := fun z : T.Leaves => (T.state z).family
    let final := fun z : T.Leaves => (T.route z).length = r
    ∀ u : {z // z ∈ ownerNodes F final},
      Paper2.Compression.restrictionD (W src streams R₀ activity ξ₀)
        Yevent (T.state u.val).rows ≤ H := by
  classical
  intro st T F final u
  have hstcost : st.protocol.cost ≤ H+r :=
    indexedInitialState_cost src streams R Yevent row0 col0 P E r H hPcost
  have hc := Paper2.ReferenceRunCorrectness.remaining_cost
    (ordinaryLaw src).toFiniteLaw (referenceInput src)
    (Paper2.ReferenceSchedule.floor w x) r H st hstcost u.val
  have hfinal : (T.route u.val).length = r :=
    (mem_ownerNodes F final u.val).mp u.property |>.1
  have hnodecost : (T.state u.val).protocol.cost ≤ H := by
    change (T.state u.val).protocol.cost ≤
      H + (r - (T.route u.val).length) at hc
    simpa [hfinal] using hc
  have hcompute0 : ∀ row ∈ st.rows, ∀ t ∈ Yevent,
      st.protocol.eval row t = W src streams R₀ activity ξ₀ t row := by
    intro row hr t ht
    exact indexedInitialState_correct src streams R₀ activity ξ₀
      R Yevent row0 col0 P hP E r ⟨row,hr⟩ ⟨t,ht⟩
  have hcompute := Paper2.ReferenceRunCorrectness.computes_on_original_rectangle
    (ordinaryLaw src).toFiniteLaw (referenceInput src)
    (Paper2.ReferenceSchedule.floor w x) 0 r st
    (fun row t => W src streams R₀ activity ξ₀ t row)
    Yevent hcompute0 u.val
  let Q := Workspace.UpperBound.Protocol.comap
    (fun row : (T.state u.val).rows => row.val)
    (fun t : Yevent => t.val) (T.state u.val).protocol
  have hQ : Q.Computes (fun row t =>
      W src streams R₀ activity ξ₀ t.val row.val) := by
    intro row t
    rw [Workspace.UpperBound.Protocol.comap_eval]
    exact hcompute row.val row.property t.val t.property
  have hbound := Paper2.PairedSelectorCapacityFibre.restrictionD_le_protocol
    (fun row t => W src streams R₀ activity ξ₀ t row)
    (T.state u.val).rows Yevent Q hQ
  have hQcost : Q.cost ≤ H := by
    simpa [Q, Workspace.UpperBound.Protocol.comap_cost] using hnodecost
  have hbound' : Paper2.Compression.restrictionD
      (fun row t => W src streams R₀ activity ξ₀ t row)
      (T.state u.val).rows Yevent ≤ H := by
    exact hbound.trans hQcost
  exact (Paper2.SourceProjection.restrictionD_transpose
    (W src streams R₀ activity ξ₀) Yevent (T.state u.val).rows).symm.trans_le
      hbound'

#print axioms indexed_initial_final_restriction_le

end CurrentAdditive.DeterministicIndexedMatrix.Sources
