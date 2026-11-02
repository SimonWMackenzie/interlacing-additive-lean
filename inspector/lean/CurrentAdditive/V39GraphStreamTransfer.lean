import CurrentAdditive.V39CompleteStreams
import CurrentAdditive.V39StreamAveraging
import CurrentAdditive.V38Matrix

/-! The source's actual graph item labels, complete K^w law, retained
events, and the same actual Boolean matrix through the stream decoder. -/

namespace CurrentAdditive.V39GraphStreamTransfer

open Paper2 Paper2.SourceMatrix
open V39CompleteStreams

variable {X V : Type*} [Fintype X] [Fintype V] [Nonempty V]
  {q₁ q₂ s : ℕ} [NeZero q₁] [NeZero s]

abbrev GraphLabel (w : ℕ) :=
  V39CompleteStreams.Label (X := X) (V := Fin (4*s) × V)
    (A := Fin (4*s) × Fin (s-3)) (q₁ := q₁) (q₂ := q₂) (s := s) w

def graphDecode {w : ℕ}
    (a : GraphLabel (X := X) (V := V) (q₁ := q₁) (q₂ := q₂) (s := s) w) :=
  fun i => SourceLawBinding.rawRowEquiv q₁ q₂ s X V (V39CompleteStreams.decode a i)

noncomputable def graphLaw (μ : PositiveRationalLaw X) (hs : 4 ≤ s) (w : ℕ) :
    PositiveRationalLaw
      (GraphLabel (X := X) (V := V) (q₁ := q₁) (q₂ := q₂) (s := s) w) := by
  letI : Nonempty (Fin (4*s)) := ⟨⟨0,by omega⟩⟩
  letI : Nonempty (Fin (s-3)) := ⟨⟨0,by omega⟩⟩
  exact V39CompleteStreams.law μ w

/-- The actual graph's K law, not a carrier with split item labels. Its
columnLaw is exactly the selected V38/V39 matrix column law. -/
theorem graph_decode_pushes (μ : PositiveRationalLaw X) (hs : 4 ≤ s) (w : ℕ) :
    (graphLaw (V := V) (q₁ := q₁) (q₂ := q₂) μ hs w).toFiniteLaw.PushesTo
      ((V38Matrix.columnLaw (V := V) (q₁ := q₁) (q₂ := q₂) μ hs).iid w).toFiniteLaw
      graphDecode := by
  letI : Nonempty (Fin (4*s)) := ⟨⟨0,by omega⟩⟩
  letI : Nonempty (Fin (s-3)) := ⟨⟨0,by omega⟩⟩
  let α := SourceLaws.rowLaw (V := Fin (4*s) × V)
    (A := Fin (4*s) × Fin (s-3)) μ q₁ q₂ s
  let β := V38Matrix.columnLaw (V := V) (q₁ := q₁) (q₂ := q₂) μ hs
  let e := SourceLawBinding.rawRowEquiv q₁ q₂ s X V
  have he : α.toFiniteLaw.PushesTo β.toFiniteLaw e := by
    intro E
    exact (PositiveRationalLaw.relabel_prob α e E).symm
  intro E
  calc
    _ = (α.iid w).toFiniteLaw.prob (fun a => E (fun i => e (a i))) :=
      V39CompleteStreams.decode_full_pushes μ w (fun a => E (fun i => e (a i)))
    _ = _ := V39CompleteStreams.iid_map_pushes α β e he w E

theorem graph_retained_mass (μ : PositiveRationalLaw X) (hs : 4 ≤ s) (w : ℕ)
    (Y : Set (Fin w → RawRow q₁ q₂ s X (EdgeSourceMatrix.Items s V))) :
    (graphLaw (V := V) μ hs w).toFiniteLaw.prob (fun a => graphDecode a ∈ Y) =
      ((V38Matrix.columnLaw (V := V) μ hs).iid w).toFiniteLaw.prob (· ∈ Y) :=
  graph_decode_pushes μ hs w (· ∈ Y)

/-- Every actual K^w tuple has an auxiliary completion, even at w=0. -/
theorem graph_decode_surjective (μ : PositiveRationalLaw X) (hs : 4 ≤ s) (w : ℕ) :
    Function.Surjective
      (graphDecode (X := X) (V := V) (q₁ := q₁) (q₂ := q₂) (s := s) (w := w)) :=
  V39StreamAveraging.surjective_of_positive_pushes
    (graphLaw (V := V) μ hs w).toFiniteLaw
    ((V38Matrix.columnLaw (V := V) μ hs).iid w) graphDecode
    (graph_decode_pushes μ hs w)

section Protocol

open Workspace.Types.Protocol

variable {Z : Type*} [Fintype Z] {w : ℕ}

/-- For any source matrix F (and hence the actual two-tag N), the complete
stream protocol computes its exact entry and has precisely the old depth. -/
theorem graph_protocol_pullback
    (F : Z → RawRow q₁ q₂ s X (EdgeSourceMatrix.Items s V) → Bool)
    (R : Set (Fin w × Z))
    (Y : Set (Fin w → RawRow q₁ q₂ s X (EdgeSourceMatrix.Items s V)))
    (P : Protocol Y R Bool)
    (hP : P.Computes (fun a z => F z.val.2 (a.val z.val.1))) :
    ∃ Q : Protocol (graphDecode ⁻¹' Y) R Bool,
      Q.cost = P.cost ∧
      Q.Computes (fun a z => F z.val.2 (graphDecode a.val z.val.1)) := by
  let f : (graphDecode ⁻¹' Y) → Y := fun a => ⟨graphDecode a.val,a.property⟩
  let Q := Workspace.UpperBound.Protocol.comap f id P
  refine ⟨Q,Workspace.UpperBound.Protocol.comap_cost _ _ P,?_⟩
  intro a z
  simpa [Q,Workspace.UpperBound.Protocol.comap_eval] using hP (f a) z

/-- Exact restricted communication cost after retaining all auxiliary
completions of the already selected actual event. -/
theorem graph_restriction_cost (μ : PositiveRationalLaw X) (hs : 4 ≤ s)
    (F : Z → RawRow q₁ q₂ s X (EdgeSourceMatrix.Items s V) → Bool)
    (R : Set (Fin w × Z))
    (Y : Set (Fin w → RawRow q₁ q₂ s X (EdgeSourceMatrix.Items s V))) :
    Compression.restrictionD
        (fun a z => F z.2 (graphDecode a z.1)) (graphDecode ⁻¹' Y) R =
      Compression.restrictionD (fun a z => F z.2 (a z.1)) Y R := by
  exact restrictionD_pullback_preimage
    (fun a z => F z.2 (a z.1)) graphDecode id
    (graph_decode_surjective μ hs w) Function.surjective_id Y R

end Protocol

end CurrentAdditive.V39GraphStreamTransfer

#print axioms CurrentAdditive.V39GraphStreamTransfer.graph_decode_pushes
#print axioms CurrentAdditive.V39GraphStreamTransfer.graph_retained_mass
#print axioms CurrentAdditive.V39GraphStreamTransfer.graph_decode_surjective
#print axioms CurrentAdditive.V39GraphStreamTransfer.graph_protocol_pullback
#print axioms CurrentAdditive.V39GraphStreamTransfer.graph_restriction_cost
