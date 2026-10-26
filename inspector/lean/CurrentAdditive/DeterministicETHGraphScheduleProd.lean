import CurrentAdditive.DeterministicETHActualSchedule
import CurrentAdditive.IndexedSemanticIteration

/-! The public dyadic choice instantiates the fixed source-item repetition
schedule on the exact T10 graph, with no colouring or cost oracle. -/

namespace CurrentAdditive.DeterministicETHGraphSchedule

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open CurrentAdditive.DeterministicParameters
open CurrentAdditive.DeterministicAdmissibility
open Paper2.Unit4Shell.T10Finite
open Paper2.Unit4Shell.T10Size

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

private instance (L : ℕ) : NeZero (s L) := ⟨(s_pos L).ne'⟩

theorem actual_graph_schedule (Φ : ValidFormula) :
    let G := t10Graph D B Φ
    let L := publicLog (max G.vertices Φ.val.variables)
      B.degreeBound (sourceGap D B)
    Nonempty (CurrentAdditive.IndexedSemanticIteration.Schedule
      (Fin G.vertices) (Fin G.edges.length) L) := by
  let G := t10Graph D B Φ
  let L := publicLog (max G.vertices Φ.val.variables)
    B.degreeBound (sourceGap D B)
  have hL : 2004 ≤ L := by
    have hc := publicLog_ge_cutoff (max G.vertices Φ.val.variables)
      B.degreeBound (sourceGap D B)
    unfold sourceCutoffLog cutoffLog at hc
    omega
  have hs : 64 ≤ s L := s_ge_64 L (by omega)
  haveI : Nonempty (Fin G.vertices) := Fin.pos_iff_nonempty.mp (t10_vertices_pos D B Φ)
  haveI : Nonempty (Fin (4*s L)) := Fin.pos_iff_nonempty.mp (by omega)
  haveI : Nonempty (Fin (s L-3)) := Fin.pos_iff_nonempty.mp (by omega)
  haveI : NeZero (s L) := ⟨(s_pos L).ne'⟩
  haveI : NeZero (q₁ L) := ⟨by dsimp [q₁]; omega⟩
  haveI : NeZero (q₂ L) := ⟨(q₂_pos L).ne'⟩
  haveI : NeZero (w L) := ⟨(w_pos L).ne'⟩
  haveI : NeZero (Q L) := ⟨(Q_pos L).ne'⟩
  have hV : G.vertices ≤ N L := by
    have hchosen := chosen_dyadic_size
      (max G.vertices Φ.val.variables) B.degreeBound
      sourceC128Ceil (sourceGap D B)
    exact (le_max_left G.vertices Φ.val.variables).trans hchosen.1
  have hE : 0 < G.edges.length := (t10_source D B Φ).1
  have hdegree : 2 * G.edges.length ≤ B.degreeBound * G.vertices :=
    (t45_relations D B Φ).2.1
  apply CurrentAdditive.IndexedSemanticIteration.schedule_exists
    (L := L) (V := Fin G.vertices) (E := Fin G.edges.length)
    B.degreeBound
  · have hc := publicLog_ge_cutoff (max G.vertices Φ.val.variables)
      B.degreeBound (sourceGap D B)
    unfold sourceCutoffLog cutoffLog at hc
    omega
  · simpa only [Fintype.card_fin] using hV
  · simpa only [Fintype.card_fin] using hE
  · simpa only [Fintype.card_fin] using hdegree

#print axioms actual_graph_schedule

end CurrentAdditive.DeterministicETHGraphSchedule
