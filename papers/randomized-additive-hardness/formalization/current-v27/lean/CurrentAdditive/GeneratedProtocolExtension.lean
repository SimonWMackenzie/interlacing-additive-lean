import CurrentAdditive.GeneratedNearFullPrefixBridge

/-!
An actual restriction protocol has columns in the retained subtype.  The
frontier needs the same protocol tree on all tagged columns.  Extend column
queries by sending deleted columns to one fixed retained column; on retained
inputs evaluation, row-prefix labels, prefix shape and cost are unchanged.
-/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Workspace.Types.Protocol
open Paper2.SourceProtocolPrefix

variable {A B : Type*} (V : Set A) (U : Set B)

noncomputable def extendColumn (hU : U.Nonempty) : B → U := by
  classical
  exact fun b => if h : b ∈ U then ⟨b, h⟩ else ⟨Classical.choose hU,
    Classical.choose_spec hU⟩

noncomputable def extendColumnProtocol (hU : U.Nonempty)
    (P : Protocol V U Bool) : Protocol V B Bool :=
  NPCC.Protocol.pullback id (extendColumn U hU) P

theorem extendColumnProtocol_eval (hU : U.Nonempty)
    (P : Protocol V U Bool) (v : V) (b : B) (hb : b ∈ U) :
    (extendColumnProtocol V U hU P).eval v b = P.eval v ⟨b, hb⟩ := by
  classical
  simp [extendColumnProtocol, NPCC.Protocol.pullback_eval,
    extendColumn, dif_pos hb]

theorem extendColumnProtocol_cost (hU : U.Nonempty)
    (P : Protocol V U Bool) :
    (extendColumnProtocol V U hU P).cost = P.cost := by
  simp [extendColumnProtocol, NPCC.Protocol.pullback_cost]

theorem extendColumnProtocol_prefix (hU : U.Nonempty)
    (P : Protocol V U Bool) (a : ℕ) :
    Paper2.SourceProtocolPrefixTree.CompleteAlicePrefix a
      (extendColumnProtocol V U hU P) ↔
    Paper2.SourceProtocolPrefixTree.CompleteAlicePrefix a P := by
  exact Paper2.SourceProtocolPrefixTree.complete_pullback_iff
    id (extendColumn U hU) a P

theorem extendColumnProtocol_rowCode (hU : U.Nonempty)
    (P : Protocol V U Bool) (a : ℕ) (x : A) :
    rowCode V (extendColumnProtocol V U hU P) a x = rowCode V P a x := by
  classical
  unfold rowCode
  split_ifs with hx
  · simp only [extendColumnProtocol,
      Paper2.PrefixPullback.prefixCodeRaw_pullback, id_eq]
  · rfl

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.extendColumnProtocol_eval
#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.extendColumnProtocol_rowCode
