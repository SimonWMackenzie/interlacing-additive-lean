import CurrentAdditive.GeneratedNearFullExact
import Paper2.SourceProtocolPrefixResidual

/-!
The graph partition is indexed by template bins, while the protocol tree is
indexed by transcript labels.  A dominant-bin bijection reindexes an actual
common-prefix branch without changing its row fibre or communication cost.
-/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2.SourceProtocolPrefix
open Workspace.Types.Protocol

variable {A B : Type*}

noncomputable def dominantBinCode (V : Set A) (P : Protocol V B Bool)
    (a : ℕ) (dom : Fin (2^a) ≃ Fin (2^a)) (x : A) : Fin (2^a) :=
  dom (rowCode V P a x)

theorem dominant_bin_fibre (V : Set A) (P : Protocol V B Bool)
    (a : ℕ) (dom : Fin (2^a) ≃ Fin (2^a)) (i : Fin (2^a)) :
    {x | x ∈ V ∧ dominantBinCode V P a dom x = i} =
      branchRows V P a (dom.symm i) := by
  ext x
  simp only [dominantBinCode, branchRows, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hx, he⟩
    exact ⟨hx, by simpa using congrArg dom.symm he⟩
  · rintro ⟨hx, he⟩
    exact ⟨hx, by simp [he]⟩

noncomputable def dominantBinInput (V : Set A) (P : Protocol V B Bool)
    (a : ℕ) (dom : Fin (2^a) ≃ Fin (2^a)) (i : Fin (2^a)) :
    {x | x ∈ V ∧ dominantBinCode V P a dom x = i} →
      branchRows V P a (dom.symm i) := by
  have h := dominant_bin_fibre V P a dom i
  exact fun x => ⟨x.val, h ▸ x.property⟩

noncomputable def dominantBinProtocol (V : Set A) (P : Protocol V B Bool)
    (a : ℕ) (dom : Fin (2^a) ≃ Fin (2^a)) (i : Fin (2^a)) :
    Protocol {x | x ∈ V ∧ dominantBinCode V P a dom x = i} B Bool :=
  NPCC.Protocol.pullback (dominantBinInput V P a dom i) id
    (branchProtocol V P a (dom.symm i))

theorem dominantBinProtocol_cost (V : Set A) (P : Protocol V B Bool)
    (a H : ℕ) (dom : Fin (2^a) ≃ Fin (2^a)) (i : Fin (2^a))
    (hp : Paper2.SourceProtocolPrefixTree.CompleteAlicePrefix a P)
    (hcost : P.cost ≤ H+a) :
    (dominantBinProtocol V P a dom i).cost ≤ H := by
  rw [dominantBinProtocol, NPCC.Protocol.pullback_cost]
  exact branchProtocol_cost V P a H (dom.symm i) hp hcost

theorem dominantBinProtocol_eval (V : Set A) (P : Protocol V B Bool)
    (a : ℕ) (dom : Fin (2^a) ≃ Fin (2^a)) (i : Fin (2^a))
    (hp : Paper2.SourceProtocolPrefixTree.CompleteAlicePrefix a P)
    (x : {x | x ∈ V ∧ dominantBinCode V P a dom x = i}) (y : B) :
    (dominantBinProtocol V P a dom i).eval x y =
      P.eval ⟨x.val, x.property.1⟩ y := by
  rw [dominantBinProtocol, NPCC.Protocol.pullback_eval]
  exact branchProtocol_eval V P a (dom.symm i) hp
    (dominantBinInput V P a dom i x) y

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.dominantBinProtocol_cost
#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.dominantBinProtocol_eval
