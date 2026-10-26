import Paper2.SourceProtocolPrefixTree
import Workspace.UpperBound

/-! Actual prefix parts and residual protocols. Inputs outside the original
retained columns are used only as arbitrary defaults for protocol pullback;
all correctness assertions remain on the original retained columns. -/

namespace CurrentAdditive.V38PrefixResidual

open Paper2 Workspace.Types.Protocol

variable {A C : Type*} {W : Set A} {U : Set C} {t : ℕ}

noncomputable def rawCode (P : Protocol W U Bool) (a : A) : Fin (2^t) := by
  classical
  exact if h : a ∈ W then NPCC.Protocol.prefixCodeRaw t P ⟨a,h⟩
    else ⟨0,Nat.two_pow_pos t⟩

theorem rawCode_of_mem (P : Protocol W U Bool) (a : A) (ha : a ∈ W) :
    rawCode (t := t) P a = NPCC.Protocol.prefixCodeRaw t P ⟨a,ha⟩ := by
  classical
  simp [rawCode,ha]

def branchRows (P : Protocol W U Bool) (w : Fin (2^t)) : Set A :=
  {a | a ∈ W ∧ rawCode P a = w}

noncomputable def branchProtocol (P : Protocol W U Bool) (hU : U.Nonempty)
    (w : Fin (2^t)) : Protocol (branchRows P w) C Bool := by
  classical
  exact Workspace.UpperBound.Protocol.comap
    (fun a => (⟨a.val,a.property.1⟩ : W))
    (fun c => if h : c ∈ U then (⟨c,h⟩ : U) else ⟨hU.choose,hU.choose_spec⟩)
    (NPCC.Protocol.rowSubtreeAtRaw t P w)

theorem branch_cost (P : Protocol W U Bool) (hU : U.Nonempty)
    (hpref : SourceProtocolPrefixTree.CompleteAlicePrefix t P) (w : Fin (2^t)) :
    (branchProtocol P hU w).cost + t ≤ P.cost := by
  classical
  simpa only [branchProtocol,Workspace.UpperBound.Protocol.comap_cost] using
    SourceProtocolPrefixTree.subtree_cost_add_le t P hpref w

theorem branch_correct (F : A → C → Bool) (P : Protocol W U Bool)
    (hU : U.Nonempty) (hpref : SourceProtocolPrefixTree.CompleteAlicePrefix t P)
    (hP : P.Computes (fun a c => F a.val c.val)) (w : Fin (2^t)) :
    ∀ a c, c ∈ U → (branchProtocol P hU w).eval a c = F a.val c := by
  classical
  intro a c hc
  have hcode : NPCC.Protocol.prefixCodeRaw t P ⟨a.val,a.property.1⟩ = w := by
    rw [← rawCode_of_mem P a.val a.property.1]
    exact a.property.2
  simp only [branchProtocol,Workspace.UpperBound.Protocol.comap_eval,dif_pos hc]
  rw [SourceProtocolPrefixTree.subtree_eval_of_prefix t P hpref w _ _ hcode]
  exact hP _ _

end CurrentAdditive.V38PrefixResidual

#print axioms CurrentAdditive.V38PrefixResidual.rawCode
#print axioms CurrentAdditive.V38PrefixResidual.rawCode_of_mem
#print axioms CurrentAdditive.V38PrefixResidual.branchRows
#print axioms CurrentAdditive.V38PrefixResidual.branchProtocol
#print axioms CurrentAdditive.V38PrefixResidual.branch_cost
#print axioms CurrentAdditive.V38PrefixResidual.branch_correct
