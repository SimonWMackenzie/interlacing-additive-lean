import Paper2.SourceProtocolPrefix

/-!
# Actual source branch protocols

Frozen v12 Section 4, `src:near-full`: after the common depth-a prefix,
each selected branch is a protocol on all unchanged columns and the actual
retained rows carrying that transcript. Its cost is at most the original
budget minus a. This module constructs that protocol explicitly.
-/

namespace Paper2.SourceProtocolPrefix

open Workspace.Types.Protocol SourceProtocolPrefixTree

variable {A B : Type*}

/-- The common row label is the actual communicated prefix on every
retained column, not merely a code on the fixed-tail submatrix. -/
theorem rowCode_eq_actualPrefix (W : Set A) (P : Protocol W B Bool)
    (a : ℕ) (hp : CompleteAlicePrefix a P) (x : W) (y : B) :
    rowCode W P a x.val = NPCC.Protocol.actualPrefixCodeRaw a P x y := by
  classical
  simp only [rowCode, dif_pos x.property]
  symm
  exact NPCC.Protocol.actualPrefixCodeRaw_eq_prefixCodeRaw_of_firstKRowBitsOn
    {x} {y} a P (firstK_of_complete {x} {y} a P hp)
    (Finset.mem_singleton_self x) (Finset.mem_singleton_self y)

def branchRows (W : Set A) (P : Protocol W B Bool) (a : ℕ) (j : Fin (2 ^ a)) : Set A :=
  {x | x ∈ W ∧ rowCode W P a x = j}

def branchInput (W : Set A) (P : Protocol W B Bool) (a : ℕ) (j : Fin (2 ^ a)) :
    branchRows W P a j → W := fun x => ⟨x.val, x.property.1⟩

/-- Keep the selected original subtree, and restrict only its row carrier.
Every original column remains available on this branch. -/
noncomputable def branchProtocol (W : Set A) (P : Protocol W B Bool)
    (a : ℕ) (j : Fin (2 ^ a)) : Protocol (branchRows W P a j) B Bool :=
  NPCC.Protocol.pullback (branchInput W P a j) id (NPCC.Protocol.rowSubtreeAtRaw a P j)

theorem branchProtocol_eval (W : Set A) (P : Protocol W B Bool)
    (a : ℕ) (j : Fin (2 ^ a)) (hp : CompleteAlicePrefix a P)
    (x : branchRows W P a j) (y : B) :
    (branchProtocol W P a j).eval x y = P.eval (branchInput W P a j x) y := by
  classical
  rw [branchProtocol, NPCC.Protocol.pullback_eval]
  apply subtree_eval_of_prefix a P hp j _ y
  have hx := x.property.2
  simpa only [rowCode, dif_pos x.property.1, branchInput] using hx

/-- The branch computes the literal original matrix on its actual row
fibre, not a separately chosen matrix of comparable mass. -/
theorem branchProtocol_computes (F : A → B → Bool)
    (W : Set A) (P : Protocol W B Bool) (a : ℕ) (j : Fin (2 ^ a))
    (hp : CompleteAlicePrefix a P) (hP : P.Computes (fun x y => F x.val y)) :
    (branchProtocol W P a j).Computes (fun x y => F x.val y) := by
  intro x y
  exact (branchProtocol_eval W P a j hp x y).trans (hP _ _)

theorem branchProtocol_cost (W : Set A) (P : Protocol W B Bool)
    (a H : ℕ) (j : Fin (2 ^ a)) (hp : CompleteAlicePrefix a P)
    (hcost : P.cost ≤ H + a) : (branchProtocol W P a j).cost ≤ H := by
  rw [branchProtocol, NPCC.Protocol.pullback_cost]
  have := subtree_cost_add_le a P hp j
  omega

end Paper2.SourceProtocolPrefix
