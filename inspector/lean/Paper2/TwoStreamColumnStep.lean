import Paper2.TwoStreamScalarCost

/-!
# The actual ordinary-column child and its bit charge

Frozen v12, Section 5, `res:two-stream`. At the first column-player
message (Alice in the transposed protocol), split only the retained
ordinary family. Foreign inputs need not follow the denser ordinary
child. The paired-capacity argument is consequently a parent argument.
-/

namespace Paper2.TwoStreamColumnStep

open Workspace.Types.Protocol

variable {Ω A C : Type*} [Fintype Ω] [Fintype C]

def ordinaryChild (O : Set Ω) (col : Ω → A) (query : A → Bool) (b : Bool) : Set Ω :=
  {c | c ∈ O ∧ query (col c) = b}

theorem ordinary_partition (κ : FiniteLaw Ω) (O : Set Ω)
    (col : Ω → A) (query : A → Bool) :
    κ.prob (· ∈ ordinaryChild O col query false) +
      κ.prob (· ∈ ordinaryChild O col query true) = κ.prob (· ∈ O) := by
  classical
  unfold FiniteLaw.prob
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  cases hb : query (col c) <;> by_cases hc : c ∈ O <;> simp [ordinaryChild, hb, hc]

/-- The ordinary retained family supplies a genuine dense child even
if all foreign labels take the other branch. -/
theorem exists_dense_child (κ : FiniteLaw Ω) (O : Set Ω)
    (col : Ω → A) (query : A → Bool) (hO : (4 / 5 : ℝ) < κ.prob (· ∈ O)) :
    ∃ b, (2 / 5 : ℝ) < κ.prob (· ∈ ordinaryChild O col query b) ∧
      (9 / 25 : ℝ) ≤ κ.prob (· ∈ ordinaryChild O col query b) := by
  have hp := ordinary_partition κ O col query
  by_cases hf : (2 / 5 : ℝ) < κ.prob (· ∈ ordinaryChild O col query false)
  · exact ⟨false, hf, by linarith⟩
  · have ht : (2 / 5 : ℝ) < κ.prob (· ∈ ordinaryChild O col query true) := by
      push_neg at hf
      linarith
    exact ⟨true, ht, by linarith⟩

/-- The given child computes the same retained ordinary rectangle, and
the parent's actual column-player bit is charged exactly once. -/
theorem ordinary_restriction_add_one_le (M : C → Ω → Bool)
    (R : Set C) (O : Set Ω) (col : Ω → A) (query : A → Bool)
    (left right : Protocol A C Bool)
    (hP : ∀ r ∈ R, ∀ c ∈ O,
      (Protocol.aNode query left right).eval (col c) r = M r c)
    (b : Bool) :
    Compression.restrictionD M R (ordinaryChild O col query b) + 1 ≤
      (Protocol.aNode query left right).cost := by
  classical
  let child := if b then right else left
  let Q := Workspace.UpperBound.Protocol.comap
    (fun r : R => r.val) (fun c : ordinaryChild O col query b => col c.val)
    (Workspace.UpperBound.Protocol.transpose child)
  have hQ : Q.Computes (fun (r : R) (c : ordinaryChild O col query b) => M r.val c.val) := by
    intro r c
    rw [Workspace.UpperBound.Protocol.comap_eval,
      Workspace.UpperBound.Protocol.transpose_eval]
    have hc := c.property
    have he := hP r.val r.property c.val hc.1
    have hb : query (col c.val) = b := hc.2
    cases b <;> simpa [Protocol.eval, hb, child] using he
  have hupper : Compression.restrictionD M R (ordinaryChild O col query b) ≤ child.cost := by
    have h : Compression.restrictionD M R (ordinaryChild O col query b) ≤ Q.cost :=
      Nat.sInf_le ⟨Q, rfl, hQ⟩
    simpa only [Q, Workspace.UpperBound.Protocol.comap_cost,
      Workspace.UpperBound.Protocol.transpose_cost] using h
  have hchild : child.cost + 1 ≤ (Protocol.aNode query left right).cost := by
    dsimp only [child]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, Protocol.cost]
    · simpa only [Nat.add_comm] using Nat.add_le_add_right (Nat.le_max_left left.cost right.cost) 1
    · simpa only [Nat.add_comm] using Nat.add_le_add_right (Nat.le_max_right left.cost right.cost) 1
  exact (Nat.add_le_add_right hupper 1).trans hchild

end Paper2.TwoStreamColumnStep

#print axioms Paper2.TwoStreamColumnStep.exists_dense_child
#print axioms Paper2.TwoStreamColumnStep.ordinary_restriction_add_one_le
