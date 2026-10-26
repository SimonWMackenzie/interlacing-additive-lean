import Paper2.ReferencePrefix
import Paper2.ReferenceCertificateTree

/-!
# Physical-path bridge for the reference certificate tree

The certificate runner adds finite supports and weights to the same actual
Alice-only protocol prefix. Its leaves are position-indexed; this module
identifies them with the protocol-only prefix and transfers physical route,
subtree, and unique row-destination facts. No certificate capacity or owner
count is assumed.
-/

namespace Paper2.ReferenceCertificateProtocol

open Workspace.Types.Protocol Paper2.SourceSupportFrontier

variable {A C I W : Type*} [Fintype W]

/-- Certificate bookkeeping does not change the shape or leaf positions of
the stopped protocol tree. -/
noncomputable def leavesEquiv (μ : FiniteLaw W) (input : I → W → A)
    (floor : ℕ → ℝ) : (d fuel : ℕ) →
      (s : ReferenceCertificateTree.State A C I W) →
    (ReferenceCertificateTree.run μ input floor d fuel s).Leaves ≃
      (ReferencePrefix.runPrefix fuel s.protocol).Leaves
  | _, 0, _ => Equiv.refl Unit
  | d, fuel + 1, s => by
      cases s with
      | mk P rows family =>
          cases P with
          | leaf z => exact Equiv.refl Unit
          | bNode query left right => exact Equiv.refl Unit
          | aNode query left right =>
              exact Equiv.sumCongr
                (leavesEquiv μ input floor (d + 1) fuel
                  (ReferenceCertificateTree.child μ input (floor (d + 1))
                    ⟨.aNode query left right, rows, family⟩ query left false))
                (leavesEquiv μ input floor (d + 1) fuel
                  (ReferenceCertificateTree.child μ input (floor (d + 1))
                    ⟨.aNode query left right, rows, family⟩ query right true))

theorem leavesEquiv_route (μ : FiniteLaw W) (input : I → W → A)
    (floor : ℕ → ℝ) (d fuel : ℕ)
    (s : ReferenceCertificateTree.State A C I W)
    (v : (ReferenceCertificateTree.run μ input floor d fuel s).Leaves) :
    (ReferenceCertificateTree.run μ input floor d fuel s).route v =
      (ReferencePrefix.runPrefix fuel s.protocol).route
        (leavesEquiv μ input floor d fuel s v) := by
  induction fuel generalizing d s with
  | zero => rfl
  | succ fuel ih =>
      cases s with
      | mk P rows family =>
          cases P with
          | leaf z => rfl
          | bNode query left right => rfl
          | aNode query left right =>
              cases v with
              | inl v =>
                  change false ::
                    (ReferenceCertificateTree.run μ input floor (d + 1) fuel
                      (ReferenceCertificateTree.child μ input (floor (d + 1))
                        ⟨.aNode query left right, rows, family⟩ query left false)).route v =
                      false :: (ReferencePrefix.runPrefix fuel left).route
                        (leavesEquiv μ input floor (d + 1) fuel
                          (ReferenceCertificateTree.child μ input (floor (d + 1))
                            ⟨.aNode query left right, rows, family⟩ query left false) v)
                  exact congrArg (List.cons false) (ih _ _ v)
              | inr v =>
                  change true ::
                    (ReferenceCertificateTree.run μ input floor (d + 1) fuel
                      (ReferenceCertificateTree.child μ input (floor (d + 1))
                        ⟨.aNode query left right, rows, family⟩ query right true)).route v =
                      true :: (ReferencePrefix.runPrefix fuel right).route
                        (leavesEquiv μ input floor (d + 1) fuel
                          (ReferenceCertificateTree.child μ input (floor (d + 1))
                            ⟨.aNode query left right, rows, family⟩ query right true) v)
                  exact congrArg (List.cons true) (ih _ _ v)

theorem leavesEquiv_protocol (μ : FiniteLaw W) (input : I → W → A)
    (floor : ℕ → ℝ) (d fuel : ℕ)
    (s : ReferenceCertificateTree.State A C I W)
    (v : (ReferenceCertificateTree.run μ input floor d fuel s).Leaves) :
    ((ReferenceCertificateTree.run μ input floor d fuel s).state v).protocol =
      (ReferencePrefix.runPrefix fuel s.protocol).state
        (leavesEquiv μ input floor d fuel s v) := by
  induction fuel generalizing d s with
  | zero => rfl
  | succ fuel ih =>
      cases s with
      | mk P rows family =>
          cases P with
          | leaf z => rfl
          | bNode query left right => rfl
          | aNode query left right =>
              cases v with
              | inl v => exact ih _ _ v
              | inr v => exact ih _ _ v

/-- Reaching rows are exactly the original rows whose actual Alice answers
follow the leaf's physical route. No support or mass assumption is needed. -/
theorem rows_iff_follows (μ : FiniteLaw W) (input : I → W → A)
    (floor : ℕ → ℝ) (d fuel : ℕ)
    (s : ReferenceCertificateTree.State A C I W)
    (v : (ReferenceCertificateTree.run μ input floor d fuel s).Leaves) (a : A) :
    a ∈ ((ReferenceCertificateTree.run μ input floor d fuel s).state v).rows ↔
      a ∈ s.rows ∧ ReferencePrefix.Follows s.protocol a
        ((ReferenceCertificateTree.run μ input floor d fuel s).route v) := by
  induction fuel generalizing d s with
  | zero => simp [ReferenceCertificateTree.run, ReferencePrefix.Follows]
  | succ fuel ih =>
      cases s with
      | mk P rows family =>
          cases P with
          | leaf z => simp [ReferenceCertificateTree.run, ReferencePrefix.Follows]
          | bNode query left right =>
              simp [ReferenceCertificateTree.run, ReferencePrefix.Follows]
          | aNode query left right =>
              cases v with
              | inl v =>
                  have h := ih (d + 1)
                    (ReferenceCertificateTree.child μ input (floor (d + 1))
                      ⟨.aNode query left right, rows, family⟩ query left false) v
                  simpa only [ReferenceCertificateTree.run, Tree.state_fork_inl,
                    Tree.route_fork_inl, ReferenceCertificateTree.child,
                    ReferencePrefix.Follows, Set.mem_setOf_eq, and_assoc] using h
              | inr v =>
                  have h := ih (d + 1)
                    (ReferenceCertificateTree.child μ input (floor (d + 1))
                      ⟨.aNode query left right, rows, family⟩ query right true) v
                  simpa only [ReferenceCertificateTree.run, Tree.state_fork_inr,
                    Tree.route_fork_inr, ReferenceCertificateTree.child,
                    ReferencePrefix.Follows, Set.mem_setOf_eq, and_assoc] using h

/-- The unique terminal position selected by an original row, translated
from the protocol-only prefix through the physical-leaf equivalence. -/
noncomputable def destination (μ : FiniteLaw W) (input : I → W → A)
    (floor : ℕ → ℝ) (d fuel : ℕ)
    (s : ReferenceCertificateTree.State A C I W) (a : A) :
    (ReferenceCertificateTree.run μ input floor d fuel s).Leaves :=
  (leavesEquiv μ input floor d fuel s).symm
    (ReferencePrefix.destination fuel s.protocol a)

theorem rows_iff_destination (μ : FiniteLaw W) (input : I → W → A)
    (floor : ℕ → ℝ) (d fuel : ℕ)
    (s : ReferenceCertificateTree.State A C I W) (a : A)
    (ha : a ∈ s.rows)
    (v : (ReferenceCertificateTree.run μ input floor d fuel s).Leaves) :
    a ∈ ((ReferenceCertificateTree.run μ input floor d fuel s).state v).rows ↔
      v = destination μ input floor d fuel s a := by
  let E := leavesEquiv μ input floor d fuel s
  rw [rows_iff_follows, and_iff_right ha, leavesEquiv_route,
    ReferencePrefix.follows_iff_destination]
  constructor
  · intro h
    have hh := congrArg E.symm h
    simpa only [E.symm_apply_apply, destination, E] using hh
  · intro h
    subst v
    exact E.apply_symm_apply _

/-- Exact capacity equality for the **annotated actual tree**, transported
from its physically identical protocol prefix. -/
theorem run_capacity_eq (μ : FiniteLaw W) (input : I → W → A)
    (floor : ℕ → ℝ) (d fuel : ℕ)
    (s : ReferenceCertificateTree.State A C I W)
    (h : ReferencePrefix.NoEarlyLeaf fuel s.protocol) :
    (∑ v : (ReferenceCertificateTree.run μ input floor d fuel s).Leaves,
      2 ^ (fuel - ((ReferenceCertificateTree.run μ input floor d fuel s).route v).length)) =
        2 ^ fuel := by
  let E := leavesEquiv μ input floor d fuel s
  have heq := Fintype.sum_equiv E
    (fun v : (ReferenceCertificateTree.run μ input floor d fuel s).Leaves =>
      2 ^ (fuel - ((ReferenceCertificateTree.run μ input floor d fuel s).route v).length))
    (fun v : (ReferencePrefix.runPrefix fuel s.protocol).Leaves =>
      2 ^ (fuel - ((ReferencePrefix.runPrefix fuel s.protocol).route v).length))
    (fun v => by
      change 2 ^ (fuel - ((ReferenceCertificateTree.run μ input floor d fuel s).route v).length) =
        2 ^ (fuel - ((ReferencePrefix.runPrefix fuel s.protocol).route
          (leavesEquiv μ input floor d fuel s v)).length)
      exact congrArg (fun route : List Bool => 2 ^ (fuel - route.length))
        (leavesEquiv_route μ input floor d fuel s v))
  exact heq.trans (ReferencePrefix.runPrefix_capacity_eq fuel s.protocol h)

theorem run_cost_add_length (μ : FiniteLaw W) (input : I → W → A)
    (floor : ℕ → ℝ) (d fuel : ℕ)
    (s : ReferenceCertificateTree.State A C I W)
    (v : (ReferenceCertificateTree.run μ input floor d fuel s).Leaves) :
    ((ReferenceCertificateTree.run μ input floor d fuel s).state v).protocol.cost +
      ((ReferenceCertificateTree.run μ input floor d fuel s).route v).length ≤
        s.protocol.cost := by
  rw [leavesEquiv_protocol, leavesEquiv_route]
  exact ReferencePrefix.runPrefix_cost_add_length fuel s.protocol _

theorem run_stop_or_depth (μ : FiniteLaw W) (input : I → W → A)
    (floor : ℕ → ℝ) (d fuel : ℕ)
    (s : ReferenceCertificateTree.State A C I W)
    (h : ReferencePrefix.NoEarlyLeaf fuel s.protocol)
    (v : (ReferenceCertificateTree.run μ input floor d fuel s).Leaves) :
    ((ReferenceCertificateTree.run μ input floor d fuel s).route v).length = fuel ∨
      ∃ q left right,
        ((ReferenceCertificateTree.run μ input floor d fuel s).state v).protocol =
          Protocol.bNode q left right := by
  rw [leavesEquiv_protocol, leavesEquiv_route]
  exact ReferencePrefix.runPrefix_stop_or_depth fuel s.protocol h _

end Paper2.ReferenceCertificateProtocol

#print axioms Paper2.ReferenceCertificateProtocol.leavesEquiv_route
#print axioms Paper2.ReferenceCertificateProtocol.leavesEquiv_protocol
#print axioms Paper2.ReferenceCertificateProtocol.rows_iff_destination
#print axioms Paper2.ReferenceCertificateProtocol.run_capacity_eq
#print axioms Paper2.ReferenceCertificateProtocol.run_cost_add_length
#print axioms Paper2.ReferenceCertificateProtocol.run_stop_or_depth
