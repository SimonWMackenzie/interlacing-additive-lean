import Paper2.ReferenceCertificateProtocol

/-!
# Correctness and budgets at original-row stopping positions

Frozen Paper 2 v12, `res:destinations`, lines 250--310. The whole column
event is unchanged throughout this Alice-only prefix. The remaining protocol
is proved correct on the original rows reaching each physical position;
this is not an independent correctness or restriction-cost certificate.
-/

namespace Paper2.ReferenceRunCorrectness

open ReferenceCertificateTree SourceSupportFrontier Workspace.Types.Protocol

variable {A C I W : Type*} [Fintype W]

theorem eval_of_mem_rows (μ : FiniteLaw W) (input : I → W → A)
    (floor : ℕ → ℝ) (d fuel : ℕ) (s : State A C I W)
    (v : (run μ input floor d fuel s).Leaves) (a : A) (c : C)
    (ha : a ∈ ((run μ input floor d fuel s).state v).rows) :
    ((run μ input floor d fuel s).state v).protocol.eval a c = s.protocol.eval a c := by
  have hf := ((ReferenceCertificateProtocol.rows_iff_follows μ input floor d fuel s v a).mp ha).2
  rw [ReferenceCertificateProtocol.leavesEquiv_route] at hf
  rw [ReferenceCertificateProtocol.leavesEquiv_protocol]
  exact ReferencePrefix.runPrefix_eval_of_follows fuel s.protocol _ a c hf

theorem rows_subset (μ : FiniteLaw W) (input : I → W → A)
    (floor : ℕ → ℝ) (d fuel : ℕ) (s : State A C I W)
    (v : (run μ input floor d fuel s).Leaves) :
    ((run μ input floor d fuel s).state v).rows ⊆ s.rows := by
  intro a ha
  exact ((ReferenceCertificateProtocol.rows_iff_follows μ input floor d fuel s v a).mp ha).1

theorem computes_on_original_rectangle (μ : FiniteLaw W) (input : I → W → A)
    (floor : ℕ → ℝ) (d fuel : ℕ) (s : State A C I W)
    (M : A → C → Bool) (O : Set C)
    (hP : ∀ a ∈ s.rows, ∀ c ∈ O, s.protocol.eval a c = M a c)
    (v : (run μ input floor d fuel s).Leaves) :
    ∀ a ∈ ((run μ input floor d fuel s).state v).rows, ∀ c ∈ O,
      ((run μ input floor d fuel s).state v).protocol.eval a c = M a c := by
  intro a ha c hc
  rw [eval_of_mem_rows μ input floor d fuel s v a c ha]
  exact hP a (rows_subset μ input floor d fuel s v ha) c hc

theorem depth_le (μ : FiniteLaw W) (input : I → W → A)
    (floor : ℕ → ℝ) (d fuel : ℕ) (s : State A C I W)
    (v : (run μ input floor d fuel s).Leaves) :
    ((run μ input floor d fuel s).route v).length ≤ fuel := by
  rw [ReferenceCertificateProtocol.leavesEquiv_route]
  exact ReferencePrefix.runPrefix_depth_le fuel s.protocol _

theorem remaining_cost (μ : FiniteLaw W) (input : I → W → A)
    (floor : ℕ → ℝ) (r H : ℕ) (s : State A C I W)
    (hcost : s.protocol.cost ≤ H + r)
    (v : (run μ input floor 0 r s).Leaves) :
    ((run μ input floor 0 r s).state v).protocol.cost ≤
      H + (r - ((run μ input floor 0 r s).route v).length) := by
  have hc := ReferenceCertificateProtocol.run_cost_add_length μ input floor 0 r s v
  have hd := depth_le μ input floor 0 r s v
  omega

theorem before_depth_is_bob (μ : FiniteLaw W) (input : I → W → A)
    (floor : ℕ → ℝ) (r : ℕ) (s : State A C I W)
    (hprefix : ReferencePrefix.NoEarlyLeaf r s.protocol)
    (v : (run μ input floor 0 r s).Leaves)
    (hnotfinal : ((run μ input floor 0 r s).route v).length ≠ r) :
    1 ≤ r - ((run μ input floor 0 r s).route v).length ∧
      ∃ q left right, ((run μ input floor 0 r s).state v).protocol =
        Protocol.bNode q left right := by
  have hd := depth_le μ input floor 0 r s v
  have hs := ReferenceCertificateProtocol.run_stop_or_depth μ input floor 0 r s hprefix v
  exact ⟨by omega, hs.resolve_left hnotfinal⟩

end Paper2.ReferenceRunCorrectness

#print axioms Paper2.ReferenceRunCorrectness.computes_on_original_rectangle
#print axioms Paper2.ReferenceRunCorrectness.remaining_cost
#print axioms Paper2.ReferenceRunCorrectness.before_depth_is_bob
