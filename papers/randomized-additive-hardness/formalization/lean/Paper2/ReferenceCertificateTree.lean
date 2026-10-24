import Paper2.ReferenceCertificates
import Paper2.SourceSupportFrontierTree
import Workspace.Types.Protocol

/-!
# Reference certificates on an actual Alice-only protocol prefix

Frozen v12 Section 5, `res:destinations`, lines 250--310. Every syntactic
branch is retained, including branches without certificates. At each Alice
query the original reference labels are filtered by the actual transmitted
bit. Unsplit labels and total weight are derived by this recursion; neither
the owner count nor a lower-bound conclusion is a field of the state.

Early leaves are retained as stops by this generic runner. The separate
prefix-padding theorem and source-specific leaf exclusion are required
before classifying all final destinations as in the paper.
-/

namespace Paper2.ReferenceCertificateTree

open Workspace.Types.Protocol SourceSupportFrontier ReferenceCertificates
open scoped BigOperators

variable {A C I W : Type*} [Fintype W]

structure State (A C I W : Type*) where
  protocol : Protocol A C Bool
  rows : Set A
  family : ReferenceCertificates.Family I W

noncomputable def child (μ : FiniteLaw W) (input : I → W → A)
    (t : ℝ) (s : State A C I W) (query : A → Bool)
    (P : Protocol A C Bool) (b : Bool) : State A C I W where
  protocol := P
  rows := {a | a ∈ s.rows ∧ query a = b}
  family := ReferenceCertificates.child μ s.family (fun i w => query (input i w)) t b

/-- The stopping rule depends on the actual protocol and depth, not the
presence or absence of a reference support. -/
noncomputable def run (μ : FiniteLaw W) (input : I → W → A)
    (floor : ℕ → ℝ) : ℕ → ℕ → State A C I W → SourceSupportFrontier.Tree (State A C I W)
  | _, 0, s => .stop s
  | d, fuel + 1, s =>
    match s.protocol with
    | .aNode query left right => .fork 0
        (run μ input floor (d + 1) fuel
          (child μ input (floor (d + 1)) s query left false))
        (run μ input floor (d + 1) fuel
          (child μ input (floor (d + 1)) s query right true))
    | _ => .stop s

theorem run_invariant (μ : FiniteLaw W) (input : I → W → A)
    (floor : ℕ → ℝ) (Good : ℕ → State A C I W → Prop)
    (hstep : ∀ d s query left right, s.protocol = .aNode query left right →
      Good d s → ∀ b, Good (d + 1)
        (child μ input (floor (d + 1)) s query (if b then right else left) b))
    (d fuel : ℕ) (s : State A C I W) (hs : Good d s) :
    ∀ v : (run μ input floor d fuel s).Leaves,
      Good (d + ((run μ input floor d fuel s).route v).length)
        ((run μ input floor d fuel s).state v) := by
  induction fuel generalizing d s with
  | zero => intro v; simpa [run, Tree.route, Tree.state] using hs
  | succ fuel ih =>
    rcases s with ⟨P, U, S⟩
    cases P with
    | leaf z => intro v; simpa [run, Tree.route, Tree.state] using hs
    | bNode query left right => intro v; simpa [run, Tree.route, Tree.state] using hs
    | aNode query left right =>
      intro v
      cases v with
      | inl v =>
        have h := ih (d + 1) _ (hstep d _ query left right rfl hs false) v
        simpa [run, Tree.route, Tree.state, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using h
      | inr v =>
        have h := ih (d + 1) _ (hstep d _ query left right rfl hs true) v
        simpa [run, Tree.route, Tree.state, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using h

theorem run_valid (μ : FiniteLaw W) (input : I → W → A)
    (floor : ℕ → ℝ) (d fuel : ℕ) (s : State A C I W)
    (hs : s.family.unsplit ⊆ s.family.active) :
    ∀ v : (run μ input floor d fuel s).Leaves,
      ((run μ input floor d fuel s).state v).family.unsplit ⊆
        ((run μ input floor d fuel s).state v).family.active := by
  apply run_invariant μ input floor
    (fun _ t => t.family.unsplit ⊆ t.family.active) _ d fuel s hs
  intro d t query left right _ ht b
  exact ReferenceCertificates.child_valid μ t.family _ _ b ht

theorem run_floor (μ : FiniteLaw W) (input : I → W → A)
    (floor : ℕ → ℝ) (hhalf : ∀ d, floor d = 2 * floor (d + 1))
    (d fuel : ℕ) (s : State A C I W)
    (hs : ∀ i ∈ s.family.active, floor d ≤ SourceSupportStep.mass μ (s.family.support i)) :
    ∀ v : (run μ input floor d fuel s).Leaves,
      ∀ i ∈ ((run μ input floor d fuel s).state v).family.active,
        floor (d + ((run μ input floor d fuel s).route v).length) ≤
          SourceSupportStep.mass μ (((run μ input floor d fuel s).state v).family.support i) := by
  apply run_invariant μ input floor
    (fun d t => ∀ i ∈ t.family.active,
      floor d ≤ SourceSupportStep.mass μ (t.family.support i)) _ d fuel s hs
  intro d t query left right _ ht b
  exact ReferenceCertificates.child_floor μ t.family _ _ b
    (by simpa only [← hhalf d] using ht)

theorem run_reaches (μ : FiniteLaw W) (input : I → W → A)
    (floor : ℕ → ℝ) (d fuel : ℕ) (s : State A C I W)
    (hs : ∀ i ∈ s.family.active, ∀ w ∈ s.family.support i, input i w ∈ s.rows) :
    ∀ v : (run μ input floor d fuel s).Leaves,
      ∀ i ∈ ((run μ input floor d fuel s).state v).family.active,
        ∀ w ∈ ((run μ input floor d fuel s).state v).family.support i,
          input i w ∈ ((run μ input floor d fuel s).state v).rows := by
  apply run_invariant μ input floor
    (fun _ t => ∀ i ∈ t.family.active, ∀ w ∈ t.family.support i, input i w ∈ t.rows)
    _ d fuel s hs
  intro d t query left right _ ht b
  exact ReferenceCertificates.child_reaches μ t.family input query t.rows _ b ht

theorem run_sets_subset (μ : FiniteLaw W) (input : I → W → A)
    (floor : ℕ → ℝ) (d fuel : ℕ) (s : State A C I W) :
    ∀ v : (run μ input floor d fuel s).Leaves,
      ((run μ input floor d fuel s).state v).family.active ⊆ s.family.active ∧
      ((run μ input floor d fuel s).state v).family.unsplit ⊆ s.family.unsplit ∧
      ∀ i, ((run μ input floor d fuel s).state v).family.support i ⊆ s.family.support i := by
  apply run_invariant μ input floor
    (fun _ t => t.family.active ⊆ s.family.active ∧
      t.family.unsplit ⊆ s.family.unsplit ∧ ∀ i, t.family.support i ⊆ s.family.support i)
    _ d fuel s ⟨Finset.Subset.refl _, Finset.Subset.refl _, fun _ => Finset.Subset.refl _⟩
  intro d t query left right _ ht b
  refine ⟨(child_active_subset μ t.family _ _ b).trans ht.1,
    (child_unsplit_subset μ t.family _ _ b).trans ht.2.1, ?_⟩
  intro i
  exact (SourceSupportStep.fibre_subset (t.family.support i) _ b).trans (ht.2.2 i)

/-- Conservation follows by adding the two actual child populations. -/
theorem run_units (μ : FiniteLaw W) (input : I → W → A)
    (floor : ℕ → ℝ) (d fuel : ℕ) (s : State A C I W)
    (hs : s.family.unsplit ⊆ s.family.active) :
    units s.family ≤ ∑ v : (run μ input floor d fuel s).Leaves,
      units (((run μ input floor d fuel s).state v).family) := by
  induction fuel generalizing d s with
  | zero => simp [run, Tree.Leaves]
  | succ fuel ih =>
    rcases s with ⟨P, U, S⟩
    cases P with
    | leaf z => simp [run, Tree.Leaves]
    | bNode query left right => simp [run, Tree.Leaves]
    | aNode query left right =>
      have hl := ih (d + 1)
        (child μ input (floor (d + 1)) ⟨.aNode query left right, U, S⟩ query left false)
        (ReferenceCertificates.child_valid μ S _ _ false hs)
      have hr := ih (d + 1)
        (child μ input (floor (d + 1)) ⟨.aNode query left right, U, S⟩ query right true)
        (ReferenceCertificates.child_valid μ S _ _ true hs)
      have hstep := units_nondecreasing μ S (fun i w => query (input i w)) (floor (d + 1)) hs
      let sl := child μ input (floor (d + 1))
        (State.mk (.aNode query left right) U S) query left false
      let sr := child μ input (floor (d + 1))
        (State.mk (.aNode query left right) U S) query right true
      let tl := run μ input floor (d + 1) fuel sl
      let tr := run μ input floor (d + 1) fuel sr
      change units S ≤ ∑ v : tl.Leaves ⊕ tr.Leaves,
        units ((SourceSupportFrontier.Tree.fork 0 tl tr).state v).family
      rw [Fintype.sum_sum_type]
      exact hstep.trans (Nat.add_le_add hl hr)

/-- A surviving unsplit origin occurs at at most one physical stopping
position, including when different positions store identical states. -/
theorem run_unsplit_disjoint (μ : FiniteLaw W) (input : I → W → A)
    (floor : ℕ → ℝ) (d fuel : ℕ) (s : State A C I W) :
    ∀ v z : (run μ input floor d fuel s).Leaves, v ≠ z →
      Disjoint (((run μ input floor d fuel s).state v).family.unsplit)
        (((run μ input floor d fuel s).state z).family.unsplit) := by
  induction fuel generalizing d s with
  | zero => intro v z h; exact (h (@Subsingleton.elim Unit _ v z)).elim
  | succ fuel ih =>
    rcases s with ⟨P, U, S⟩
    cases P with
    | leaf z => intro v z h; exact (h (@Subsingleton.elim Unit _ v z)).elim
    | bNode query left right => intro v z h; exact (h (@Subsingleton.elim Unit _ v z)).elim
    | aNode query left right =>
      intro v z h
      have hdis := unsplit_disjoint μ S (fun i w => query (input i w)) (floor (d + 1))
      cases v with
      | inl v =>
        cases z with
        | inl z => exact ih _ _ v z (fun e => h (congrArg Sum.inl e))
        | inr z =>
          exact hdis.mono (run_sets_subset μ input floor _ _ _ v).2.1
            (run_sets_subset μ input floor _ _ _ z).2.1
      | inr v =>
        cases z with
        | inl z =>
          exact hdis.symm.mono (run_sets_subset μ input floor _ _ _ v).2.1
            (run_sets_subset μ input floor _ _ _ z).2.1
        | inr z => exact ih _ _ v z (fun e => h (congrArg Sum.inr e))

end Paper2.ReferenceCertificateTree

#print axioms Paper2.ReferenceCertificateTree.run_floor
#print axioms Paper2.ReferenceCertificateTree.run_reaches
#print axioms Paper2.ReferenceCertificateTree.run_units
#print axioms Paper2.ReferenceCertificateTree.run_unsplit_disjoint
