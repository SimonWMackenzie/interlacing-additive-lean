import Paper2.SourceSupportFrontierOverload
import Paper2.ProjectedSupportRouting

/-!
# Generated projected-support frontier

Frozen v12, Section 5, `res:two-stream`. The tree below follows actual Bob
queries of the transposed protocol. Its supports are original row labels;
the routing decision may inspect their selector images, but the retained
support is always the raw query fibre. Physical paths distinguish branches
even when projected selector images overlap.
-/

namespace Paper2.ProjectedSupportFrontier

open Workspace.Types.Protocol
open Paper2.SourceSupportFrontier
open Paper2.ProjectedSupportRouting
open scoped BigOperators

variable {A C I W : Type*} [Fintype W]

/-- The existing state stores the protocol, reaching columns, active bins,
attachments, and raw original-row supports. -/
abbrev State (A C I W : Type*) := SourceSupportFrontier.State A C I W

/-- A child stores the literal protocol subtree and literal query fibres.
`split` and `choose` will be instantiated from projected image mass. -/
noncomputable def child (s : State A C I W) (input : I → W → C)
    (query : C → Bool) (P : Protocol A C Bool)
    (split : Finset I) (choose : I → Bool) (b : Bool) : State A C I W := by
  classical
  exact {
  protocol := P
  columns := {c | c ∈ s.columns ∧ query c = b}
  coordinates := ProjectedSupportRouting.childCoordinates s.coordinates split choose b
  attachments := ProjectedSupportRouting.childAttachments s.attachments split choose b
  support := fun i => SourceSupportStep.fibre (s.support i)
    (fun w => query (input i w)) b
  }

/-- Only Bob nodes are traversed; the next transition retains original row
labels and records the number of attachments which split. -/
noncomputable def run (input : I → W → C)
    (select : ∀ (s : State A C I W) (query : C → Bool), Finset I × (I → Bool)) :
    ℕ → State A C I W → SourceSupportFrontier.Tree (State A C I W)
  | 0, s => .stop s
  | fuel + 1, s =>
    match s.protocol with
    | .bNode query left right =>
      let decision := select s query
      .fork decision.1.card
        (run input select fuel (child s input query left decision.1 decision.2 false))
        (run input select fuel (child s input query right decision.1 decision.2 true))
    | _ => .stop s

/-- Every generated stop carries its exact Bob-only path in the original
protocol, hence inherits evaluation and additive cost accounting. -/
theorem run_bobPath (input : I → W → C)
    (select : ∀ (s : State A C I W) (query : C → Bool), Finset I × (I → Bool))
    (fuel : ℕ) (s : State A C I W) :
    ∀ v : (run input select fuel s).Leaves,
      BobPath s.protocol s.columns ((run input select fuel s).route v)
        ((run input select fuel s).state v).protocol
        ((run input select fuel s).state v).columns := by
  induction fuel generalizing s with
  | zero => intro v; exact BobPath.here _ _
  | succ fuel ih =>
    rcases s with ⟨P, U, Q, Z, S⟩
    cases P with
    | leaf value => intro v; exact BobPath.here _ _
    | aNode query left right => intro v; exact BobPath.here _ _
    | bNode query left right =>
      intro v
      cases v with
      | inl v => exact BobPath.left (ih _ v)
      | inr v => exact BobPath.right (ih _ v)

/-- Exact evaluation of the original transposed protocol at every retained
reaching input, with the consumed row-prefix length charged to cost. -/
theorem run_eval_cost (input : I → W → C)
    (select : ∀ (s : State A C I W) (query : C → Bool), Finset I × (I → Bool))
    (fuel : ℕ) (s : State A C I W) :
    ∀ v : (run input select fuel s).Leaves,
      (∀ a c, c ∈ ((run input select fuel s).state v).columns →
        ((run input select fuel s).state v).protocol.eval a c =
          s.protocol.eval a c) ∧
      ((run input select fuel s).state v).protocol.cost +
        ((run input select fuel s).route v).length ≤ s.protocol.cost := by
  intro v
  have hp := run_bobPath input select fuel s v
  exact ⟨hp.eval_eq, hp.cost_add_length⟩

/-- A stopping route consumes at most the supplied fuel; a shorter route
ends before an Alice node or leaf. -/
theorem run_stopping (input : I → W → C)
    (select : ∀ (s : State A C I W) (query : C → Bool), Finset I × (I → Bool))
    (fuel : ℕ) (s : State A C I W) :
    ∀ v : (run input select fuel s).Leaves,
      ((run input select fuel s).route v).length ≤ fuel ∧
      (((run input select fuel s).route v).length = fuel ∨
        NonBob ((run input select fuel s).state v).protocol) := by
  induction fuel generalizing s with
  | zero => intro v; exact ⟨Nat.le_refl 0, Or.inl rfl⟩
  | succ fuel ih =>
    rcases s with ⟨P, U, Q, Z, S⟩
    cases P with
    | leaf value => intro v; exact ⟨Nat.zero_le _, Or.inr trivial⟩
    | aNode query left right => intro v; exact ⟨Nat.zero_le _, Or.inr trivial⟩
    | bNode query left right =>
      intro v
      cases v with
      | inl v =>
        obtain ⟨hle, heq | hstop⟩ := ih _ v
        · exact ⟨Nat.succ_le_succ hle, Or.inl (congrArg Nat.succ heq)⟩
        · exact ⟨Nat.succ_le_succ hle, Or.inr hstop⟩
      | inr v =>
        obtain ⟨hle, heq | hstop⟩ := ih _ v
        · exact ⟨Nat.succ_le_succ hle, Or.inl (congrArg Nat.succ heq)⟩
        · exact ⟨Nat.succ_le_succ hle, Or.inr hstop⟩

/-- A predicate stable under the two literal transitions holds at every
generated stopping state, indexed by the length of its physical path. -/
theorem run_invariant (input : I → W → C)
    (select : ∀ (s : State A C I W) (query : C → Bool), Finset I × (I → Bool))
    (Good : ℕ → State A C I W → Prop)
    (hstep : ∀ d s query left right, s.protocol = .bNode query left right →
      Good d s → ∀ b, Good (d + 1)
        (child s input query (if b then right else left)
          (select s query).1 (select s query).2 b))
    (d fuel : ℕ) (s : State A C I W) (hs : Good d s) :
    ∀ v : (run input select fuel s).Leaves,
      Good (d + ((run input select fuel s).route v).length)
        ((run input select fuel s).state v) := by
  induction fuel generalizing d s with
  | zero => intro v; simpa [run, Tree.route, Tree.state] using hs
  | succ fuel ih =>
    rcases s with ⟨P, U, Q, Z, S⟩
    cases P with
    | leaf value => intro v; simpa [run, Tree.route, Tree.state] using hs
    | aNode query left right => intro v; simpa [run, Tree.route, Tree.state] using hs
    | bNode query left right =>
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

/-- Every active raw row reaches the node on its original input label. -/
theorem run_support_reaches (input : I → W → C)
    (select : ∀ (s : State A C I W) (query : C → Bool), Finset I × (I → Bool))
    (fuel : ℕ) (s : State A C I W)
    (hs : ∀ i ∈ s.coordinates, ∀ w ∈ s.support i, input i w ∈ s.columns) :
    ∀ v : (run input select fuel s).Leaves,
      ∀ i ∈ ((run input select fuel s).state v).coordinates,
        ∀ w ∈ ((run input select fuel s).state v).support i,
          input i w ∈ ((run input select fuel s).state v).columns := by
  classical
  apply run_invariant input select
    (fun _ t => ∀ i ∈ t.coordinates, ∀ w ∈ t.support i, input i w ∈ t.columns)
    _ 0 fuel s hs
  intro d t query left right _ ht b i hi w hw
  have hiQ : i ∈ t.coordinates :=
    ProjectedSupportRouting.childCoordinates_subset _ _ _ _ hi
  have hmem := (SourceSupportStep.mem_fibre (t.support i)
    (fun w => query (input i w)) b w).mp hw
  exact ⟨ht i hiQ w hmem.1, hmem.2⟩

/-- Active bins, attachments, and raw supports retain their original labels. -/
theorem run_sets_subset (input : I → W → C)
    (select : ∀ (s : State A C I W) (query : C → Bool), Finset I × (I → Bool))
    (fuel : ℕ) (s : State A C I W) :
    ∀ v : (run input select fuel s).Leaves,
      ((run input select fuel s).state v).coordinates ⊆ s.coordinates ∧
      ((run input select fuel s).state v).attachments ⊆ s.attachments ∧
      ∀ i, ((run input select fuel s).state v).support i ⊆ s.support i := by
  classical
  apply run_invariant input select
    (fun _ t => t.coordinates ⊆ s.coordinates ∧ t.attachments ⊆ s.attachments ∧
      ∀ i, t.support i ⊆ s.support i) _ 0 fuel s
    ⟨Finset.Subset.refl _, Finset.Subset.refl _, fun _ => Finset.Subset.refl _⟩
  intro d t query left right _ ht b
  refine ⟨?_, ?_, ?_⟩
  · exact (ProjectedSupportRouting.childCoordinates_subset _ _ _ _).trans ht.1
  · exact (ProjectedSupportRouting.childAttachments_subset _ _ _ _).trans ht.2.1
  · intro i
    exact (SourceSupportStep.fibre_subset _ _ _).trans (ht.2.2 i)

/-- Attachments are always among the ordinary coordinates whenever the
chosen split set is contained in the current attachment set. -/
theorem run_attachments_subset (input : I → W → C)
    (select : ∀ (s : State A C I W) (query : C → Bool), Finset I × (I → Bool))
    (fuel : ℕ) (s : State A C I W)
    (hZ : s.attachments ⊆ s.coordinates) :
    ∀ v : (run input select fuel s).Leaves,
      ((run input select fuel s).state v).attachments ⊆
        ((run input select fuel s).state v).coordinates := by
  classical
  apply run_invariant input select
    (fun _ t => t.attachments ⊆ t.coordinates) _ 0 fuel s hZ
  intro d t query left right _ ht b
  exact ProjectedSupportRouting.childAttachments_subset_childCoordinates
    t.coordinates t.attachments (select t query).1 (select t query).2 b ht

/-- Generated count identities, with a local proof that every split index
is attached at its parent. No conservation statement is assumed globally. -/
theorem run_counts (input : I → W → C)
    (select : ∀ (s : State A C I W) (query : C → Bool), Finset I × (I → Bool))
    (hsplit : ∀ s query, (select s query).1 ⊆ s.attachments)
    (fuel : ℕ) (s : State A C I W)
    (hZ : s.attachments ⊆ s.coordinates) :
    (∑ v : (run input select fuel s).Leaves,
      ((run input select fuel s).state v).coordinates.card) =
        s.coordinates.card + (run input select fuel s).totalSplits ∧
    (∑ v : (run input select fuel s).Leaves,
      ((run input select fuel s).state v).attachments.card) +
        (run input select fuel s).totalSplits = s.attachments.card := by
  classical
  induction fuel generalizing s with
  | zero => simp [run, Tree.Leaves]
  | succ fuel ih =>
    rcases s with ⟨P, U, Q, Z, S⟩
    cases P with
    | leaf value => simp [run, Tree.Leaves]
    | aNode query left right => simp [run, Tree.Leaves]
    | bNode query left right =>
      let s0 : State A C I W := ⟨.bNode query left right, U, Q, Z, S⟩
      let split := (select s0 query).1
      let choose := (select s0 query).2
      let sl := child s0 input query left split choose false
      let sr := child s0 input query right split choose true
      let tl := run input select fuel sl
      let tr := run input select fuel sr
      have hs : split ⊆ Z := hsplit s0 query
      have hsQ : split ⊆ Q := hs.trans hZ
      have hl := ih sl (ProjectedSupportRouting.childAttachments_subset_childCoordinates
        Q Z split choose false hZ)
      have hr := ih sr (ProjectedSupportRouting.childAttachments_subset_childCoordinates
        Q Z split choose true hZ)
      have hQ := ProjectedSupportRouting.childCoordinates_card Q split choose hsQ
      have hA := ProjectedSupportRouting.childAttachments_card Z split choose hs
      change (∑ v : (Tree.fork split.card tl tr).Leaves,
          ((Tree.fork split.card tl tr).state v).coordinates.card) =
          Q.card + (Tree.fork split.card tl tr).totalSplits ∧
        (∑ v : (Tree.fork split.card tl tr).Leaves,
          ((Tree.fork split.card tl tr).state v).attachments.card) +
          (Tree.fork split.card tl tr).totalSplits = Z.card
      rw [Tree.sum_state_fork split.card tl tr (fun t : State A C I W => t.coordinates.card),
        Tree.sum_state_fork split.card tl tr (fun t : State A C I W => t.attachments.card)]
      simp only [Tree.totalSplits]
      dsimp only [tl, tr, sl, sr, child, s0] at hl hr ⊢
      omega

/-- The active positions are the nonempty-bin leaves of this literal run. -/
abbrev Active (T : SourceSupportFrontier.Tree (State A C I W)) :=
  SourceSupportFrontier.Active T

/-- Prefix-freeness and the generated count identities force an overloaded
physical node. Empty-bin leaves contribute zero and are removed by `Active`. -/
theorem run_active_overload (input : I → W → C)
    (select : ∀ (s : State A C I W) (query : C → Bool), Finset I × (I → Bool))
    (hsplit : ∀ s query, (select s query).1 ⊆ s.attachments)
    (fuel : ℕ) (s : State A C I W)
    (hZ : s.attachments ⊆ s.coordinates) (q b : ℕ)
    (hcount : s.coordinates.card + b = q)
    (hexcess : 3 * b < s.attachments.card) :
    ∃ v : Active (run input select fuel s),
      3 * ((q : ℝ) / 2 ^ ((run input select fuel s).route v.val).length) / 4 ≤
        (((run input select fuel s).state v.val).coordinates.card : ℝ) ∧
      (q : ℝ) / 2 ^ ((run input select fuel s).route v.val).length <
        (((run input select fuel s).state v.val).coordinates.card : ℝ) +
          (((run input select fuel s).state v.val).attachments.card : ℝ) := by
  classical
  let T := run input select fuel s
  have hz : ∀ v : T.Leaves, (T.state v).attachments ⊆ (T.state v).coordinates :=
    run_attachments_subset input select fuel s hZ
  have hc := run_counts input select hsplit fuel s hZ
  have hQnat : (∑ v : Active T, (T.state v.val).coordinates.card) =
      s.coordinates.card + T.totalSplits := by
    rw [SourceSupportFrontier.sum_active_coordinates T]
    exact hc.1
  have hZnat : (∑ v : Active T, (T.state v.val).attachments.card) +
      T.totalSplits = s.attachments.card := by
    rw [SourceSupportFrontier.sum_active_attachments T hz]
    exact hc.2
  have hQreal : (∑ v : Active T, ((T.state v.val).coordinates.card : ℝ)) =
      (q : ℝ) - b + T.totalSplits := by
    have hc' : (∑ v : Active T, ((T.state v.val).coordinates.card : ℝ)) =
        (s.coordinates.card : ℝ) + T.totalSplits := by exact_mod_cast hQnat
    have hi : (s.coordinates.card : ℝ) + b = q := by exact_mod_cast hcount
    linarith
  have hZreal : (∑ v : Active T, ((T.state v.val).attachments.card : ℝ)) =
      (s.attachments.card : ℝ) - T.totalSplits := by
    have hc' : (∑ v : Active T, ((T.state v.val).attachments.card : ℝ)) +
        (T.totalSplits : ℝ) = s.attachments.card := by exact_mod_cast hZnat
    linarith
  exact Frontier.frontier_overload (fun v : Active T => T.route v.val)
    (SourceSupportFrontier.active_prefixFree T)
    (fun v => ((T.state v.val).coordinates.card : ℝ))
    (fun v => ((T.state v.val).attachments.card : ℝ))
    (q : ℝ) (b : ℝ) (T.totalSplits : ℝ) (s.attachments.card : ℝ)
    (Nat.cast_nonneg q) (fun _ => Nat.cast_nonneg _)
    (fun v => by
      change ((T.state v.val).attachments.card : ℝ) ≤
        ((T.state v.val).coordinates.card : ℝ)
      exact_mod_cast Finset.card_le_card (hz v.val))
    hQreal hZreal (Nat.cast_nonneg _) (by exact_mod_cast hexcess)

end Paper2.ProjectedSupportFrontier
