import Paper2.ProjectedSupportFrontier
import Paper2.ProjectedSupportStep

/-!
# Depth-indexed projected row-prefix walk

The routing choice at depth `d` uses the *next* selector-image floor.
The supports are literal original-row query fibres. This scheduled walk
has no premise asserting a frontier, count identity, or lower bound.
-/

namespace Paper2.ProjectedSupportFrontier

open Workspace.Types.Protocol SourceSupportFrontier
open scoped BigOperators

variable {A C I W S : Type*} [Fintype S]

/-- The concrete projection-aware decision at the indicated next floor. -/
noncomputable def projectedDecision (μ : FiniteLaw S) (σ : I → W → S)
    (input : I → W → C) (t : ℝ) (s : State A C I W)
    (query : C → Bool) : Finset I × (I → Bool) :=
  (ProjectedSupportStep.splits μ σ s.attachments s.support
      (fun i w => query (input i w)) t,
    fun i => ProjectedSupportStep.heavyBit μ (σ i) (s.support i)
      (fun w => query (input i w)))

theorem projectedDecision_subset (μ : FiniteLaw S) (σ : I → W → S)
    (input : I → W → C) (t : ℝ) (s : State A C I W)
    (query : C → Bool) :
    (projectedDecision μ σ input t s query).1 ⊆ s.attachments :=
  ProjectedSupportStep.splits_subset μ σ s.attachments s.support
    (fun i w => query (input i w)) t

/-- Literal child of the original transposed protocol under projected-mass
routing at the next floor. -/
noncomputable def projectedChild (μ : FiniteLaw S) (σ : I → W → S)
    (input : I → W → C) (t : ℝ) (s : State A C I W)
    (query : C → Bool) (P : Protocol A C Bool) (b : Bool) : State A C I W :=
  child s input query P (projectedDecision μ σ input t s query).1
    (projectedDecision μ σ input t s query).2 b

/-- The actual depth-indexed recursion stops before the first Alice node,
a leaf, or exhausted fuel. -/
noncomputable def runScheduled (μ : FiniteLaw S) (σ : I → W → S)
    (input : I → W → C) (floor : ℕ → ℝ) :
    ℕ → ℕ → State A C I W → SourceSupportFrontier.Tree (State A C I W)
  | _, 0, s => .stop s
  | d, fuel + 1, s =>
    match s.protocol with
    | .bNode query left right =>
      let decision := projectedDecision μ σ input (floor (d + 1)) s query
      .fork decision.1.card
        (runScheduled μ σ input floor (d + 1) fuel
          (child s input query left decision.1 decision.2 false))
        (runScheduled μ σ input floor (d + 1) fuel
          (child s input query right decision.1 decision.2 true))
    | _ => .stop s

/-- Every scheduled stop has its original physical Bob-only path and exact
reaching-column set. -/
theorem runScheduled_bobPath (μ : FiniteLaw S) (σ : I → W → S)
    (input : I → W → C) (floor : ℕ → ℝ)
    (d fuel : ℕ) (s : State A C I W) :
    ∀ v : (runScheduled μ σ input floor d fuel s).Leaves,
      BobPath s.protocol s.columns
        ((runScheduled μ σ input floor d fuel s).route v)
        ((runScheduled μ σ input floor d fuel s).state v).protocol
        ((runScheduled μ σ input floor d fuel s).state v).columns := by
  induction fuel generalizing d s with
  | zero => intro v; exact BobPath.here _ _
  | succ fuel ih =>
    rcases s with ⟨P, U, Q, Z, F⟩
    cases P with
    | leaf value => intro v; exact BobPath.here _ _
    | aNode query left right => intro v; exact BobPath.here _ _
    | bNode query left right =>
      intro v
      cases v with
      | inl v => exact BobPath.left (ih (d + 1) _ v)
      | inr v => exact BobPath.right (ih (d + 1) _ v)

/-- Scheduled path provenance includes exact evaluation and additive cost. -/
theorem runScheduled_eval_cost (μ : FiniteLaw S) (σ : I → W → S)
    (input : I → W → C) (floor : ℕ → ℝ)
    (d fuel : ℕ) (s : State A C I W) :
    ∀ v : (runScheduled μ σ input floor d fuel s).Leaves,
      (∀ a c, c ∈ ((runScheduled μ σ input floor d fuel s).state v).columns →
        ((runScheduled μ σ input floor d fuel s).state v).protocol.eval a c =
          s.protocol.eval a c) ∧
      ((runScheduled μ σ input floor d fuel s).state v).protocol.cost +
        ((runScheduled μ σ input floor d fuel s).route v).length ≤ s.protocol.cost := by
  intro v
  have hp := runScheduled_bobPath μ σ input floor d fuel s v
  exact ⟨hp.eval_eq, hp.cost_add_length⟩

/-- A route shorter than fuel stops at a leaf or before an Alice query. -/
theorem runScheduled_stopping (μ : FiniteLaw S) (σ : I → W → S)
    (input : I → W → C) (floor : ℕ → ℝ)
    (d fuel : ℕ) (s : State A C I W) :
    ∀ v : (runScheduled μ σ input floor d fuel s).Leaves,
      ((runScheduled μ σ input floor d fuel s).route v).length ≤ fuel ∧
      (((runScheduled μ σ input floor d fuel s).route v).length = fuel ∨
        NonBob ((runScheduled μ σ input floor d fuel s).state v).protocol) := by
  induction fuel generalizing d s with
  | zero => intro v; exact ⟨Nat.le_refl 0, Or.inl rfl⟩
  | succ fuel ih =>
    rcases s with ⟨P, U, Q, Z, F⟩
    cases P with
    | leaf value => intro v; exact ⟨Nat.zero_le _, Or.inr trivial⟩
    | aNode query left right => intro v; exact ⟨Nat.zero_le _, Or.inr trivial⟩
    | bNode query left right =>
      intro v
      cases v with
      | inl v =>
        obtain ⟨hle, heq | hstop⟩ := ih (d + 1) _ v
        · exact ⟨Nat.succ_le_succ hle, Or.inl (congrArg Nat.succ heq)⟩
        · exact ⟨Nat.succ_le_succ hle, Or.inr hstop⟩
      | inr v =>
        obtain ⟨hle, heq | hstop⟩ := ih (d + 1) _ v
        · exact ⟨Nat.succ_le_succ hle, Or.inl (congrArg Nat.succ heq)⟩
        · exact ⟨Nat.succ_le_succ hle, Or.inr hstop⟩

/-- Every surviving raw row takes the actual query bits to its stop. -/
theorem runScheduled_support_reaches (μ : FiniteLaw S) (σ : I → W → S)
    (input : I → W → C) (floor : ℕ → ℝ)
    (d fuel : ℕ) (s : State A C I W)
    (hs : ∀ i ∈ s.coordinates, ∀ w ∈ s.support i, input i w ∈ s.columns) :
    ∀ v : (runScheduled μ σ input floor d fuel s).Leaves,
      ∀ i ∈ ((runScheduled μ σ input floor d fuel s).state v).coordinates,
        ∀ w ∈ ((runScheduled μ σ input floor d fuel s).state v).support i,
          input i w ∈ ((runScheduled μ σ input floor d fuel s).state v).columns := by
  classical
  induction fuel generalizing d s with
  | zero => intro v; simpa [runScheduled, Tree.state] using hs
  | succ fuel ih =>
    rcases s with ⟨P, U, Q, Z, F⟩
    cases P with
    | leaf value => intro v; simpa [runScheduled, Tree.state] using hs
    | aNode query left right => intro v; simpa [runScheduled, Tree.state] using hs
    | bNode query left right =>
      let s0 : State A C I W := ⟨.bNode query left right, U, Q, Z, F⟩
      let t := floor (d + 1)
      intro v
      cases v with
      | inl v =>
        have hc := ProjectedSupportStep.childSupport_reaches μ σ Q Z F input
          query U t false hs
        have h := ih (d + 1)
          (projectedChild μ σ input t s0 query left false) (by
            simpa [projectedChild, projectedDecision, child,
              ProjectedSupportStep.childCoordinates,
              ProjectedSupportStep.childSupport] using hc) v
        simpa [runScheduled, projectedChild, projectedDecision, t] using h
      | inr v =>
        have hc := ProjectedSupportStep.childSupport_reaches μ σ Q Z F input
          query U t true hs
        have h := ih (d + 1)
          (projectedChild μ σ input t s0 query right true) (by
            simpa [projectedChild, projectedDecision, child,
              ProjectedSupportStep.childCoordinates,
              ProjectedSupportStep.childSupport] using hc) v
        simpa [runScheduled, projectedChild, projectedDecision, t] using h

/-- Each reached bin, attachment and original-row support descends from
its input state; no selector image is substituted for the raw support. -/
theorem runScheduled_sets_subset (μ : FiniteLaw S) (σ : I → W → S)
    (input : I → W → C) (floor : ℕ → ℝ)
    (d fuel : ℕ) (s : State A C I W) :
    ∀ v : (runScheduled μ σ input floor d fuel s).Leaves,
      ((runScheduled μ σ input floor d fuel s).state v).coordinates ⊆ s.coordinates ∧
      ((runScheduled μ σ input floor d fuel s).state v).attachments ⊆ s.attachments ∧
      ∀ i, ((runScheduled μ σ input floor d fuel s).state v).support i ⊆ s.support i := by
  classical
  induction fuel generalizing d s with
  | zero =>
    intro v
    simpa [runScheduled, Tree.state] using
      (show s.coordinates ⊆ s.coordinates ∧ s.attachments ⊆ s.attachments ∧
        ∀ i, s.support i ⊆ s.support i from
          ⟨Finset.Subset.refl _, Finset.Subset.refl _, fun _ => Finset.Subset.refl _⟩)
  | succ fuel ih =>
    rcases s with ⟨P, U, Q, Z, F⟩
    cases P with
    | leaf value =>
      intro v
      simpa [runScheduled, Tree.state] using
        (show Q ⊆ Q ∧ Z ⊆ Z ∧ ∀ i, F i ⊆ F i from
          ⟨Finset.Subset.refl _, Finset.Subset.refl _, fun _ => Finset.Subset.refl _⟩)
    | aNode query left right =>
      intro v
      simpa [runScheduled, Tree.state] using
        (show Q ⊆ Q ∧ Z ⊆ Z ∧ ∀ i, F i ⊆ F i from
          ⟨Finset.Subset.refl _, Finset.Subset.refl _, fun _ => Finset.Subset.refl _⟩)
    | bNode query left right =>
      let s0 : State A C I W := ⟨.bNode query left right, U, Q, Z, F⟩
      let t := floor (d + 1)
      intro v
      cases v with
      | inl v =>
        have h := ih (d + 1) (projectedChild μ σ input t s0 query left false) v
        have hQ : (projectedChild μ σ input t s0 query left false).coordinates ⊆ Q := by
          exact ProjectedSupportRouting.childCoordinates_subset _ _ _ _
        have hZ : (projectedChild μ σ input t s0 query left false).attachments ⊆ Z := by
          exact ProjectedSupportRouting.childAttachments_subset _ _ _ _
        simpa [runScheduled, projectedChild, projectedDecision, child, t] using
          (show ((runScheduled μ σ input floor (d + 1) fuel
            (projectedChild μ σ input t s0 query left false)).state v).coordinates ⊆ Q ∧
            ((runScheduled μ σ input floor (d + 1) fuel
              (projectedChild μ σ input t s0 query left false)).state v).attachments ⊆ Z ∧
            ∀ i, ((runScheduled μ σ input floor (d + 1) fuel
              (projectedChild μ σ input t s0 query left false)).state v).support i ⊆ F i from
            ⟨h.1.trans hQ, h.2.1.trans hZ,
              fun i => (h.2.2 i).trans (SourceSupportStep.fibre_subset _ _ _)⟩)
      | inr v =>
        have h := ih (d + 1) (projectedChild μ σ input t s0 query right true) v
        have hQ : (projectedChild μ σ input t s0 query right true).coordinates ⊆ Q := by
          exact ProjectedSupportRouting.childCoordinates_subset _ _ _ _
        have hZ : (projectedChild μ σ input t s0 query right true).attachments ⊆ Z := by
          exact ProjectedSupportRouting.childAttachments_subset _ _ _ _
        simpa [runScheduled, projectedChild, projectedDecision, child, t] using
          (show ((runScheduled μ σ input floor (d + 1) fuel
            (projectedChild μ σ input t s0 query right true)).state v).coordinates ⊆ Q ∧
            ((runScheduled μ σ input floor (d + 1) fuel
              (projectedChild μ σ input t s0 query right true)).state v).attachments ⊆ Z ∧
            ∀ i, ((runScheduled μ σ input floor (d + 1) fuel
              (projectedChild μ σ input t s0 query right true)).state v).support i ⊆ F i from
            ⟨h.1.trans hQ, h.2.1.trans hZ,
              fun i => (h.2.2 i).trans (SourceSupportStep.fibre_subset _ _ _)⟩)

/-- Selector-image floors propagate on every actual physical path. -/
theorem runScheduled_floor (μ : FiniteLaw S) (σ : I → W → S)
    (input : I → W → C) (floor : ℕ → ℝ)
    (hhalf : ∀ d, floor d = 2 * floor (d + 1))
    (d fuel : ℕ) (s : State A C I W)
    (hstart : ∀ i ∈ s.coordinates,
      floor d ≤ ProjectedSupportStep.mass μ (σ i) (s.support i)) :
    ∀ v : (runScheduled μ σ input floor d fuel s).Leaves,
      ∀ i ∈ ((runScheduled μ σ input floor d fuel s).state v).coordinates,
        floor (d + ((runScheduled μ σ input floor d fuel s).route v).length) ≤
          ProjectedSupportStep.mass μ (σ i)
            (((runScheduled μ σ input floor d fuel s).state v).support i) := by
  induction fuel generalizing d s with
  | zero => intro v; simpa [runScheduled, Tree.route, Tree.state] using hstart
  | succ fuel ih =>
    rcases s with ⟨P, U, Q, Z, F⟩
    cases P with
    | leaf value => intro v; simpa [runScheduled, Tree.route, Tree.state] using hstart
    | aNode query left right =>
      intro v; simpa [runScheduled, Tree.route, Tree.state] using hstart
    | bNode query left right =>
      let s0 : State A C I W := ⟨.bNode query left right, U, Q, Z, F⟩
      let t := floor (d + 1)
      have hn : ∀ i ∈ Q, 2 * t ≤ ProjectedSupportStep.mass μ (σ i) (F i) := by
        intro i hi
        have h := hstart i hi
        rw [hhalf d] at h
        exact h
      intro v
      cases v with
      | inl v =>
        have hc := ProjectedSupportStep.child_floor μ σ Q Z F
          (fun i w => query (input i w)) t false hn
        have h := ih (d + 1)
          (projectedChild μ σ input t s0 query left false) (by
            simpa [projectedChild, projectedDecision, child,
              ProjectedSupportStep.childCoordinates,
              ProjectedSupportStep.childSupport] using hc) v
        simpa [runScheduled, projectedChild, projectedDecision, t,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      | inr v =>
        have hc := ProjectedSupportStep.child_floor μ σ Q Z F
          (fun i w => query (input i w)) t true hn
        have h := ih (d + 1)
          (projectedChild μ σ input t s0 query right true) (by
            simpa [projectedChild, projectedDecision, child,
              ProjectedSupportStep.childCoordinates,
              ProjectedSupportStep.childSupport] using hc) v
        simpa [runScheduled, projectedChild, projectedDecision, t,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- The attached family retains its original ambient raw-law mass, up to
the finite halving loss. The law is not renormalized at intermediate nodes. -/
theorem runScheduled_attachment_floor [Fintype W]
    (κ : I → FiniteLaw W) (μ : FiniteLaw S) (σ : I → W → S)
    (input : I → W → C) (floor : ℕ → ℝ) (base : I → ℝ)
    (hhalf : ∀ d, floor d = 2 * floor (d + 1))
    (d fuel : ℕ) (s : State A C I W)
    (hσ : ∀ i ∈ s.attachments, (κ i).PushesTo μ (σ i))
    (hstart : ∀ i ∈ s.attachments,
      base i + floor d ≤ SourceSupportStep.mass (κ i) (s.support i)) :
    ∀ v : (runScheduled μ σ input floor d fuel s).Leaves,
      ∀ i ∈ ((runScheduled μ σ input floor d fuel s).state v).attachments,
        base i + floor (d + ((runScheduled μ σ input floor d fuel s).route v).length) ≤
          SourceSupportStep.mass (κ i)
            (((runScheduled μ σ input floor d fuel s).state v).support i) := by
  classical
  induction fuel generalizing d s with
  | zero => intro v; simpa [runScheduled, Tree.route, Tree.state] using hstart
  | succ fuel ih =>
    rcases s with ⟨P, U, Q, Z, F⟩
    cases P with
    | leaf value => intro v; simpa [runScheduled, Tree.route, Tree.state] using hstart
    | aNode query left right =>
      intro v; simpa [runScheduled, Tree.route, Tree.state] using hstart
    | bNode query left right =>
      let s0 : State A C I W := ⟨.bNode query left right, U, Q, Z, F⟩
      let t := floor (d + 1)
      have hn : ∀ i ∈ Z,
          base i + 2 * t ≤ SourceSupportStep.mass (κ i) (F i) := by
        intro i hi
        have h := hstart i hi
        rw [hhalf d] at h
        exact h
      intro v
      cases v with
      | inl v =>
        have hc := ProjectedSupportStep.attachment_floor κ μ σ Z F
          (fun i w => query (input i w)) t base false hσ hn
        have hs : ∀ i ∈ (projectedChild μ σ input t s0 query left false).attachments,
            (κ i).PushesTo μ (σ i) := by
          intro i hi
          exact hσ i ((ProjectedSupportRouting.childAttachments_subset _ _ _ _)
            (show i ∈ ProjectedSupportRouting.childAttachments Z
              (ProjectedSupportStep.splits μ σ Z F (fun i w => query (input i w)) t)
              (fun i => ProjectedSupportStep.heavyBit μ (σ i) (F i)
                (fun w => query (input i w))) false from hi))
        have h := ih (d + 1)
          (projectedChild μ σ input t s0 query left false) hs (by
            simpa [projectedChild, projectedDecision, child,
              ProjectedSupportStep.childAttachments,
              ProjectedSupportStep.childSupport] using hc) v
        simpa [runScheduled, projectedChild, projectedDecision, t,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      | inr v =>
        have hc := ProjectedSupportStep.attachment_floor κ μ σ Z F
          (fun i w => query (input i w)) t base true hσ hn
        have hs : ∀ i ∈ (projectedChild μ σ input t s0 query right true).attachments,
            (κ i).PushesTo μ (σ i) := by
          intro i hi
          exact hσ i ((ProjectedSupportRouting.childAttachments_subset _ _ _ _)
            (show i ∈ ProjectedSupportRouting.childAttachments Z
              (ProjectedSupportStep.splits μ σ Z F (fun i w => query (input i w)) t)
              (fun i => ProjectedSupportStep.heavyBit μ (σ i) (F i)
                (fun w => query (input i w))) true from hi))
        have h := ih (d + 1)
          (projectedChild μ σ input t s0 query right true) hs (by
            simpa [projectedChild, projectedDecision, child,
              ProjectedSupportStep.childAttachments,
              ProjectedSupportStep.childSupport] using hc) v
        simpa [runScheduled, projectedChild, projectedDecision, t,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- No attachment can leave its counted original outer bin. -/
theorem runScheduled_attachments_subset (μ : FiniteLaw S) (σ : I → W → S)
    (input : I → W → C) (floor : ℕ → ℝ)
    (d fuel : ℕ) (s : State A C I W)
    (hZ : s.attachments ⊆ s.coordinates) :
    ∀ v : (runScheduled μ σ input floor d fuel s).Leaves,
      ((runScheduled μ σ input floor d fuel s).state v).attachments ⊆
        ((runScheduled μ σ input floor d fuel s).state v).coordinates := by
  classical
  induction fuel generalizing d s with
  | zero => intro v; simpa [runScheduled, Tree.state] using hZ
  | succ fuel ih =>
    rcases s with ⟨P, U, Q, Z, F⟩
    cases P with
    | leaf value => intro v; simpa [runScheduled, Tree.state] using hZ
    | aNode query left right => intro v; simpa [runScheduled, Tree.state] using hZ
    | bNode query left right =>
      let s0 : State A C I W := ⟨.bNode query left right, U, Q, Z, F⟩
      let t := floor (d + 1)
      intro v
      cases v with
      | inl v =>
        have hc := ProjectedSupportStep.childAttachments_subset μ σ Q Z F
          (fun i w => query (input i w)) t false hZ
        have h := ih (d + 1)
          (projectedChild μ σ input t s0 query left false) (by
            simpa [projectedChild, projectedDecision, child,
              ProjectedSupportStep.childCoordinates,
              ProjectedSupportStep.childAttachments] using hc) v
        simpa [runScheduled, projectedChild, projectedDecision, t] using h
      | inr v =>
        have hc := ProjectedSupportStep.childAttachments_subset μ σ Q Z F
          (fun i w => query (input i w)) t true hZ
        have h := ih (d + 1)
          (projectedChild μ σ input t s0 query right true) (by
            simpa [projectedChild, projectedDecision, child,
              ProjectedSupportStep.childCoordinates,
              ProjectedSupportStep.childAttachments] using hc) v
        simpa [runScheduled, projectedChild, projectedDecision, t] using h

/-- Exact generated conservation of ordinary supports and unsplit
attachments, using the literal projected-mass split set at each node. -/
theorem runScheduled_counts (μ : FiniteLaw S) (σ : I → W → S)
    (input : I → W → C) (floor : ℕ → ℝ)
    (d fuel : ℕ) (s : State A C I W)
    (hZ : s.attachments ⊆ s.coordinates) :
    (∑ v : (runScheduled μ σ input floor d fuel s).Leaves,
      ((runScheduled μ σ input floor d fuel s).state v).coordinates.card) =
        s.coordinates.card + (runScheduled μ σ input floor d fuel s).totalSplits ∧
    (∑ v : (runScheduled μ σ input floor d fuel s).Leaves,
      ((runScheduled μ σ input floor d fuel s).state v).attachments.card) +
        (runScheduled μ σ input floor d fuel s).totalSplits = s.attachments.card := by
  classical
  induction fuel generalizing d s with
  | zero => simp [runScheduled, Tree.Leaves]
  | succ fuel ih =>
    rcases s with ⟨P, U, Q, Z, F⟩
    cases P with
    | leaf value => simp [runScheduled, Tree.Leaves]
    | aNode query left right => simp [runScheduled, Tree.Leaves]
    | bNode query left right =>
      let s0 : State A C I W := ⟨.bNode query left right, U, Q, Z, F⟩
      let t := floor (d + 1)
      let split := (projectedDecision μ σ input t s0 query).1
      let choose := (projectedDecision μ σ input t s0 query).2
      let sl := child s0 input query left split choose false
      let sr := child s0 input query right split choose true
      let tl := runScheduled μ σ input floor (d + 1) fuel sl
      let tr := runScheduled μ σ input floor (d + 1) fuel sr
      have hs : split ⊆ Z := projectedDecision_subset μ σ input t s0 query
      have hsQ : split ⊆ Q := hs.trans hZ
      have hl := ih (d + 1) sl (ProjectedSupportRouting.childAttachments_subset_childCoordinates
        Q Z split choose false hZ)
      have hr := ih (d + 1) sr (ProjectedSupportRouting.childAttachments_subset_childCoordinates
        Q Z split choose true hZ)
      have hQ := ProjectedSupportRouting.childCoordinates_card Q split choose hsQ
      have hA := ProjectedSupportRouting.childAttachments_card Z split choose hs
      change (∑ v : (Tree.fork split.card tl tr).Leaves,
          ((Tree.fork split.card tl tr).state v).coordinates.card) =
          Q.card + (Tree.fork split.card tl tr).totalSplits ∧
        (∑ v : (Tree.fork split.card tl tr).Leaves,
          ((Tree.fork split.card tl tr).state v).attachments.card) +
          (Tree.fork split.card tl tr).totalSplits = Z.card
      rw [Tree.sum_state_fork split.card tl tr (fun x : State A C I W => x.coordinates.card),
        Tree.sum_state_fork split.card tl tr (fun x : State A C I W => x.attachments.card)]
      simp only [Tree.totalSplits]
      dsimp only [tl, tr, sl, sr, child, s0] at hl hr ⊢
      omega

/-- The actual scheduled frontier has an overloaded nonempty physical
position. This uses only generated counts and actual prefix-free paths. -/
theorem runScheduled_active_overload (μ : FiniteLaw S) (σ : I → W → S)
    (input : I → W → C) (floor : ℕ → ℝ)
    (d fuel : ℕ) (s : State A C I W)
    (hZ : s.attachments ⊆ s.coordinates) (q b : ℕ)
    (hcount : s.coordinates.card + b = q)
    (hexcess : 3 * b < s.attachments.card) :
    ∃ v : Active (runScheduled μ σ input floor d fuel s),
      3 * ((q : ℝ) / 2 ^ ((runScheduled μ σ input floor d fuel s).route v.val).length) / 4 ≤
        (((runScheduled μ σ input floor d fuel s).state v.val).coordinates.card : ℝ) ∧
      (q : ℝ) / 2 ^ ((runScheduled μ σ input floor d fuel s).route v.val).length <
        (((runScheduled μ σ input floor d fuel s).state v.val).coordinates.card : ℝ) +
          (((runScheduled μ σ input floor d fuel s).state v.val).attachments.card : ℝ) := by
  classical
  let T := runScheduled μ σ input floor d fuel s
  have hz : ∀ v : T.Leaves, (T.state v).attachments ⊆ (T.state v).coordinates :=
    runScheduled_attachments_subset μ σ input floor d fuel s hZ
  have hc := runScheduled_counts μ σ input floor d fuel s hZ
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

/-- Raw-set subtraction has the expected ambient-law mass when the smaller
set is contained in the larger one. -/
theorem raw_mass_sdiff_add [Fintype W] [DecidableEq W] (κ : FiniteLaw W)
    (F G : Finset W) (h : G ⊆ F) :
    SourceSupportStep.mass κ (F \ G) + SourceSupportStep.mass κ G =
      SourceSupportStep.mass κ F := by
  classical
  unfold SourceSupportStep.mass FiniteLaw.prob
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hwG : w ∈ G
  · have hwF := h hwG
    simp [hwG, hwF]
  · by_cases hwF : w ∈ F <;> simp [hwG, hwF]

/-- A surviving attachment has lost at most the finite telescoping budget
`floor d - floor actualDepth` in its *original* ambient row law. -/
theorem runScheduled_raw_loss [Fintype W]
    [DecidableEq W]
    (κ : I → FiniteLaw W) (μ : FiniteLaw S) (σ : I → W → S)
    (input : I → W → C) (floor : ℕ → ℝ)
    (hhalf : ∀ d, floor d = 2 * floor (d + 1))
    (d fuel : ℕ) (s : State A C I W)
    (hσ : ∀ i ∈ s.attachments, (κ i).PushesTo μ (σ i)) :
    ∀ v : (runScheduled μ σ input floor d fuel s).Leaves,
      ∀ i ∈ ((runScheduled μ σ input floor d fuel s).state v).attachments,
        SourceSupportStep.mass (κ i)
          (s.support i \ ((runScheduled μ σ input floor d fuel s).state v).support i) ≤
          floor d - floor (d + ((runScheduled μ σ input floor d fuel s).route v).length) := by
  intro v i hi
  let base : I → ℝ := fun j => SourceSupportStep.mass (κ j) (s.support j) - floor d
  have hinit : ∀ j ∈ s.attachments,
      base j + floor d ≤ SourceSupportStep.mass (κ j) (s.support j) := by
    intro j _
    dsimp [base]
    linarith
  have hmass := runScheduled_attachment_floor κ μ σ input floor base hhalf
    d fuel s hσ hinit v i hi
  have hsub := (runScheduled_sets_subset μ σ input floor d fuel s v).2.2 i
  have heq := raw_mass_sdiff_add (κ i) (s.support i)
    (((runScheduled μ σ input floor d fuel s).state v).support i) hsub
  dsimp [base] at hmass
  linarith

/-- The finite telescoping bound has the strict endpoint required by the
paired-retention condition, including at depth zero. -/
theorem runScheduled_raw_loss_lt [Fintype W] [DecidableEq W]
    (κ : I → FiniteLaw W) (μ : FiniteLaw S) (σ : I → W → S)
    (input : I → W → C) (floor : ℕ → ℝ)
    (hhalf : ∀ d, floor d = 2 * floor (d + 1))
    (hpos : ∀ d, 0 < floor d)
    (d fuel : ℕ) (s : State A C I W)
    (hσ : ∀ i ∈ s.attachments, (κ i).PushesTo μ (σ i)) :
    ∀ v : (runScheduled μ σ input floor d fuel s).Leaves,
      ∀ i ∈ ((runScheduled μ σ input floor d fuel s).state v).attachments,
        SourceSupportStep.mass (κ i)
          (s.support i \ ((runScheduled μ σ input floor d fuel s).state v).support i) <
          floor d := by
  intro v i hi
  have h := runScheduled_raw_loss κ μ σ input floor hhalf d fuel s hσ v i hi
  have hp := hpos (d + ((runScheduled μ σ input floor d fuel s).route v).length)
  linarith

end Paper2.ProjectedSupportFrontier
