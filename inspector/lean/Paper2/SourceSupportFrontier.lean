import Paper2.SourceSupportStep
import Paper2.SourceSupportFrontierTree
import Workspace.Types.Protocol

/-!
# The actual Bob-only stopping tree

Frozen v12, Section 4, `src:near-full`.  Recursion follows the original
protocol, stops before an Alice message or a leaf, and uses an explicit
depth cap.  States contain only actual objects, not certificates of the
count identities or lower bounds needed later.  Empty-coordinate branches
are retained; their contribution to support and attachment counts is zero.
-/

namespace Paper2.SourceSupportFrontier

open Workspace.Types.Protocol SourceSupportStep
open scoped BigOperators

variable {A C I W : Type*} [Fintype W]

/-- Rows and column labels retain their original types throughout the walk. -/
structure State (A C I W : Type*) where
  protocol : Protocol A C Bool
  columns : Set C
  coordinates : Finset I
  attachments : Finset I
  support : I → Finset W

/-- A child is an actual subtree and its supports use the actual Bob bit. -/
noncomputable def child (μ : FiniteLaw W) (input : I → W → C)
    (t : ℝ) (s : State A C I W) (query : C → Bool)
    (P : Protocol A C Bool) (b : Bool) : State A C I W where
  protocol := P
  columns := {c | c ∈ s.columns ∧ query c = b}
  coordinates := childCoordinates μ s.coordinates s.attachments s.support
    (fun i w => query (input i w)) t b
  attachments := childAttachments μ s.attachments s.support
    (fun i w => query (input i w)) t b
  support := childSupport s.support (fun i w => query (input i w)) b

/-- Follow only Bob nodes. The floor supplied at a transition is the next
depth's support floor. A returned leaf has its own physical binary path. -/
noncomputable def run (μ : FiniteLaw W) (input : I → W → C)
    (floor : ℕ → ℝ) : ℕ → ℕ → State A C I W → Tree (State A C I W)
  | _, 0, s => .stop s
  | depth, fuel + 1, s =>
    match s.protocol with
    | .bNode query left right =>
      .fork (splits μ s.attachments s.support
        (fun i w => query (input i w)) (floor (depth + 1))).card
        (run μ input floor (depth + 1) fuel
          (child μ input (floor (depth + 1)) s query left false))
        (run μ input floor (depth + 1) fuel
          (child μ input (floor (depth + 1)) s query right true))
    | _ => .stop s

/-- Any state property preserved by each literal Bob transition is true
at every generated stopping node, with its actual path length. -/
theorem run_invariant (μ : FiniteLaw W) (input : I → W → C)
    (floor : ℕ → ℝ) (Good : ℕ → State A C I W → Prop)
    (hstep : ∀ d s query left right, s.protocol = .bNode query left right →
      Good d s → ∀ b, Good (d + 1)
        (child μ input (floor (d + 1)) s query (if b then right else left) b))
    (d fuel : ℕ) (s : State A C I W) (hs : Good d s) :
    ∀ v : (run μ input floor d fuel s).Leaves,
      Good (d + ((run μ input floor d fuel s).route v).length)
        ((run μ input floor d fuel s).state v) := by
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

/-- Attachments remain a subset of the counted supports at every stop. -/
theorem run_attachments_subset (μ : FiniteLaw W) (input : I → W → C)
    (floor : ℕ → ℝ) (d fuel : ℕ) (s : State A C I W)
    (hZ : s.attachments ⊆ s.coordinates) :
    ∀ v : (run μ input floor d fuel s).Leaves,
      ((run μ input floor d fuel s).state v).attachments ⊆
        ((run μ input floor d fuel s).state v).coordinates := by
  apply run_invariant μ input floor (fun _ t => t.attachments ⊆ t.coordinates)
    _ d fuel s hZ
  intro d t query left right _ ht b
  exact childAttachments_subset μ t.coordinates t.attachments t.support _ _ b ht

/-- Global count identities follow from the generated transitions. -/
theorem run_counts (μ : FiniteLaw W) (input : I → W → C)
    (floor : ℕ → ℝ) (d fuel : ℕ) (s : State A C I W)
    (hZ : s.attachments ⊆ s.coordinates) :
    (∑ v : (run μ input floor d fuel s).Leaves,
      ((run μ input floor d fuel s).state v).coordinates.card) =
        s.coordinates.card + (run μ input floor d fuel s).totalSplits ∧
    (∑ v : (run μ input floor d fuel s).Leaves,
      ((run μ input floor d fuel s).state v).attachments.card) +
        (run μ input floor d fuel s).totalSplits = s.attachments.card := by
  induction fuel generalizing d s with
  | zero => simp [run, Tree.Leaves]
  | succ fuel ih =>
    rcases s with ⟨P, U, Q, Z, S⟩
    cases P with
    | leaf value => simp [run, Tree.Leaves]
    | aNode query left right => simp [run, Tree.Leaves]
    | bNode query left right =>
      have hl := ih (d + 1)
        (child μ input (floor (d + 1)) ⟨.bNode query left right, U, Q, Z, S⟩
          query left false)
        (childAttachments_subset μ Q Z S _ _ false hZ)
      have hr := ih (d + 1)
        (child μ input (floor (d + 1)) ⟨.bNode query left right, U, Q, Z, S⟩
          query right true)
        (childAttachments_subset μ Q Z S _ _ true hZ)
      have hQ := childCoordinates_card μ Q Z S (fun i w => query (input i w))
        (floor (d + 1)) hZ
      have hA := childAttachments_card μ Z S (fun i w => query (input i w))
        (floor (d + 1))
      let sl := child μ input (floor (d + 1))
        (State.mk (.bNode query left right) U Q Z S) query left false
      let sr := child μ input (floor (d + 1))
        (State.mk (.bNode query left right) U Q Z S) query right true
      let tl := run μ input floor (d + 1) fuel sl
      let tr := run μ input floor (d + 1) fuel sr
      let n := (splits μ Z S (fun i w => query (input i w)) (floor (d + 1))).card
      change (∑ v : (Tree.fork n tl tr).Leaves,
          ((Tree.fork n tl tr).state v).coordinates.card) =
          Q.card + (Tree.fork n tl tr).totalSplits ∧
        (∑ v : (Tree.fork n tl tr).Leaves,
          ((Tree.fork n tl tr).state v).attachments.card) +
          (Tree.fork n tl tr).totalSplits = Z.card
      rw [Tree.sum_state_fork n tl tr (fun t : State A C I W => t.coordinates.card),
        Tree.sum_state_fork n tl tr (fun t : State A C I W => t.attachments.card)]
      simp only [Tree.totalSplits]
      dsimp only [tl, tr, sl, sr, n, child] at hl hr ⊢
      omega

/-- The support floor and the stronger unsplit-attachment floor propagate
along actual messages, for any exact halving schedule. -/
theorem run_mass_floors (μ : FiniteLaw W) (input : I → W → C)
    (floor : ℕ → ℝ) (hhalf : ∀ d, floor d = 2 * floor (d + 1))
    (base : ℝ) (d fuel : ℕ) (s : State A C I W)
    (hQ : ∀ i ∈ s.coordinates, floor d ≤ mass μ (s.support i))
    (hZ : ∀ i ∈ s.attachments, base + floor d ≤ mass μ (s.support i)) :
    ∀ v : (run μ input floor d fuel s).Leaves,
      (∀ i ∈ ((run μ input floor d fuel s).state v).coordinates,
        floor (d + ((run μ input floor d fuel s).route v).length) ≤
          mass μ (((run μ input floor d fuel s).state v).support i)) ∧
      (∀ i ∈ ((run μ input floor d fuel s).state v).attachments,
        base + floor (d + ((run μ input floor d fuel s).route v).length) ≤
          mass μ (((run μ input floor d fuel s).state v).support i)) := by
  apply run_invariant μ input floor
    (fun d t => (∀ i ∈ t.coordinates, floor d ≤ mass μ (t.support i)) ∧
      (∀ i ∈ t.attachments, base + floor d ≤ mass μ (t.support i))) _ d fuel s ⟨hQ, hZ⟩
  intro d t query left right _ ht b
  constructor
  · apply child_floor μ t.coordinates t.attachments t.support _ _ b
    simpa only [← hhalf d] using ht.1
  · apply attachment_floor μ t.attachments t.support _ _ base b
    simpa only [← hhalf d] using ht.2

/-- A physical path consisting only of original Bob nodes. The column set
at its endpoint is the exact iterated query fibre of the original set. -/
inductive BobPath : Protocol A C Bool → Set C → List Bool →
    Protocol A C Bool → Set C → Prop
  | here (P : Protocol A C Bool) (U : Set C) : BobPath P U [] P U
  | left {query : C → Bool} {left right Q : Protocol A C Bool}
      {U V : Set C} {path : List Bool}
      (h : BobPath left {c | c ∈ U ∧ query c = false} path Q V) :
      BobPath (.bNode query left right) U (false :: path) Q V
  | right {query : C → Bool} {left right Q : Protocol A C Bool}
      {U V : Set C} {path : List Bool}
      (h : BobPath right {c | c ∈ U ∧ query c = true} path Q V) :
      BobPath (.bNode query left right) U (true :: path) Q V

theorem BobPath.columns_subset {P Q : Protocol A C Bool} {U V : Set C}
    {path : List Bool} (h : BobPath P U path Q V) : V ⊆ U := by
  induction h with
  | here => exact Set.Subset.rfl
  | left _ ih => exact fun c hc => (ih hc).1
  | right _ ih => exact fun c hc => (ih hc).1

theorem BobPath.eval_eq {P Q : Protocol A C Bool} {U V : Set C}
    {path : List Bool} (h : BobPath P U path Q V) :
    ∀ a c, c ∈ V → Q.eval a c = P.eval a c := by
  induction h with
  | here => intros; rfl
  | left h ih =>
    intro a c hc
    have hq := (h.columns_subset hc).2
    simpa [Protocol.eval, hq] using ih a c hc
  | right h ih =>
    intro a c hc
    have hq := (h.columns_subset hc).2
    simpa [Protocol.eval, hq] using ih a c hc

theorem BobPath.cost_add_length {P Q : Protocol A C Bool} {U V : Set C}
    {path : List Bool} (h : BobPath P U path Q V) :
    Q.cost + path.length ≤ P.cost := by
  induction h with
  | here => simp
  | @left query left right Q U V path h ih =>
    simp only [List.length_cons, Protocol.cost]
    have := Nat.le_max_left left.cost right.cost
    omega
  | @right query left right Q U V path h ih =>
    simp only [List.length_cons, Protocol.cost]
    have := Nat.le_max_right left.cost right.cost
    omega

/-- Every stopping state is literally connected to the input protocol by
the recorded Bob-only path, on its exact original reaching-column set. -/
theorem run_bobPath (μ : FiniteLaw W) (input : I → W → C)
    (floor : ℕ → ℝ) (d fuel : ℕ) (s : State A C I W) :
    ∀ v : (run μ input floor d fuel s).Leaves,
      BobPath s.protocol s.columns ((run μ input floor d fuel s).route v)
        ((run μ input floor d fuel s).state v).protocol
        ((run μ input floor d fuel s).state v).columns := by
  induction fuel generalizing d s with
  | zero => intro v; exact BobPath.here _ _
  | succ fuel ih =>
    rcases s with ⟨P, U, Q, Z, S⟩
    cases P with
    | leaf value => intro v; exact BobPath.here _ _
    | aNode query left right => intro v; exact BobPath.here _ _
    | bNode query left right =>
      intro v
      cases v with
      | inl v => exact BobPath.left (ih (d + 1) _ v)
      | inr v => exact BobPath.right (ih (d + 1) _ v)

/-- Every counted support word reaches that physical node on its literal
original input label, uniformly for all rows. -/
theorem run_support_reaches (μ : FiniteLaw W) (input : I → W → C)
    (floor : ℕ → ℝ) (d fuel : ℕ) (s : State A C I W)
    (hs : ∀ i ∈ s.coordinates, ∀ w ∈ s.support i, input i w ∈ s.columns) :
    ∀ v : (run μ input floor d fuel s).Leaves,
      ∀ i ∈ ((run μ input floor d fuel s).state v).coordinates,
        ∀ w ∈ ((run μ input floor d fuel s).state v).support i,
          input i w ∈ ((run μ input floor d fuel s).state v).columns := by
  apply run_invariant μ input floor
    (fun _ t => ∀ i ∈ t.coordinates, ∀ w ∈ t.support i, input i w ∈ t.columns)
    _ d fuel s hs
  intro d t query left right _ ht b
  exact childSupport_reaches μ t.coordinates t.attachments t.support input query
    t.columns (floor (d + 1)) b ht

/-- Recursion stops before a non-Bob node; it never consumes an Alice bit. -/
def NonBob : Protocol A C Bool → Prop
  | .leaf _ => True
  | .aNode _ _ _ => True
  | .bNode _ _ _ => False

/-- A stopping path has used at most the supplied fuel, and either uses all
of it or ends at a leaf or an Alice node. This is a property of `run`. -/
theorem run_stopping (μ : FiniteLaw W) (input : I → W → C)
    (floor : ℕ → ℝ) (d fuel : ℕ) (s : State A C I W) :
    ∀ v : (run μ input floor d fuel s).Leaves,
      ((run μ input floor d fuel s).route v).length ≤ fuel ∧
      (((run μ input floor d fuel s).route v).length = fuel ∨
        NonBob ((run μ input floor d fuel s).state v).protocol) := by
  induction fuel generalizing d s with
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
        obtain ⟨hle, heq | hstop⟩ := ih (d + 1) _ v
        · exact ⟨Nat.succ_le_succ hle, Or.inl (congrArg Nat.succ heq)⟩
        · exact ⟨Nat.succ_le_succ hle, Or.inr hstop⟩
      | inr v =>
        obtain ⟨hle, heq | hstop⟩ := ih (d + 1) _ v
        · exact ⟨Nat.succ_le_succ hle, Or.inl (congrArg Nat.succ heq)⟩
        · exact ⟨Nat.succ_le_succ hle, Or.inr hstop⟩

/-- All coordinate and attachment labels, and every full word, retain their
original provenance. In particular surviving attachments retain the same
coordinate-indexed collision data supplied at initialization. -/
theorem run_sets_subset (μ : FiniteLaw W) (input : I → W → C)
    (floor : ℕ → ℝ) (d fuel : ℕ) (s : State A C I W) :
    ∀ v : (run μ input floor d fuel s).Leaves,
      ((run μ input floor d fuel s).state v).coordinates ⊆ s.coordinates ∧
      ((run μ input floor d fuel s).state v).attachments ⊆ s.attachments ∧
      ∀ i, ((run μ input floor d fuel s).state v).support i ⊆ s.support i := by
  apply run_invariant μ input floor
    (fun _ t => t.coordinates ⊆ s.coordinates ∧ t.attachments ⊆ s.attachments ∧
      ∀ i, t.support i ⊆ s.support i) _ d fuel s
    ⟨Finset.Subset.refl _, Finset.Subset.refl _, fun _ => Finset.Subset.refl _⟩
  intro d t query left right _ ht b
  refine ⟨?_, ?_, ?_⟩
  · exact (childCoordinates_subset μ t.coordinates t.attachments t.support _ _ b).trans ht.1
  · intro i hi
    exact ht.2.1 ((mem_childAttachments μ t.attachments t.support _ _ b i).mp hi).1
  · intro i
    exact (fibre_subset (t.support i) (fun w => query (input i w)) b).trans (ht.2.2 i)

end Paper2.SourceSupportFrontier
