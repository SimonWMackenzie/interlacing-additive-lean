import Paper2.PairedSupportStep
import Paper2.SourceSupportFrontier

/-!
# The actual paired-support stopping tree

Frozen v12, Section 5, `res:paired`. A pair consists of two independently
routed tagged supports. If they choose different children, they remain
separate tagged singles thereafter. In particular a separated foreign
support remains counted. This is not the single-support splitting rule
used in Section 4.
-/

namespace Paper2.PairedSupportFrontier

open Workspace.Types.Protocol SourceSupportFrontier SourceSupportStep
open scoped BigOperators

variable {A C I W : Type*} [Fintype W]

/-- Actual protocol and reaching columns, with single and paired full-word
supports. The structure has no desired-invariant or count-certificate fields. -/
structure State (A C I W : Type*) where
  protocol : Protocol A C Bool
  columns : Set C
  singles : Finset (Bool × I)
  pairs : Finset I
  support : (Bool × I) → Finset W

namespace State

def h (s : State A C I W) : ℕ := s.singles.card + s.pairs.card

def z (s : State A C I W) : ℕ := s.pairs.card

def Valid (s : State A C I W) : Prop := PairedSupportStep.Valid s.singles s.pairs

noncomputable def blocks (s : State A C I W) : Finset (Bool × I) :=
  PairedSupportStep.active s.singles s.pairs

omit [Fintype W] in
theorem z_le_h (s : State A C I W) : s.z ≤ s.h := by
  simp only [z, h]
  omega

end State

/-- Both members use their own heavier fibre of the actual Bob query. -/
noncomputable def child (μ : FiniteLaw W) (input : (Bool × I) → W → C)
    (s : State A C I W) (query : C → Bool)
    (P : Protocol A C Bool) (b : Bool) : State A C I W where
  protocol := P
  columns := {c | c ∈ s.columns ∧ query c = b}
  singles := PairedSupportStep.childSingles μ s.singles s.pairs s.support
    (fun i w => query (input i w)) b
  pairs := PairedSupportStep.childPairs μ s.pairs s.support
    (fun i w => query (input i w)) b
  support := PairedSupportStep.childSupport s.support (fun i w => query (input i w)) b

/-- Stop before the first Alice query, at a leaf, or at the fuel limit.
Unlike Section 4 routing, the paired heavy-child rule does not use a floor. -/
noncomputable def run (μ : FiniteLaw W) (input : (Bool × I) → W → C) :
    ℕ → State A C I W → SourceSupportFrontier.Tree (State A C I W)
  | 0, s => .stop s
  | fuel + 1, s =>
    match s.protocol with
    | .bNode query left right =>
      .fork (PairedSupportStep.splitPairs μ s.pairs s.support
        (fun i w => query (input i w))).card
        (run μ input fuel (child μ input s query left false))
        (run μ input fuel (child μ input s query right true))
    | _ => .stop s

/-- Local preservation implies the corresponding property at every actual
stopping state and its actual depth. -/
theorem run_invariant (μ : FiniteLaw W) (input : (Bool × I) → W → C)
    (Good : ℕ → State A C I W → Prop)
    (hstep : ∀ d s query left right, s.protocol = .bNode query left right →
      Good d s → ∀ b, Good (d + 1)
        (child μ input s query (if b then right else left) b))
    (d fuel : ℕ) (s : State A C I W) (hs : Good d s) :
    ∀ v : (run μ input fuel s).Leaves,
      Good (d + ((run μ input fuel s).route v).length)
        ((run μ input fuel s).state v) := by
  induction fuel generalizing d s with
  | zero => intro v; simpa [run, Tree.route, Tree.state] using hs
  | succ fuel ih =>
    rcases s with ⟨P, U, S, Z, F⟩
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

/-- Physical paths, protocol subtrees and exact reaching-column fibres are
the same objects used in the recursion, not supplied by a certificate. -/
theorem run_bobPath (μ : FiniteLaw W) (input : (Bool × I) → W → C)
    (fuel : ℕ) (s : State A C I W) :
    ∀ v : (run μ input fuel s).Leaves,
      BobPath s.protocol s.columns ((run μ input fuel s).route v)
        ((run μ input fuel s).state v).protocol
        ((run μ input fuel s).state v).columns := by
  induction fuel generalizing s with
  | zero => intro v; exact BobPath.here _ _
  | succ fuel ih =>
    rcases s with ⟨P, U, S, Z, F⟩
    cases P with
    | leaf value => intro v; exact BobPath.here _ _
    | aNode query left right => intro v; exact BobPath.here _ _
    | bNode query left right =>
      intro v
      cases v with
      | inl v => exact BobPath.left (ih _ v)
      | inr v => exact BobPath.right (ih _ v)

/-- The recursion never consumes an Alice bit. Fuel exhaustion is an
explicit stopping reason, to be ruled out separately for live supports. -/
theorem run_stopping (μ : FiniteLaw W) (input : (Bool × I) → W → C)
    (fuel : ℕ) (s : State A C I W) :
    ∀ v : (run μ input fuel s).Leaves,
      ((run μ input fuel s).route v).length ≤ fuel ∧
      (((run μ input fuel s).route v).length = fuel ∨
        NonBob ((run μ input fuel s).state v).protocol) := by
  induction fuel generalizing s with
  | zero => intro v; exact ⟨Nat.le_refl 0, Or.inl rfl⟩
  | succ fuel ih =>
    rcases s with ⟨P, U, S, Z, F⟩
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

/-- No single tagged block overlaps a pair at any generated stop. -/
theorem run_valid (μ : FiniteLaw W) (input : (Bool × I) → W → C)
    (fuel : ℕ) (s : State A C I W) (hs : s.Valid) :
    ∀ v : (run μ input fuel s).Leaves, ((run μ input fuel s).state v).Valid := by
  apply run_invariant μ input (fun _ t => t.Valid) _ 0 fuel s hs
  intro d t query left right _ ht b
  exact PairedSupportStep.child_valid μ t.singles t.pairs t.support _ b ht

/-- Every active member, including a separated foreign singleton, keeps
the corresponding half-mass floor along its own actual message path. -/
theorem run_mass_floors (μ : FiniteLaw W) (input : (Bool × I) → W → C)
    (floor : ℕ → ℝ) (hhalf : ∀ d, floor d = 2 * floor (d + 1))
    (d fuel : ℕ) (s : State A C I W)
    (hs : ∀ a ∈ s.blocks, floor d ≤ mass μ (s.support a)) :
    ∀ v : (run μ input fuel s).Leaves,
      ∀ a ∈ ((run μ input fuel s).state v).blocks,
        floor (d + ((run μ input fuel s).route v).length) ≤
          mass μ (((run μ input fuel s).state v).support a) := by
  apply run_invariant μ input
    (fun d t => ∀ a ∈ t.blocks, floor d ≤ mass μ (t.support a)) _ d fuel s hs
  intro d t query left right _ ht b
  apply PairedSupportStep.child_floor μ t.singles t.pairs t.support _ _ b
  simpa only [← hhalf d] using ht

/-- Every active support uses the same original input and reaches its
exact query-fibre column set uniformly for all unchanged row labels. -/
theorem run_support_reaches (μ : FiniteLaw W) (input : (Bool × I) → W → C)
    (fuel : ℕ) (s : State A C I W)
    (hs : ∀ a ∈ s.blocks, ∀ w ∈ s.support a, input a w ∈ s.columns) :
    ∀ v : (run μ input fuel s).Leaves,
      ∀ a ∈ ((run μ input fuel s).state v).blocks,
        ∀ w ∈ ((run μ input fuel s).state v).support a,
          input a w ∈ ((run μ input fuel s).state v).columns := by
  apply run_invariant μ input
    (fun _ t => ∀ a ∈ t.blocks, ∀ w ∈ t.support a, input a w ∈ t.columns)
    _ 0 fuel s hs
  intro d t query left right _ ht b
  exact PairedSupportStep.child_reaches μ t.singles t.pairs t.support input query
    t.columns b ht

/-- Tagged block and word provenance never change. A split pair can create
new singles, so the correct preserved set is all active tagged blocks,
not the initial singleton set alone. -/
theorem run_sets_subset (μ : FiniteLaw W) (input : (Bool × I) → W → C)
    (fuel : ℕ) (s : State A C I W) :
    ∀ v : (run μ input fuel s).Leaves,
      ((run μ input fuel s).state v).blocks ⊆ s.blocks ∧
      ((run μ input fuel s).state v).pairs ⊆ s.pairs ∧
      ∀ a, ((run μ input fuel s).state v).support a ⊆ s.support a := by
  apply run_invariant μ input
    (fun _ t => t.blocks ⊆ s.blocks ∧ t.pairs ⊆ s.pairs ∧
      ∀ a, t.support a ⊆ s.support a) _ 0 fuel s
    ⟨Finset.Subset.refl _, Finset.Subset.refl _, fun _ => Finset.Subset.refl _⟩
  intro d t query left right _ ht b
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    exact ht.1 ((PairedSupportStep.child_active_iff μ t.singles t.pairs t.support _ b a).mp ha).1
  · intro i hi
    exact ht.2.1 ((PairedSupportStep.mem_childPairs μ t.pairs t.support _ b i).mp hi).1
  · intro a
    exact (fibre_subset (t.support a) (fun w => query (input a w)) b).trans (ht.2.2 a)

end Paper2.PairedSupportFrontier
