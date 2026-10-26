import Paper2.Frontier

/-!
# Actual binary paths of a finite stopping tree

This is the finite tree bookkeeping used for the stopping frontier in the
locked v12 source's remaining-conversation argument, Section 4,
`src:frontier`. The leaves are positions in the tree, not state values:
distinct leaves remain distinct even when their stored states are equal.
Prefix-freeness therefore follows from the actual binary paths, without an
assumed frontier certificate. The mathematical stopping rule and support
invariants are supplied separately.
-/

namespace Paper2.SourceSupportFrontier

open scoped BigOperators

/-- A finite stopping tree. A fork records its local number of split witnesses. -/
inductive Tree (σ : Type*) where
  | stop (state : σ)
  | fork (splits : ℕ) (left right : Tree σ)

namespace Tree

variable {σ : Type*}

/-- A leaf is a position, distinguished recursively by its left/right choices. -/
def Leaves : Tree σ → Type
  | .stop _ => Unit
  | .fork _ left right => Leaves left ⊕ Leaves right

instance leavesFintype : (T : Tree σ) → Fintype T.Leaves
  | .stop _ => inferInstanceAs (Fintype Unit)
  | .fork _ left right => by
      letI := leavesFintype left
      letI := leavesFintype right
      exact inferInstanceAs (Fintype (Leaves left ⊕ Leaves right))

noncomputable instance leavesDecidableEq (T : Tree σ) : DecidableEq T.Leaves :=
  Classical.decEq _

/-- The state stored at the specified leaf position. -/
def state : (T : Tree σ) → T.Leaves → σ
  | .stop s, _ => s
  | .fork _ left _, .inl v => state left v
  | .fork _ _ right, .inr v => state right v

/-- The actual binary path to a leaf; false means left and true means right. -/
def route : (T : Tree σ) → T.Leaves → List Bool
  | .stop _, _ => []
  | .fork _ left _, .inl v => false :: route left v
  | .fork _ _ right, .inr v => true :: route right v

/-- Total number of witness splits recorded at internal nodes. -/
def totalSplits : Tree σ → ℕ
  | .stop _ => 0
  | .fork splits left right => splits + totalSplits left + totalSplits right

/-- Maximum number of edges from the root to a stopping leaf. -/
def depth : Tree σ → ℕ
  | .stop _ => 0
  | .fork _ left right => 1 + max (depth left) (depth right)

@[simp] theorem state_stop (s : σ) (v : (Tree.stop s).Leaves) :
    (Tree.stop s).state v = s := rfl

@[simp] theorem state_fork_inl (splits : ℕ) (left right : Tree σ)
    (v : left.Leaves) :
    (Tree.fork splits left right).state (.inl v) = left.state v := rfl

@[simp] theorem state_fork_inr (splits : ℕ) (left right : Tree σ)
    (v : right.Leaves) :
    (Tree.fork splits left right).state (.inr v) = right.state v := rfl

@[simp] theorem route_stop (s : σ) (v : (Tree.stop s).Leaves) :
    (Tree.stop s).route v = [] := rfl

@[simp] theorem route_fork_inl (splits : ℕ) (left right : Tree σ)
    (v : left.Leaves) :
    (Tree.fork splits left right).route (.inl v) = false :: left.route v := rfl

@[simp] theorem route_fork_inr (splits : ℕ) (left right : Tree σ)
    (v : right.Leaves) :
    (Tree.fork splits left right).route (.inr v) = true :: right.route v := rfl

@[simp] theorem totalSplits_stop (s : σ) :
    (Tree.stop s).totalSplits = 0 := rfl

@[simp] theorem totalSplits_fork (splits : ℕ) (left right : Tree σ) :
    (Tree.fork splits left right).totalSplits =
      splits + left.totalSplits + right.totalSplits := rfl

/-- Sums over the two child frontiers use their actual disjoint positions. -/
@[simp] theorem sum_fork {M : Type*} [AddCommMonoid M]
    (splits : ℕ) (left right : Tree σ)
    (f : (Tree.fork splits left right).Leaves → M) :
    ∑ v, f v = (∑ v : left.Leaves, f (.inl v)) +
      ∑ v : right.Leaves, f (.inr v) := by
  exact Fintype.sum_sum_type f

@[simp] theorem sum_stop {M : Type*} [AddCommMonoid M]
    (s : σ) (f : (Tree.stop s).Leaves → M) :
    ∑ v, f v = f () := by
  change (∑ v : Unit, f v) = f ()
  exact Fintype.sum_unique (fun v : Unit => f v)

/-- State-valued summands expose the fork even when the leaf type is opaque. -/
@[simp] theorem sum_state_fork {M : Type*} [AddCommMonoid M]
    (splits : ℕ) (left right : Tree σ) (f : σ → M) :
    (∑ v, f ((Tree.fork splits left right).state v)) =
      (∑ v : left.Leaves, f (left.state v)) +
        ∑ v : right.Leaves, f (right.state v) := by
  exact sum_fork splits left right (fun v => f ((Tree.fork splits left right).state v))

@[simp] theorem sum_state_stop {M : Type*} [AddCommMonoid M]
    (s : σ) (f : σ → M) :
    (∑ v, f ((Tree.stop s).state v)) = f s := by
  exact sum_stop s (fun v => f ((Tree.stop s).state v))

/-- Distinct stopping positions have incomparable binary paths. -/
theorem prefixFree (T : Tree σ) : Frontier.PrefixFree T.route := by
  induction T with
  | stop s =>
      intro v w hne
      exact (hne (@Subsingleton.elim Unit _ v w)).elim
  | fork splits left right ihl ihr =>
      intro v w hne hp
      cases v with
      | inl v =>
          cases w with
          | inl w =>
              exact ihl v w (fun h => hne (congrArg Sum.inl h))
                (List.cons_prefix_cons.mp hp).2
          | inr w =>
              have h := (List.cons_prefix_cons.mp hp).1
              exact Bool.false_ne_true h
      | inr v =>
          cases w with
          | inl w =>
              have h := (List.cons_prefix_cons.mp hp).1
              exact Bool.false_ne_true h.symm
          | inr w =>
              exact ihr v w (fun h => hne (congrArg Sum.inr h))
                (List.cons_prefix_cons.mp hp).2

/-- Leaf positions can be recovered uniquely from their paths. -/
theorem route_injective (T : Tree σ) : Function.Injective T.route := by
  intro v w h
  by_contra hne
  apply T.prefixFree v w hne
  rw [h]

theorem route_length_le_depth (T : Tree σ) (v : T.Leaves) :
    (T.route v).length ≤ T.depth := by
  induction T with
  | stop s => simp [depth]
  | fork splits left right ihl ihr =>
      cases v with
      | inl v =>
          have h := ihl v
          simp only [route_fork_inl, List.length_cons, depth]
          omega
      | inr v =>
          have h := ihr v
          simp only [route_fork_inr, List.length_cons, depth]
          omega

end Tree

end Paper2.SourceSupportFrontier
