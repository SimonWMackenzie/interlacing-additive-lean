import Paper2.RecursiveSamplingExecution

/-! A capped finite-choice execution either aborts or returns a leaf of its
actual finite program. Applied to the table program, a successful leaf is
the recursive matrix on one pair of sampled indexed label arrays. -/

namespace Paper2.GenericSamplerRunSplit

open Paper2.RecursiveSamplingProgram
open Paper2.RecursiveSamplingCapped
open Paper2.RecursiveSampling
open Paper2.RecursiveSamplingExecution
open Paper2.RecursiveEntries
open Paper2.RecursiveSamplingSeed

def AllLeaves {A : Type*} (P : A → Prop) : Program A → Prop
  | .pure a => P a
  | .draw _ _ next => ∀ i, AllLeaves P (next i)

theorem allLeaves_step {A : Type*} (P : A → Prop) (p : Program A)
    (i : Fin (denominator p)) (h : AllLeaves P p) :
    AllLeaves P (step p i) := by
  cases p with
  | pure a => exact h
  | draw n hn next => exact h i

theorem allLeaves_map {A B : Type*} (P : B → Prop)
    (f : A → B) (p : Program A) (h : ∀ a, P (f a)) :
    AllLeaves P (Program.map f p) := by
  induction p with
  | pure a => exact h a
  | draw n hn next ih => exact fun i => ih i

theorem runState_allLeaves {A : Type*} {M : ℕ}
    (P : A → Prop) (B R : ℕ) (hMB : Nat.clog 2 M ≤ B)
    (N : ℕ) (s : State A M) (t : CappedSampler.Adaptive.Tape B R N)
    (u : State A M) (hu : runState B R hMB N s t = some u)
    (hs : AllLeaves P s.val) : AllLeaves P u.val := by
  induction N generalizing s u with
  | zero =>
      simp only [runState, CappedSampler.Adaptive.run, Option.some.injEq] at hu
      subst u
      exact hs
  | succ N ih =>
      change (CappedSampler.runWideBits (stateDenominator s) B R
        (state_width hMB s) t.1).bind
          (fun i => runState B R hMB N (stateStep s i) t.2) = some u at hu
      cases hd : CappedSampler.runWideBits (stateDenominator s) B R
          (state_width hMB s) t.1 with
      | none => simp [hd] at hu
      | some i =>
          simp only [hd, Option.bind_some] at hu
          exact ih (stateStep s i) t.2 u hu
            (allLeaves_step P s.val i hs)

theorem run_some_leaf {A : Type*} {M : ℕ}
    (P : A → Prop) (B R : ℕ) (hMB : Nat.clog 2 M ≤ B)
    (N : ℕ) (s : State A M) (t : CappedSampler.Adaptive.Tape B R N)
    (a : A) (ha : run B R hMB N s t = some a)
    (hs : AllLeaves P s.val) : P a := by
  cases hu : runState B R hMB N s t with
  | none => simp [RecursiveSamplingCapped.run, hu] at ha
  | some u =>
      have hleaf := runState_allLeaves P B R hMB N s t u hu hs
      cases hv : u.val with
      | pure b =>
          simp only [RecursiveSamplingCapped.run, hu, Option.bind_some, hv,
            readResult] at ha
          cases ha
          simpa only [AllLeaves, hv] using hleaf
      | draw n hn next =>
          simp only [RecursiveSamplingCapped.run, hu, Option.bind_some, hv,
            readResult] at ha
          cases ha

variable {V : Type} [Fintype V] [Nonempty V]
  {s q₁ q₂ w Q : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q]

theorem successful_run_is_sampled_table
    (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (p : ℕ) (hp : 0 < p)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s V)
      s q₁ q₂ w Q)
    (k mX mY : ℕ)
    (t : Tape V s q₁ q₂ w Q p k mX mY)
    (M : Fin mX → Fin mY → Bool)
    (h : RecursiveSamplingCapped.run _ _ le_rfl _
      (state order hs p hp activity ξ k mX mY) t = some M) :
    ∃ rows : Fin mX → Row (Fin p → Bool) (Fin p)
        (SourceConstruction.Items s V) s q₁ q₂ w Q k,
      ∃ cols : Fin mY → Column (Fin p → Bool) (Fin p)
        (SourceConstruction.Items s V) s q₁ q₂ w Q k,
        M = RecursiveEntries.table (LookupSeed.matrix p) activity ξ k rows cols := by
  let F : (Fin mY → Column (Fin p → Bool) (Fin p)
        (SourceConstruction.Items s V) s q₁ q₂ w Q k) ×
      (Fin mX → Row (Fin p → Bool) (Fin p)
        (SourceConstruction.Items s V) s q₁ q₂ w Q k) →
      Fin mX → Fin mY → Bool :=
    fun pair => RecursiveEntries.table (LookupSeed.matrix p) activity ξ k pair.2 pair.1
  have hall : AllLeaves (fun T => ∃ pair, T = F pair)
      (state order hs p hp activity ξ k mX mY).val := by
    change AllLeaves (fun T => ∃ pair, T = F pair)
      (RecursiveSampling.tableProgram order hs (seedRow p) (seedColumn p hp)
        (LookupSeed.matrix p) activity ξ k mX mY)
    exact allLeaves_map _ F _ (fun pair => ⟨pair, rfl⟩)
  obtain ⟨pair, hpair⟩ := run_some_leaf
    (fun T => ∃ pair, T = F pair) _ _ le_rfl _
    (state order hs p hp activity ξ k mX mY) t M h hall
  exact ⟨pair.2, pair.1, hpair⟩

theorem run_sampled_table_or_zero
    (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (p : ℕ) (hp : 0 < p)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s V)
      s q₁ q₂ w Q)
    (k mX mY : ℕ)
    (t : Tape V s q₁ q₂ w Q p k mX mY) :
    (∃ rows cols,
      RecursiveSamplingExecution.run order hs p hp activity ξ k mX mY t =
        RecursiveEntries.table (LookupSeed.matrix p) activity ξ k rows cols) ∨
    RecursiveSamplingExecution.run order hs p hp activity ξ k mX mY t =
      (fun _ _ => false) := by
  cases h : RecursiveSamplingCapped.run _ _ le_rfl _
      (state order hs p hp activity ξ k mX mY) t with
  | none =>
      exact Or.inr (run_eq_zero_of_abort order hs p hp activity ξ k mX mY t h)
  | some M =>
      obtain ⟨rows, cols, heq⟩ := successful_run_is_sampled_table
        order hs p hp activity ξ k mX mY t M h
      left
      exact ⟨rows, cols, by
        simp [RecursiveSamplingExecution.run, CappedSampler.completed, h, heq]⟩

#print axioms run_sampled_table_or_zero

end Paper2.GenericSamplerRunSplit
