import Paper2.RecursiveSamplingExecution

/-!
# Every-tape upper bounds for the actual capped sampled matrix

Frozen v12 Appendix D, the every-tape YES preservation and zero-on-abort
paragraphs. A successful interpreter result is a reachable leaf of the
original finite-choice program. In the table program, each such leaf is
an actual indexed restriction of the same recursive source matrix. The
abort output is constant. Consequently no random tape increases its
deterministic communication complexity. This proves neither a machine
runtime nor that the source matrix has a particular YES budget.
-/

namespace Paper2.RecursiveSamplingProgram.Program

variable {A B : Type*}

/-- An actual output leaf along a sequence of permitted finite choices. -/
def Reaches : Program A → A → Prop
  | .pure a, b => a = b
  | .draw _ _ next, b => ∃ i, Reaches (next i) b

theorem reaches_map_iff (f : A → B) (p : Program A) (b : B) :
    Reaches (map f p) b ↔ ∃ a, Reaches p a ∧ f a = b := by
  induction p with
  | pure a => simp [Reaches]
  | draw n hn next ih =>
    simp only [map_draw, Reaches, ih]
    constructor
    · rintro ⟨i, a, ha, hb⟩
      exact ⟨a, ⟨i, ha⟩, hb⟩
    · rintro ⟨a, ⟨i, ha⟩, hb⟩
      exact ⟨i, a, ha, hb⟩

end Paper2.RecursiveSamplingProgram.Program

namespace Paper2.RecursiveSamplingCapped

open RecursiveSamplingProgram

variable {A : Type*}

theorem reaches_of_step (p : Program A) (i : Fin (denominator p))
    (a : A) (h : Program.Reaches (step p i) a) : Program.Reaches p a := by
  cases p with
  | pure b => exact h
  | draw n hn next => exact ⟨i, h⟩

/-- Every reachable leaf of a successfully obtained residual state was
already reachable in the original program. No probability hypothesis is used. -/
theorem runState_reaches {M : ℕ} (B R : ℕ) (hMB : Nat.clog 2 M ≤ B)
    (N : ℕ) (s : State A M) (t : CappedSampler.Adaptive.Tape B R N)
    (u : State A M) (hu : runState B R hMB N s t = some u)
    (a : A) (ha : Program.Reaches u.val a) : Program.Reaches s.val a := by
  induction N generalizing s u with
  | zero =>
    simp only [runState, CappedSampler.Adaptive.run, Option.some.injEq] at hu
    subst u
    exact ha
  | succ N ih =>
    change (CappedSampler.runWideBits (stateDenominator s) B R (state_width hMB s) t.1).bind
      (fun i => runState B R hMB N (stateStep s i) t.2) = some u at hu
    cases hd : CappedSampler.runWideBits (stateDenominator s) B R (state_width hMB s) t.1 with
    | none => simp [hd] at hu
    | some i =>
      simp only [hd, Option.bind_some] at hu
      exact reaches_of_step s.val i a (ih (stateStep s i) t.2 u hu ha)

/-- The interpreter cannot manufacture an output absent from its input tree. -/
theorem run_reaches {M : ℕ} (B R : ℕ) (hMB : Nat.clog 2 M ≤ B)
    (N : ℕ) (s : State A M) (t : CappedSampler.Adaptive.Tape B R N)
    (a : A) (ha : run B R hMB N s t = some a) : Program.Reaches s.val a := by
  unfold run at ha
  cases hu : runState B R hMB N s t with
  | none => simp [hu] at ha
  | some u =>
    simp only [hu, Option.bind_some] at ha
    apply runState_reaches B R hMB N s t u hu a
    cases hp : u.val with
    | pure b => simpa only [hp, readResult, Option.some.injEq] using ha
    | draw n hn next => simp [hp, readResult] at ha

end Paper2.RecursiveSamplingCapped

namespace Paper2.RecursiveSampling

open SourceMatrix RecursiveEntries RecursiveSamplingProgram
open Workspace.Types.CommComplexity

variable {X₀ Y₀ V : Type} [Fintype V] [Nonempty V]
  {s q₁ q₂ w Q : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q]

/-- Each reachable table output uses genuine generated input arrays; the
array pair itself is a reachable leaf of the actual sampling program. -/
theorem tableProgram_reaches (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (row₀ : Program X₀) (col₀ : Program Y₀) (F : X₀ → Y₀ → Bool)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : Tails X₀ Y₀ (SourceConstruction.Items s V) s q₁ q₂ w Q)
    (k mX mY : ℕ) (T : Fin mX → Fin mY → Bool)
    (hT : Program.Reaches (tableProgram order hs row₀ col₀ F activity ξ k mX mY) T) :
    ∃ labels, Program.Reaches (samples (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
        order hs row₀ col₀ k mX mY) labels ∧
      T = RecursiveEntries.table F activity ξ k labels.2 labels.1 := by
  obtain ⟨labels, hl, hT⟩ := (Program.reaches_map_iff _ _ T).mp hT
  exact ⟨labels, hl, hT.symm⟩

theorem tableProgram_reaches_D_le [Fintype X₀] [Fintype Y₀]
    (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (row₀ : Program X₀) (col₀ : Program Y₀) (F : X₀ → Y₀ → Bool)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : Tails X₀ Y₀ (SourceConstruction.Items s V) s q₁ q₂ w Q)
    (k mX mY : ℕ) (T : Fin mX → Fin mY → Bool)
    (hT : Program.Reaches (tableProgram order hs row₀ col₀ F activity ξ k mX mY) T) :
    D T ≤ D (RecursiveEntries.matrix F activity ξ k) := by
  obtain ⟨labels, _, rfl⟩ := tableProgram_reaches order hs row₀ col₀ F activity ξ k mX mY T hT
  rw [RecursiveEntries.table_eq_sampleMatrix]
  exact sample_D_le _ labels.2 labels.1

end Paper2.RecursiveSampling

namespace Paper2.RecursiveSamplingExecution

open SourceMatrix RecursiveEntries RecursiveSamplingProgram
open Workspace.Types.CommComplexity Workspace.Types.Protocol

variable {V : Type} [Fintype V] [Nonempty V]
  {s q₁ q₂ w Q : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q]

/-- A single zero-output leaf witnesses zero communication even if one
of the output index sets is empty. -/
theorem zero_table_D (mX mY : ℕ) : D (fun (_ : Fin mX) (_ : Fin mY) => false) = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact Nat.sInf_le ⟨Protocol.leaf false, rfl, fun _ _ => rfl⟩

/-- Every public tape either outputs a genuine sampled restriction or the
constant abort table. Neither case increases communication complexity. -/
theorem run_D_le (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (p : ℕ) (hp : 0 < p)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s V) s q₁ q₂ w Q)
    (k mX mY : ℕ) (t : Tape V s q₁ q₂ w Q p k mX mY) :
    D (run order hs p hp activity ξ k mX mY t) ≤
      D (RecursiveEntries.matrix (LookupSeed.matrix p) activity ξ k) := by
  cases hrun : RecursiveSamplingCapped.run _ _ le_rfl _
      (state order hs p hp activity ξ k mX mY) t with
  | none =>
    rw [run_eq_zero_of_abort order hs p hp activity ξ k mX mY t hrun, zero_table_D]
    exact Nat.zero_le _
  | some T =>
    have hT := RecursiveSamplingCapped.run_reaches _ _ le_rfl _
      (state order hs p hp activity ξ k mX mY) t T hrun
    change Program.Reaches (RecursiveSampling.tableProgram order hs
      (RecursiveSamplingSeed.seedRow p) (RecursiveSamplingSeed.seedColumn p hp)
      (LookupSeed.matrix p) activity ξ k mX mY) T at hT
    have hD := RecursiveSampling.tableProgram_reaches_D_le order hs
      (RecursiveSamplingSeed.seedRow p) (RecursiveSamplingSeed.seedColumn p hp)
      (LookupSeed.matrix p) activity ξ k mX mY T hT
    simpa only [run, hrun, CappedSampler.completed] using hD

end Paper2.RecursiveSamplingExecution
