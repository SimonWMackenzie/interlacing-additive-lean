import Paper2.RecursiveSamplingCapped

/-!
Private v27 sampler core. Source: `appendices/D-implementation.tex:84--105` and
`sections/06-reduction.tex:77--80` in `2026-10-12-proof-exposition-v27`.
Each capped elementary draw has a positive current denominator. Exhaustion
selects its first member and continues with the remaining independent blocks.
-/

namespace Paper2.CappedSampler.Adaptive

variable {S : Type*} (D : S → ℕ) (next : (s : S) → Fin (D s) → S)
  (B R : ℕ) (hB : ∀ s, Nat.clog 2 (D s) ≤ B) (hD : ∀ s, 0 < D s)

/-- A total fixed-tape execution that defaults each exhausted draw locally. -/
def runFallback : (n : ℕ) → S → Tape B R n → S
  | 0, s, _ => s
  | n + 1, s, t =>
      let i := (runWideBits (D s) B R (hB s) t.1).getD ⟨0, hD s⟩
      runFallback n (next s i) t.2

@[simp] theorem runFallback_zero (s : S) (t : Tape B R 0) :
    runFallback D next B R hB hD 0 s t = s := rfl

theorem runFallback_succ (n : ℕ) (s : S) (t : Tape B R (n + 1)) :
    runFallback D next B R hB hD (n + 1) s t =
      runFallback D next B R hB hD n
        (next s ((runWideBits (D s) B R (hB s) t.1).getD ⟨0, hD s⟩)) t.2 := rfl

/-- When the old partial runner succeeds, both interpreters use the identical
choice at every reached node of the same tape. -/
theorem runFallback_eq_of_run_eq_some (n : ℕ) (s : S) (t : Tape B R n)
    (u : S) (hu : run D next B R hB n s t = some u) :
    runFallback D next B R hB hD n s t = u := by
  induction n generalizing s u with
  | zero =>
      simp only [run, Option.some.injEq] at hu
      simpa [runFallback] using hu
  | succ n ih =>
      cases hr : runWideBits (D s) B R (hB s) t.1 with
      | none => simp [run, hr] at hu
      | some i =>
          have hs : run D next B R hB n (next s i) t.2 = some u := by
            simpa [run, hr] using hu
          simpa [runFallback_succ, hr] using ih (next s i) t.2 u hs


end Paper2.CappedSampler.Adaptive

namespace Paper2.RecursiveSamplingCapped

open RecursiveSamplingProgram

variable {A : Type*}

/-- The manuscript's per-draw fallback on the residual program state. -/
def runStateFallback {M : ℕ} (B R : ℕ) (hMB : Nat.clog 2 M ≤ B)
    (N : ℕ) (s : State A M) (t : CappedSampler.Adaptive.Tape B R N) : State A M :=
  CappedSampler.Adaptive.runFallback stateDenominator stateStep B R
    (state_width hMB) stateDenominator_pos N s t

theorem runStateFallback_draws_le {M : ℕ} (B R : ℕ) (hMB : Nat.clog 2 M ≤ B)
    (N : ℕ) (s : State A M) (t : CappedSampler.Adaptive.Tape B R N) :
    (runStateFallback B R hMB N s t).val.maxDraws ≤ s.val.maxDraws - N := by
  induction N generalizing s with
  | zero => simp [runStateFallback, CappedSampler.Adaptive.runFallback]
  | succ N ih =>
      let i : Fin (stateDenominator s) :=
        (CappedSampler.runWideBits (stateDenominator s) B R
          (state_width hMB s) t.1).getD ⟨0, stateDenominator_pos s⟩
      have hstep := step_maxDraws_le s.val i
      have hrec := ih (stateStep s i) t.2
      change (stateStep s i).val.maxDraws ≤ s.val.maxDraws - 1 at hstep
      change (runStateFallback B R hMB N (stateStep s i) t.2).val.maxDraws ≤
        (stateStep s i).val.maxDraws - N at hrec
      change (runStateFallback B R hMB (N + 1) s t).val.maxDraws ≤ _
      change (runStateFallback B R hMB N (stateStep s i) t.2).val.maxDraws ≤ _
      omega

theorem runStateFallback_pure {M : ℕ} (B R : ℕ) (hMB : Nat.clog 2 M ≤ B)
    (N : ℕ) (s : State A M) (hN : s.val.maxDraws ≤ N)
    (t : CappedSampler.Adaptive.Tape B R N) :
    ∃ a, (runStateFallback B R hMB N s t).val = .pure a := by
  apply pure_of_maxDraws_zero
  have h := runStateFallback_draws_le B R hMB N s t
  omega

/-- Extract the value of a program with no remaining draws. -/
def leafValue (p : Program A) (hp : p.maxDraws = 0) : A :=
  match p with
  | .pure a => a
  | .draw _ _ _ => False.elim (by simp at hp)

@[simp] theorem leafValue_pure (a : A) (h : (Program.pure a).maxDraws = 0) :
    leafValue (.pure a) h = a := rfl

/-- A total executable leaf extractor. The impossible `draw` branch is
eliminated using the proved public draw-count bound. -/
def runProgramFallback {M : ℕ} (B R : ℕ) (hMB : Nat.clog 2 M ≤ B)
    (N : ℕ) (s : State A M) (hN : s.val.maxDraws ≤ N)
    (t : CappedSampler.Adaptive.Tape B R N) : A :=
  leafValue (runStateFallback B R hMB N s t).val (by
    have h := runStateFallback_draws_le B R hMB N s t
    omega)

theorem runProgramFallback_eq_leaf {M : ℕ} (B R : ℕ) (hMB : Nat.clog 2 M ≤ B)
    (N : ℕ) (s : State A M) (hN : s.val.maxDraws ≤ N)
    (t : CappedSampler.Adaptive.Tape B R N) (a : A)
    (ha : (runStateFallback B R hMB N s t).val = .pure a) :
    runProgramFallback B R hMB N s hN t = a := by
  simp [runProgramFallback, ha]

theorem runStateFallback_eq_of_runState_eq_some {M : ℕ} (B R : ℕ)
    (hMB : Nat.clog 2 M ≤ B) (N : ℕ) (s u : State A M)
    (t : CappedSampler.Adaptive.Tape B R N)
    (hu : runState B R hMB N s t = some u) :
    runStateFallback B R hMB N s t = u :=
  CappedSampler.Adaptive.runFallback_eq_of_run_eq_some
    stateDenominator stateStep B R (state_width hMB) stateDenominator_pos N s t u hu

end Paper2.RecursiveSamplingCapped

#print axioms Paper2.CappedSampler.Adaptive.runFallback_eq_of_run_eq_some
#print axioms Paper2.RecursiveSamplingCapped.runStateFallback_pure
#print axioms Paper2.RecursiveSamplingCapped.runProgramFallback_eq_leaf
