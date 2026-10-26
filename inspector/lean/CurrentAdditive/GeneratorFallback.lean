import CurrentAdditive.AdaptiveFallback
import Paper2.GeneratorResult

/-!
First-order generator implementation of the same per-draw fallback semantics.
This is the explicit code-stack interpreter, not yet a TM2 machine program.
-/

namespace Paper2.GeneratorCode

private theorem wide_cast {D E B R : Nat} (h : D = E)
    (hD : Nat.clog 2 D ≤ B) (hE : Nat.clog 2 E ≤ B)
    (t : CappedSampler.BitTape B R) :
    (CappedSampler.runWideBits D B R hD t).map (Fin.cast h) =
      CappedSampler.runWideBits E B R hE t := by
  subst E
  simp

/-- The actual generator stack consumes every public block. A failed current
draw advances with the first member of its current positive alphabet. -/
def cappedFallback {M : Nat} (B R : Nat) (hMB : Nat.clog 2 M ≤ B)
    (N : Nat) (s : BoundedState M) (t : CappedSampler.Adaptive.Tape B R N) :
    BoundedState M :=
  CappedSampler.Adaptive.runFallback den next B R (den_width hMB) den_pos N s t

/-- Same-tape equality of explicit code-stack execution and residual-program
semantics, including all tapes on which a cap is exhausted. -/
theorem cappedFallback_semantic {M : Nat} (B R : Nat)
    (hMB : Nat.clog 2 M ≤ B) (N : Nat) (s : BoundedState M)
    (t : CappedSampler.Adaptive.Tape B R N) :
    semantic (cappedFallback B R hMB N s t) =
      RecursiveSamplingCapped.runStateFallback B R hMB N (semantic s) t := by
  induction N generalizing s with
  | zero => rfl
  | succ N ih =>
      let i : Fin (den s) :=
        (CappedSampler.runWideBits (den s) B R (den_width hMB s) t.1).getD
          ⟨0, den_pos s⟩
      have hden : den s = RecursiveSamplingCapped.stateDenominator (semantic s) := den_eq s
      have hw := wide_cast hden (den_width hMB s)
        (RecursiveSamplingCapped.state_width hMB (semantic s)) t.1
      have hi : semanticTicket s i =
          (CappedSampler.runWideBits
            (RecursiveSamplingCapped.stateDenominator (semantic s)) B R
            (RecursiveSamplingCapped.state_width hMB (semantic s)) t.1).getD
              ⟨0, RecursiveSamplingCapped.stateDenominator_pos (semantic s)⟩ := by
        rw [← hw]
        cases hr : CappedSampler.runWideBits (den s) B R (den_width hMB s) t.1 with
        | none =>
            simp [i, hr, semanticTicket]
        | some j =>
            simp [i, hr, semanticTicket]
            exact Fin.ext rfl
      change semantic
        (cappedFallback B R hMB N (next s i) t.2) =
        RecursiveSamplingCapped.runStateFallback B R hMB N
          (RecursiveSamplingCapped.stateStep (semantic s)
            ((CappedSampler.runWideBits
              (RecursiveSamplingCapped.stateDenominator (semantic s)) B R
              (RecursiveSamplingCapped.state_width hMB (semantic s)) t.1).getD
                ⟨0, RecursiveSamplingCapped.stateDenominator_pos (semantic s)⟩)) t.2
      rw [← hi, ← next_semantic]
      exact ih (next s i) t.2

theorem cappedFallback_eq_of_capped_eq_some {M : Nat} (B R : Nat)
    (hMB : Nat.clog 2 M ≤ B) (N : Nat) (s u : BoundedState M)
    (t : CappedSampler.Adaptive.Tape B R N)
    (hu : capped B R hMB N s t = some u) :
    cappedFallback B R hMB N s t = u :=
  CappedSampler.Adaptive.runFallback_eq_of_run_eq_some
    den next B R (den_width hMB) den_pos N s t u hu

theorem read_cappedFallback_some {M : Nat} (B R : Nat)
    (hMB : Nat.clog 2 M ≤ B) (N : Nat) (s : BoundedState M)
    (hN : (stateMeaning s.val).maxDraws ≤ N)
    (t : CappedSampler.Adaptive.Tape B R N) :
    ∃ bits, read (cappedFallback B R hMB N s t).val = some bits := by
  obtain ⟨bits, hb⟩ := RecursiveSamplingCapped.runStateFallback_pure
    B R hMB N (semantic s) hN t
  have hs : stateMeaning (cappedFallback B R hMB N s t).val =
      RecursiveSamplingProgram.Program.pure bits := by
    change (semantic (cappedFallback B R hMB N s t)).val = _
    rw [cappedFallback_semantic, hb]
  exact ⟨bits, by rw [read_eq, hs]; rfl⟩

/-- The first-order stack evaluator always returns bits after the public
number of draws. Its impossible branch is eliminated by the progress proof. -/
def runCodeFallback {M : Nat} (B R : Nat) (hMB : Nat.clog 2 M ≤ B)
    (N : Nat) (s : BoundedState M)
    (hN : (stateMeaning s.val).maxDraws ≤ N)
    (t : CappedSampler.Adaptive.Tape B R N) : List Bool :=
  (read (cappedFallback B R hMB N s t).val).get (by
    obtain ⟨bits, hb⟩ := read_cappedFallback_some B R hMB N s hN t
    simp [hb])

/-- This explicit code-stack result is the same complete original label as
the residual-program interpreter on every fixed tape. -/
theorem runCodeFallback_eq_program {M : Nat} (B R : Nat)
    (hMB : Nat.clog 2 M ≤ B) (N : Nat) (s : BoundedState M)
    (hN : (stateMeaning s.val).maxDraws ≤ N)
    (t : CappedSampler.Adaptive.Tape B R N) :
    runCodeFallback B R hMB N s hN t =
      RecursiveSamplingCapped.runProgramFallback B R hMB N (semantic s) hN t := by
  obtain ⟨bits, hb⟩ := RecursiveSamplingCapped.runStateFallback_pure
    B R hMB N (semantic s) hN t
  have hs : stateMeaning (cappedFallback B R hMB N s t).val =
      RecursiveSamplingProgram.Program.pure bits := by
    change (semantic (cappedFallback B R hMB N s t)).val = _
    rw [cappedFallback_semantic, hb]
  have hread : read (cappedFallback B R hMB N s t).val = some bits := by
    rw [read_eq, hs]; rfl
  rw [RecursiveSamplingCapped.runProgramFallback_eq_leaf B R hMB N (semantic s) hN t bits hb]
  simp [runCodeFallback, hread]

theorem runCodeFallback_eq_of_run_eq_some {M : Nat} (B R : Nat)
    (hMB : Nat.clog 2 M ≤ B) (N : Nat) (s : BoundedState M)
    (hN : (stateMeaning s.val).maxDraws ≤ N)
    (t : CappedSampler.Adaptive.Tape B R N) (bits : List Bool)
    (h : run B R hMB N s t = some bits) :
    runCodeFallback B R hMB N s hN t = bits := by
  unfold run at h
  cases hc : capped B R hMB N s t with
  | none => simp [hc] at h
  | some u =>
      have hr : read u.val = some bits := by simpa [hc] using h
      have hf := cappedFallback_eq_of_capped_eq_some B R hMB N s u t hc
      simp [runCodeFallback, hf, hr]

end Paper2.GeneratorCode

#print axioms Paper2.GeneratorCode.cappedFallback_semantic
#print axioms Paper2.GeneratorCode.runCodeFallback_eq_program
#print axioms Paper2.GeneratorCode.runCodeFallback_eq_of_run_eq_some
