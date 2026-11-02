import Paper2.GeneratorExecution

/-! The same capped fair-bit execution, now with a first-order generator state.
Proof fields bound its alphabet; they do not supply an execution or a runtime. -/
namespace Paper2.GeneratorCode

open RecursiveSamplingProgram

def BoundedState (M : Nat) := {s : State // (stateMeaning s).maxAlphabet ≤ M}

def den {M : Nat} (s : BoundedState M) : Nat := request (normalize s.val)

def semantic {M : Nat} (s : BoundedState M) : RecursiveSamplingCapped.State (List Bool) M :=
  ⟨stateMeaning s.val, s.property⟩

theorem den_eq {M : Nat} (s : BoundedState M) :
    den s = RecursiveSamplingCapped.denominator (stateMeaning s.val) := by
  rw [den, ← ready_request (normalize s.val) (normalize_ready s.val), normalize_meaning]

def semanticTicket {M : Nat} (s : BoundedState M) (i : Fin (den s)) :
    Fin (RecursiveSamplingCapped.stateDenominator (semantic s)) :=
  ⟨i.val, by simpa only [semantic, RecursiveSamplingCapped.stateDenominator, ← den_eq] using i.isLt⟩

def nextRaw {M : Nat} (s : BoundedState M) (i : Fin (den s)) : State :=
  advance (normalize s.val) i.val

theorem program_step_congr {A : Type} {p q : Program A} (hp : p = q)
    (i : Fin (RecursiveSamplingCapped.denominator p))
    (j : Fin (RecursiveSamplingCapped.denominator q)) (hij : i.val = j.val) :
    RecursiveSamplingCapped.step p i = RecursiveSamplingCapped.step q j := by
  subst q
  have he : i = j := Fin.ext hij
  subst j
  rfl

theorem nextRaw_meaning {M : Nat} (s : BoundedState M) (i : Fin (den s)) :
    stateMeaning (nextRaw s i) =
      RecursiveSamplingCapped.step (stateMeaning s.val) (semanticTicket s i) := by
  have h := ready_step (normalize s.val) (normalize_ready s.val) i
  exact h.trans (program_step_congr (normalize_meaning s.val) _ _ rfl)

def next {M : Nat} (s : BoundedState M) (i : Fin (den s)) : BoundedState M :=
  ⟨nextRaw s i, by
    rw [nextRaw_meaning]
    exact (RecursiveSamplingCapped.step_maxAlphabet_le _ _).trans s.property⟩

theorem next_semantic {M : Nat} (s : BoundedState M) (i : Fin (den s)) :
    semantic (next s i) = RecursiveSamplingCapped.stateStep (semantic s) (semanticTicket s i) := by
  apply Subtype.ext
  exact nextRaw_meaning s i

theorem den_pos {M : Nat} (s : BoundedState M) : 0 < den s := request_pos _

theorem den_width {M B : Nat} (hMB : Nat.clog 2 M ≤ B) (s : BoundedState M) :
    Nat.clog 2 (den s) ≤ B := by
  rw [den_eq]
  exact RecursiveSamplingCapped.state_width hMB (semantic s)

/-- Every public block is consumed exactly as in the source capped run;
finished states continue to ask for singleton padding draws. -/
def capped {M : Nat} (B R : Nat) (hMB : Nat.clog 2 M ≤ B)
    (N : Nat) (s : BoundedState M) (t : CappedSampler.Adaptive.Tape B R N) :
    Option (BoundedState M) :=
  CappedSampler.Adaptive.run den next B R (den_width hMB) N s t

theorem wide_bind_congr {A : Type} {D E B R : Nat} (h : D = E)
    (hD : Nat.clog 2 D ≤ B) (hE : Nat.clog 2 E ≤ B)
    (t : CappedSampler.BitTape B R) (f : Fin D → Option A) (g : Fin E → Option A)
    (hfg : ∀ i, f i = g (Fin.cast h i)) :
    (CappedSampler.runWideBits D B R hD t).bind f =
      (CappedSampler.runWideBits E B R hE t).bind g := by
  subst E
  have he : f = g := funext hfg
  subst g
  rfl

/-- Pointwise, same-tape equality, including exhausted caps and padding
after a finished leaf. This is not only equality of output distributions. -/
theorem capped_semantic {M : Nat} (B R : Nat) (hMB : Nat.clog 2 M ≤ B)
    (N : Nat) (s : BoundedState M) (t : CappedSampler.Adaptive.Tape B R N) :
    (capped B R hMB N s t).map semantic =
      RecursiveSamplingCapped.runState B R hMB N (semantic s) t := by
  induction N generalizing s with
  | zero => rfl
  | succ N ih =>
      change Option.map semantic
          ((CappedSampler.runWideBits (den s) B R (den_width hMB s) t.1).bind
            (fun i => capped B R hMB N (next s i) t.2)) =
        (CappedSampler.runWideBits
          (RecursiveSamplingCapped.stateDenominator (semantic s)) B R
          (RecursiveSamplingCapped.state_width hMB (semantic s)) t.1).bind
            (fun i => RecursiveSamplingCapped.runState B R hMB N
              (RecursiveSamplingCapped.stateStep (semantic s) i) t.2)
      rw [Option.map_bind]
      apply wide_bind_congr (den_eq s)
      intro i
      dsimp only [Function.comp_def]
      rw [ih, next_semantic]
      rfl

#print axioms nextRaw_meaning
#print axioms next_semantic
#print axioms den_width
#print axioms capped_semantic

end Paper2.GeneratorCode
