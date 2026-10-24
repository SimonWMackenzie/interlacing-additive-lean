import CurrentAdditive.RoundedCodeBudget

namespace EthInapproximability.CurrentPaper.RoundedCodeLoop

open Paper2.GeneratorCode Paper2.GeneratorPositive Paper2.GeneratorStateSize
open Paper2.RecursiveSamplingProgram Paper2.RecursiveSamplingCapped
open CurrentAdditive.RoundedDraw
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

def tapeWord (b : ℕ) : (N : ℕ) → BitBlocks b N → List Bool
  | 0, _ => []
  | N+1, bits => Paper2.CappedTicketMachine.ticketWord bits.1 ++ tapeWord b N bits.2

/-- Deterministic source execution stops at the first leaf and records all
reserved but unused tape bits. At zero fuel it only normalizes the syntax.
The physical theorem separately proves that sufficient fuel reaches a leaf. -/
def execute (b : ℕ) : (N : ℕ) → Paper2.GeneratorCode.State → BitBlocks b N →
    Paper2.GeneratorCode.State × List Bool
  | 0, s, _ => (Paper2.GeneratorCode.normalize s, [])
  | N+1, s, bits =>
      if (Paper2.GeneratorCode.normalize s).todo = [] then
        (Paper2.GeneratorCode.normalize s, tapeWord b (N+1) bits)
      else execute b N (roundedNext s b bits.1) bits.2

def programRun (b N : ℕ) (p : Program (List Bool)) (bits : BitBlocks b N) :
    Program (List Bool) :=
  runBitsRounded denominator step b denominator_pos N p bits

theorem programRun_pure (b N : ℕ) (out : List Bool) (bits : BitBlocks b N) :
    programRun b N (.pure out) bits = .pure out := by
  induction N with
  | zero => rfl
  | succ N ih => exact ih bits.2

theorem roundedNext_meaning (s : Paper2.GeneratorCode.State) (b : ℕ)
    (bits : Fin b → Bool) :
    stateMeaning (roundedNext s b bits) =
      step (stateMeaning s)
        (draw (denominator (stateMeaning s)) (2 ^ b) (denominator_pos _) (by positivity)
          (Paper2.CappedSampler.bitsTicketEquiv b bits)) := by
  have hd : denominator (stateMeaning s) = request (Paper2.GeneratorCode.normalize s) := by
    rw [← normalize_meaning s, ready_request _ (normalize_ready s)]
  exact (ready_step _ (normalize_ready s) (roundedTicket s b bits)).trans
    (program_step_congr (normalize_meaning s) _ _ (by
      simp [roundedTicket, draw, hd]))

theorem execute_meaning (b N : ℕ) (s : Paper2.GeneratorCode.State) (bits : BitBlocks b N) :
    stateMeaning (execute b N s bits).1 = programRun b N (stateMeaning s) bits := by
  induction N generalizing s with
  | zero => exact normalize_meaning s
  | succ N ih =>
      by_cases hd : (Paper2.GeneratorCode.normalize s).todo = []
      · have hpure : stateMeaning s = .pure (Paper2.GeneratorCode.normalize s).output := by
          rw [← normalize_meaning s]
          simp [stateMeaning, hd, stackMeaning]
        simp only [execute, hd, ↓reduceIte, Prod.fst]
        rw [normalize_meaning, hpure, programRun_pure]
      · simp only [execute, hd, ↓reduceIte]
        rw [ih, roundedNext_meaning]
        rfl

theorem next_draws_le (s : Paper2.GeneratorCode.State) (b : ℕ) (bits : Fin b → Bool) :
    (stateMeaning (roundedNext s b bits)).maxDraws ≤ (stateMeaning s).maxDraws - 1 := by
  rw [roundedNext_meaning]
  exact step_maxDraws_le _ _

theorem roundedNext_positive (s : Paper2.GeneratorCode.State) (hp : PositiveState s)
    (b : ℕ) (bits : Fin b → Bool) : PositiveState (roundedNext s b bits) :=
  advance_positive _ (normalize_positive s hp) (normalize_ready s) (roundedTicket s b bits)

theorem roundedNext_trace (root : Code) (s : Paper2.GeneratorCode.State) (ht : Trace root s)
    (b : ℕ) (bits : Fin b → Bool) : Trace root (roundedNext s b bits) :=
  Trace.accepted (trace_normalize root s ht) (normalize_ready s) (roundedTicket s b bits)

theorem no_draws_done (s : Paper2.GeneratorCode.State) (hp : PositiveState s)
    (hzero : (stateMeaning s).maxDraws = 0) :
    (Paper2.GeneratorCode.normalize s).todo = [] := by
  by_contra hne
  obtain ⟨c, cs, hc, hdraw⟩ := ready_positive_draw _ (normalize_positive s hp)
    (normalize_ready s) hne
  have hz : (stateMeaning (Paper2.GeneratorCode.normalize s)).maxDraws = 0 := by
    rw [normalize_meaning, hzero]
  unfold stateMeaning at hz
  rw [hc] at hz
  cases c with
  | emit word => simp [DrawHead] at hdraw
  | append left right => simp [DrawHead] at hdraw
  | ticket a =>
      cases a with
      | zero => simp [DrawHead] at hdraw
      | succ a =>
          simp only [stackMeaning, meaning, concat, Program.uniform, Program.map_draw,
            Program.bind_draw, Program.maxDraws_draw] at hz
          omega
  | bit =>
      simp only [stackMeaning, meaning, concat, Paper2.RecursiveSamplingSeed.bit,
        Program.uniform, Program.map_draw, Program.bind_draw, Program.maxDraws_draw] at hz
      omega
  | branch3 a cut₁ cut₂ first second third =>
      cases a with
      | zero => simp [DrawHead] at hdraw
      | succ a =>
          simp only [stackMeaning, meaning, concat, Program.map_draw,
            Program.bind_draw, Program.maxDraws_draw] at hz
          omega

theorem execute_done (b N : ℕ) (s : Paper2.GeneratorCode.State) (hp : PositiveState s)
    (hN : (stateMeaning s).maxDraws ≤ N) (bits : BitBlocks b N) :
    (execute b N s bits).1.todo = [] := by
  induction N generalizing s with
  | zero => exact no_draws_done s hp (by omega)
  | succ N ih =>
      by_cases hd : (Paper2.GeneratorCode.normalize s).todo = []
      · simpa only [execute, hd, ↓reduceIte] using hd
      · simp only [execute, hd, ↓reduceIte]
        apply ih _ (roundedNext_positive s hp b bits.1) _ bits.2
        have hnext := next_draws_le s b bits.1
        omega

#print axioms execute_meaning
#print axioms execute_done

end
end EthInapproximability.CurrentPaper.RoundedCodeLoop
