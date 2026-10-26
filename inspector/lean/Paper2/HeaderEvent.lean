import Paper2.HeaderWordPoly
import Paper2.EncodedSelectedOutput
import Paper2.FiniteSampling

/-!
# Pointwise and finite-law transport for the physical header run

The output word here is read from the fixed machine's actual output stack
after its verified clock. The probability equality holds for any finite law,
in particular the selected sampler's law once its physical source-front run
has been established. There is no independent postprocessing specification.
-/

noncomputable section

namespace Paper2.HeaderWordRun

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication

def printedAtClock (k : ℕ) (i : Instance) : List Bool :=
  ((machine k).run (clock k i) ((machine k).init (encodeInstance i))).stk
    (machine k).output

theorem printedAtClock_eq (k : ℕ) (i : Instance) (hk : 0 < k) :
    printedAtClock k i = headeredWord k i :=
  (BitMachine.outputsWithin_at_bound (machine k) (machine_outputs k i hk)).2

theorem event_prob_transport {τ : Type*} [Fintype τ]
    (μ : FiniteLaw τ) (f : τ → Instance) (k : ℕ) (hk : 0 < k)
    (E : List Bool → Prop) :
    μ.prob (fun t => E (printedAtClock k (f t))) =
      μ.prob (fun t => E (headeredWord k (f t))) := by
  congr 1
  funext t
  rw [printedAtClock_eq k (f t) hk]

open Paper2.EncodedSelectedOutput Paper2.TotalFiniteConstructorScratch in
theorem machine_outputBits {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (sourceGap headerGap : ℕ)
    (hgap : 0 < headerGap)
    (t : (select hn edge Δ γ sourceGap).Tape) :
    (machine headerGap).OutputsWithin (outputBits hn edge Δ γ sourceGap t)
      (natField (2 * (select hn edge Δ γ sourceGap).budget + headerGap) ++
        AFront.Projection.matrixWord
          (select hn edge Δ γ sourceGap).rows
          (select hn edge Δ γ sourceGap).cols
          ((select hn edge Δ γ sourceGap).table t).bits)
      (clock headerGap (selectedInstance hn edge Δ γ sourceGap t)) := by
  simpa [outputBits, headeredWord, matrix, selectedInstance, instanceOf] using
    machine_outputs headerGap (selectedInstance hn edge Δ γ sourceGap t) hgap

open Paper2.EncodedSelectedOutput Paper2.TotalFiniteConstructorScratch in
theorem selected_event_prob_transport {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (sourceGap headerGap : ℕ)
    (hgap : 0 < headerGap)
    [Fintype (select hn edge Δ γ sourceGap).Tape]
    (μ : FiniteLaw (select hn edge Δ γ sourceGap).Tape)
    (E : List Bool → Prop) :
    μ.prob (fun t => E (printedAtClock headerGap
      (selectedInstance hn edge Δ γ sourceGap t))) =
    μ.prob (fun t => E
      (natField (2 * (select hn edge Δ γ sourceGap).budget + headerGap) ++
        AFront.Projection.matrixWord
          (select hn edge Δ γ sourceGap).rows
          (select hn edge Δ γ sourceGap).cols
          ((select hn edge Δ γ sourceGap).table t).bits)) := by
  simpa [headeredWord, matrix, selectedInstance, instanceOf] using
    event_prob_transport μ
      (selectedInstance hn edge Δ γ sourceGap) headerGap hgap E

#print axioms printedAtClock_eq
#print axioms event_prob_transport
#print axioms machine_outputBits
#print axioms selected_event_prob_transport

end Paper2.HeaderWordRun
