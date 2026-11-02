import Paper2.HeaderWordRun
import Paper2.A4PolyIn

/-!
# Polynomial charge of the physical fixed-gap header machine

The clock here is the exact charge from `HeaderWordRun.machine_outputs`.
Intermediate word sizes are charged through the finite machines' verified
output-length theorem, so the bound does not rely on a semantic output-size
guess or on a source-front assembly premise.
-/

noncomputable section

namespace Paper2.HeaderWordRun

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open Paper2.Unit4Shell.Poly

private def size (i : Instance) : ℕ := (encodeInstance i).length

private theorem outputPoly (M : BitMachine.Machine)
    {a b : Instance → List Bool} {T : Instance → ℕ}
    (ha : PolyIn size (fun i => (a i).length))
    (hT : PolyIn size T)
    (hrun : ∀ i, M.OutputsWithin (a i) (b i) (T i)) :
    PolyIn size (fun i => (b i).length) :=
  mono (fun i => BitMachine.output_length_bound M (hrun i))
    (add ha (mul hT (const M.pushBound)))

theorem clock_poly (k : ℕ) : PolyIn size (clock k) := by
  have hin : PolyIn size (fun i => (encodeInstance i).length) := self
  have ht1 : PolyIn size splitClock := by
    simpa [splitClock] using
      (mul (const (sz := size) 3) (add self (const 1)))
  have hmid1 : PolyIn size (fun i => (splitWord i).length) :=
    outputPoly AFront.Split.splitMachine hin ht1 splitRun
  have ht2 : PolyIn size swapClock := by
    simpa [swapClock] using
      (mul (const (sz := size) 3) (add hmid1 (const 1)))
  have hmid2 : PolyIn size (fun i => (swappedWord i).length) :=
    outputPoly Paper2.Unit4Shell.KofLoops.Swap.machine hmid1 ht2 swapRun
  have hbits : PolyIn size (fun i => i.threshold.bits.length) :=
    mono (fun i => by
      dsimp [size]
      rw [EncodedCommunication.encodeInstance_length]
      omega) self
  have hheaderTime : PolyIn size
      (fun i => headerC k * (i.threshold.bits.length + 1) ^ headerD k) := by
    exact mul (const _) (pow (add hbits (const 1)) (headerD k))
  have hheaderLength : PolyIn size
      (fun i => (FixedGapHeader.bitsHeader k i.threshold.bits).length) :=
    outputPoly (headerMachine k) hbits hheaderTime
      (fun i => headerRun k i.threshold.bits)
  have ht3 : PolyIn size (mapClock k) := by
    simpa [mapClock] using
      (add (add (add
        (mul (const (sz := size) 2) hbits) hheaderTime)
        (mul (const 2) hheaderLength)) (const 6))
  have hmid3 : PolyIn size (fun i => (mappedWord k i).length) :=
    outputPoly (Paper2.Unit4Shell.PairMap.machine (headerMachine k))
      hmid2 ht3 (mapRun k)
  have ht4 : PolyIn size (concatClock k) := by
    simpa [concatClock] using
      (mul (const (sz := size) 3) (add hmid3 (const 1)))
  simpa [clock] using
    (add (add (add ht1 (mul (const (sz := size) 2) hmid1)) (const 2))
      (add (add (add ht2 (mul (const 2) hmid2)) (const 2))
        (add (add (add ht3 (mul (const 2) hmid3)) (const 2)) ht4)))

theorem machine_outputs_polynomial (k : ℕ) :
    ∃ C D : ℕ, ∀ i : Instance, 0 < k →
      (machine k).OutputsWithin (encodeInstance i) (headeredWord k i)
        (C * ((encodeInstance i).length + 1) ^ D) := by
  obtain ⟨C, D, hclock⟩ := clock_poly k
  refine ⟨C, D, ?_⟩
  intro i hk
  exact BitMachine.outputsWithin_mono _ (machine_outputs k i hk) (hclock i)

#print axioms clock_poly
#print axioms machine_outputs_polynomial

end Paper2.HeaderWordRun
