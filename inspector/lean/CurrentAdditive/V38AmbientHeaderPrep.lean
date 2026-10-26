import CurrentAdditive.CanonicalAmbientWriterHeaderFull
import CurrentAdditive.V38AmbientHeaderRun

/-! One fixed four-job physical copy program prepares the final exact
encoded-instance header from row/column/threshold words and table bits. -/

noncomputable section

namespace CurrentAdditive.V38TablePrinter.Ambient

open CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2.HeaderA

def headerJobs (t N : ℕ) : List (Cell t N × List (Cell t N)) :=
  [(.dimensions 5, [.header (fuel 0)]),
   (.dimensions 7, [.header (fuel 1)]),
   (.threshold 1, [.header (fuel 2)]),
   (.writer (.inr .output), [.header outH])]

def headerPrepProgram (t N : ℕ) :=
  MultiMove.program ((headerJobs t N).map CopyFill.toJob) (.copyScratch 0)

theorem headerJobs_good (t N : ℕ) :
    CopyFill.Good (.copyScratch 0) (headerJobs t N) := by
  constructor
  · intro j hj i hi
    simp [headerJobs] at hj hi
    rcases hj with (rfl|rfl|rfl|rfl) <;>
      rcases hi with (rfl|rfl|rfl|rfl) <;>
      simp [fuel, outH]
  · simp [headerJobs, fuel, outH]
  · intro j hj
    simp [headerJobs] at hj
    rcases hj with (rfl|rfl|rfl|rfl) <;> simp
  · intro j hj
    simp [headerJobs] at hj
    rcases hj with (rfl|rfl|rfl|rfl) <;> simp

theorem physical_header_prep_jobs (t N : ℕ) (S : Cell t N → List Bool)
    (hscratch : S (.copyScratch 0) = [])
    (hblank : ∀ j ∈ headerJobs t N, ∀ d ∈ j.2, S d = []) :
    ((advance (headerPrepProgram t N))^[CopyFill.fillCost (headerJobs t N) S + 1])
      (⟨some (MultiMove.startLabel ((headerJobs t N).map CopyFill.toJob)),
        MultiMove.initial, S⟩ :
          TM2.Cfg (fun _ : Cell t N => Bool) _ _) =
      ⟨none, MultiMove.initial, CopyFill.fill (headerJobs t N) S⟩ := by
  exact CopyFill.run (.copyScratch 0) (headerJobs t N) (headerJobs_good t N)
    S hscratch hblank

theorem headerPrep_ready (t N rows cols thr : ℕ)
    (bits : List Bool) (S : Cell t N → List Bool)
    (hheader : ∀ k : HB, S (.header k) = [])
    (hrows : S (.dimensions 5) = List.replicate rows true)
    (hcols : S (.dimensions 7) = List.replicate cols true)
    (hthr : S (.threshold 1) = List.replicate thr true)
    (hbits : S (.writer (.inr .output)) = bits) :
    ∀ k : HB,
      CopyFill.fill (headerJobs t N) S (.header k) =
        Hin rows cols thr bits [] k := by
  intro k
  rcases k with ⟨i, j⟩ | i
  · simp [CopyFill.fill, headerJobs, Hin, fuel, outH, hheader]
  · fin_cases i <;>
      simp [CopyFill.fill, headerJobs, Hin, fuel, outH,
        hrows, hcols, hthr, hbits, hheader]

#print axioms headerJobs_good
#print axioms physical_header_prep_jobs
#print axioms headerPrep_ready

end CurrentAdditive.V38TablePrinter.Ambient
