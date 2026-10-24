import CurrentAdditive.CanonicalAmbientFieldFull

/-! One fixed four-job physical copy program prepares the public row/column
factor cells. A fifth fixed unary writer supplies q = 2^(t-1). -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2.YaoMachine

def dimensionJobs (t : ℕ) : List (Cell t 16 × List (Cell t 16)) :=
  [(.source (sN 3), [.dimensions 0]),
   (.selector 1, [.dimensions 1]),
   (.source (sN 6), [.dimensions 2]),
   (.square 3, [.dimensions 3])]

def dimensionCopyProgram (t : ℕ) :=
  MultiMove.program ((dimensionJobs t).map CopyFill.toJob) (.copyScratch 0)

def dimensionPrepProgram (t : ℕ) :=
  BitMachineRawSequence.program (dimensionCopyProgram t)
    (SourceClauseFixedUnary.program (.dimensions 4 : Cell t 16) (2^(t-1)))
    (0 : SourceClauseFixedUnary.Label (2^(t-1)))
    MultiMove.initial ()

theorem dimensionJobs_good (t : ℕ) :
    CopyFill.Good (.copyScratch 0) (dimensionJobs t) := by
  constructor
  · intro j hj i hi
    simp [dimensionJobs] at hj hi
    rcases hj with (rfl|rfl|rfl|rfl) <;>
      rcases hi with (rfl|rfl|rfl|rfl) <;> simp
  · simp [dimensionJobs]
  · intro j hj
    simp [dimensionJobs] at hj
    rcases hj with (rfl|rfl|rfl|rfl) <;> simp
  · intro j hj
    simp [dimensionJobs] at hj
    rcases hj with (rfl|rfl|rfl|rfl) <;> simp

theorem dimensionCopy_local (t v cap H R2 : ℕ)
    (S : Cell t 16 → List Bool)
    (hblank : ∀ i : Fin 11, S (.dimensions i) = [])
    (hv : S (.source (sN 3)) = List.replicate v true)
    (hcap : S (.selector 1) = List.replicate cap true)
    (hH : S (.source (sN 6)) = List.replicate H true)
    (hR2 : S (.square 3) = List.replicate R2 true) :
    ∀ i : Fin 11,
      CopyFill.fill (dimensionJobs t) S (.dimensions i) =
        if i = 0 then List.replicate v true
        else if i = 1 then List.replicate cap true
        else if i = 2 then List.replicate H true
        else if i = 3 then List.replicate R2 true else [] := by
  intro i
  fin_cases i <;>
    simp_all [CopyFill.fill, dimensionJobs]

theorem physical_dimension_prep (t v cap H R2 : ℕ)
    (S : Cell t 16 → List Bool)
    (hblank : ∀ i : Fin 11, S (.dimensions i) = [])
    (hscratch : S (.copyScratch 0) = [])
    (hv : S (.source (sN 3)) = List.replicate v true)
    (hcap : S (.selector 1) = List.replicate cap true)
    (hH : S (.source (sN 6)) = List.replicate H true)
    (hR2 : S (.square 3) = List.replicate R2 true) :
    ∃ steps ≤ CopyFill.fillCost (dimensionJobs t) S + 1 +
        (2^(t-1)+1) + 1,
      ((advance (dimensionPrepProgram t))^[steps])
        (⟨some (BitMachineRawSequence.leftLabel
            (MultiMove.startLabel ((dimensionJobs t).map CopyFill.toJob))),
          (MultiMove.initial, ()), S⟩ :
            TM2.Cfg (fun _ : Cell t 16 => Bool) _ _) =
        ⟨none, (MultiMove.initial, ()),
          Function.update (CopyFill.fill (dimensionJobs t) S)
            (.dimensions 4) (List.replicate (2^(t-1)) true)⟩ := by
  let S1 := CopyFill.fill (dimensionJobs t) S
  have hblankJobs : ∀ j ∈ dimensionJobs t, ∀ dst ∈ j.2, S dst = [] := by
    intro j hj dst hd
    simp [dimensionJobs] at hj
    rcases hj with (rfl|rfl|rfl|rfl) <;>
      simp_all [hblank]
  have hcopy := CopyFill.run (.copyScratch 0) (dimensionJobs t)
    (dimensionJobs_good t) S hscratch hblankJobs
  have h4 : S1 (.dimensions 4) = [] := by
    simpa [S1] using dimensionCopy_local t v cap H R2 S
      hblank hv hcap hH hR2 4
  have hfixed := SourceClauseFixedUnary.run
    (.dimensions 4 : Cell t 16) S1 (2^(t-1)) h4
  obtain ⟨steps, hsteps, hrun⟩ := BitMachineRawSequence.runs
    (dimensionCopyProgram t)
    (SourceClauseFixedUnary.program (.dimensions 4 : Cell t 16) (2^(t-1)))
    (MultiMove.startLabel ((dimensionJobs t).map CopyFill.toJob))
    (0 : SourceClauseFixedUnary.Label (2^(t-1)))
    MultiMove.initial MultiMove.initial () ()
    S S1 _ (CopyFill.fillCost (dimensionJobs t) S + 1)
    (2^(t-1)+1)
    (by simpa [dimensionCopyProgram, S1] using hcopy) hfixed
  exact ⟨steps, by omega,
    by simpa [dimensionPrepProgram, S1] using hrun⟩

#print axioms dimensionJobs_good
#print axioms dimensionCopy_local
#print axioms physical_dimension_prep

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
