import CurrentAdditive.CanonicalAmbientWriterFull

/-! Charged four-word preparation followed by exact encoded-instance
framing in one literal ambient program. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open EthInapproximability.CurrentPaper.EncodedCommunication
open CurrentAdditive.FiniteFieldConstructor.CanonicalTable
open Paper2.YaoLookup Paper2.YaoFrame Paper2.HeaderA

def headerFullProgram (t N : ℕ) :=
  BitMachineRawSequence.program (headerPrepProgram t N)
    (headerStage t N) progStart MultiMove.initial progCtl

theorem physical_header_full {v e : ℕ} (t N d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (S : Cell t N → List Bool)
    (hscratch : S (.copyScratch 0) = [])
    (hheader : ∀ k : HB, S (.header k) = [])
    (hrows : S (.dimensions 5) =
      List.replicate (rowCount v (paddedEdgeBits e) t) true)
    (hcols : S (.dimensions 7) =
      List.replicate (columnCount (paddedEdgeBits e) t d) true)
    (hthr : S (.threshold 1) =
      List.replicate (2*paddedEdgeBits e+4*t+2) true)
    (hbits : S (.writer (.inr .output)) =
      (table (paddedEdgeBits e) t d modulus
        (le_paddedEdgeCount e) edges).bits) :
    ∃ steps ≤ CopyFill.fillCost (headerJobs t N) S + 1 +
        (UnaryBinaryEncoding.coefficient *
          (rowCount v (paddedEdgeBits e) t + 1)^2 +
         UnaryBinaryEncoding.coefficient *
          (columnCount (paddedEdgeBits e) t d + 1)^2 +
         UnaryBinaryEncoding.coefficient *
          (2*paddedEdgeBits e+4*t+2+1)^2 +
         (2*(natField (rowCount v (paddedEdgeBits e) t) ++
           natField (columnCount (paddedEdgeBits e) t d) ++
           natField (2*paddedEdgeBits e+4*t+2)).length+2)+3) + 1,
      ((advance (headerFullProgram t N))^[steps])
        (⟨some (BitMachineRawSequence.leftLabel
            (MultiMove.startLabel ((headerJobs t N).map CopyFill.toJob))),
          (MultiMove.initial, progCtl), S⟩ :
            TM2.Cfg (fun _ : Cell t N => Bool) _ _) =
        ⟨none, (MultiMove.initial, progCtl),
          bank (headerEmbed t N) (CopyFill.fill (headerJobs t N) S)
            (fun k => if k = outH then
              encodeInstance
                (instanceOfTable (paddedEdgeBits e) t d modulus
                  (le_paddedEdgeCount e) edges)
              else [])⟩ := by
  let S1 := CopyFill.fill (headerJobs t N) S
  have hblank : ∀ j ∈ headerJobs t N, ∀ dst ∈ j.2, S dst = [] := by
    intro j hj dst hd
    simp [headerJobs] at hj
    rcases hj with (rfl|rfl|rfl|rfl) <;>
      simp only [List.mem_singleton] at hd <;>
      subst dst <;>
      exact hheader _
  have hprep := physical_header_prep_jobs t N S hscratch hblank
  have hlocal := headerPrep_ready t N
    (rowCount v (paddedEdgeBits e) t)
    (columnCount (paddedEdgeBits e) t d)
    (2*paddedEdgeBits e+4*t+2)
    (table (paddedEdgeBits e) t d modulus
      (le_paddedEdgeCount e) edges).bits S
    hheader hrows hcols hthr hbits
  obtain ⟨u, hu, hwrite⟩ := physical_ambient_header
    t N d modulus edges S1 (by intro k; exact hlocal k)
  obtain ⟨steps, hsteps, hrun⟩ := BitMachineRawSequence.runs
    (headerPrepProgram t N) (headerStage t N)
    (MultiMove.startLabel ((headerJobs t N).map CopyFill.toJob))
    progStart MultiMove.initial MultiMove.initial progCtl progCtl
    S S1 _ (CopyFill.fillCost (headerJobs t N) S+1) u
    (by simpa [S1] using hprep)
    (by simpa [S1, stackCfg] using hwrite)
  exact ⟨steps, by omega,
    by simpa [headerFullProgram, S1, stackCfg] using hrun⟩

#print axioms physical_header_full

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
