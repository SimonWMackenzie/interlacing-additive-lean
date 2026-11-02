import CurrentAdditive.CanonicalAmbientTableRun

/-! The exact encoded-instance header writer embedded in the same ambient
TM2 stack namespace, conditional on its four physically prepared input cells. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open EthInapproximability.CurrentPaper.EncodedCommunication
open CurrentAdditive.FiniteFieldConstructor.CanonicalTable
open Paper2.YaoLookup Paper2.HeaderA Paper2.YaoFrame

def headerStage (t N : ℕ) :=
  fun l => stackStmt (headerEmbed t N) (Paper2.HeaderA.prog l)

theorem physical_ambient_header {v e : ℕ} (t N d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (S : Cell t N → List Bool)
    (hlocal : ∀ k : HB,
      S (.header k) =
        Hin (rowCount v (paddedEdgeBits e) t)
          (columnCount (paddedEdgeBits e) t d)
          (2*paddedEdgeBits e+4*t+2)
          (table (paddedEdgeBits e) t d modulus
            (le_paddedEdgeCount e) edges).bits [] k) :
    ∃ steps ≤ UnaryBinaryEncoding.coefficient *
        (rowCount v (paddedEdgeBits e) t + 1) ^ 2 +
        UnaryBinaryEncoding.coefficient *
        (columnCount (paddedEdgeBits e) t d + 1) ^ 2 +
        UnaryBinaryEncoding.coefficient *
        (2*paddedEdgeBits e+4*t+2+1) ^ 2 +
        (2 * (natField (rowCount v (paddedEdgeBits e) t) ++
          natField (columnCount (paddedEdgeBits e) t d) ++
          natField (2*paddedEdgeBits e+4*t+2)).length + 2) + 3,
      ((advance (headerStage t N))^[steps])
        (⟨some progStart, progCtl, S⟩ :
          TM2.Cfg (fun _ : Cell t N => Bool) _ _) =
        stackCfg (headerEmbed t N) S
          (⟨none, progCtl,
            fun k => if k = outH then
              encodeInstance
                (instanceOfTable (paddedEdgeBits e) t d modulus
                  (le_paddedEdgeCount e) edges)
              else []⟩ : TM2.Cfg (fun _ : HB => Bool) _ _) := by
  obtain ⟨steps, hsteps, hrun⟩ := canonical_header_run t d modulus edges
  refine ⟨steps, hsteps, ?_⟩
  have hbank := bank_eq_self (headerEmbed t N) S _
    (by intro k; exact (hlocal k).symm)
  have he := EthInapproximability.CurrentPaper.BitMachineStackRun.run
    (headerEmbed t N) S Paper2.HeaderA.prog
    (⟨some progStart, progCtl,
      Hin (rowCount v (paddedEdgeBits e) t)
        (columnCount (paddedEdgeBits e) t d)
        (2*paddedEdgeBits e+4*t+2)
        (table (paddedEdgeBits e) t d modulus
          (le_paddedEdgeCount e) edges).bits []⟩ :
            TM2.Cfg (fun _ : HB => Bool) _ _) steps
  have hr := congrArg (stackCfg (headerEmbed t N) S) hrun
  have hcombined := he.trans hr
  simpa [headerStage, stackCfg, hbank] using hcombined

#print axioms physical_ambient_header

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
