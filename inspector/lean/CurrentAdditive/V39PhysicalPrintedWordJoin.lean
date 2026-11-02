import CurrentAdditive.V39PromisedRandomizedReduction
import CurrentAdditive.V39WEncodedTransport

set_option autoImplicit false

/-! The probability event is the output word of the actual fixed table/
header controller, at the exact labels emitted by the physical sampler.
The raw sampler-to-writer source-bank copy is owned separately. -/

namespace CurrentAdditive.V39ActualRandomizedReduction
noncomputable section
open Paper2 Turing V38Schedule V39PublicSchedule V39RecursiveGenerator
open EthInapproximability.CurrentPaper
open BitMachineEncoding
open V39WEntry
local instance : DecidableEq V39WEncodedTable.Stack := Classical.decEq _
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 16384

variable (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
variable (L r : ℕ) (hq : fullQ₂ L=LiteralEdgeEncoder.Width (fullS L) g.edges.length r)

theorem physical_same_word (k : ℕ)
    (ξ : RecursiveEntries.Tails (Fin (seedWidth L) → Bool) (Fin (seedWidth L))
      (SourceConstruction.Items (fullS L) (Fin g.vertices))
      (fullS L) (fullQ₁ L) (fullQ₂ L) (fullW L) (fullQ L))
    (hN : sampleDrawBudget (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L)
      (fullW L) (fullQ L) k (sampleSide L k)≤V39PhysicalSample.fullReservation L k)
    (bits : RoundedDraw.BitBlocks (V39PhysicalSample.fullPrecision g.vertices L k)
      (V39PhysicalSample.fullReservation L k)) :
    let m:=sampleSide L k
    let z:=V39PhysicalSample.sampleAtBudget g.vertices (seedWidth L) (fullQ₁ L) (fullQ₂ L)
      (fullS L) (fullW L) (fullQ L) (by have h:=fullS_ge_256 L; omega) rfl
      k m (V39PhysicalSample.fullReservation L k) hN bits
    let S:=V39WTablePrepare.sourceWords g r k m z.1 z.2
    let f:Fin m → Fin m → Bool:=fun i j => matrix g hg L r hq k (z.1 i) (z.2 j)
    let WB:=(MatrixTableWriter.ready (bankW g r k m m z.1 z.2) m m 0 0 0 0 []
      (MatrixMaterialization.rowMajor f)).contents
    ∃ t≤V39WTablePrepare.clock S+
        MatrixTableWriter.writerBound m m (Tent g hg (by have h:=fullS_ge_256 L; omega)
          r hq ξ k m m z.1 z.2)+V39WHeaderExact.clock m m (B L k)+2, ∃ v,
      ((advance V39WEncodedTable.program)^[t])
        (⟨some V39WEncodedTable.start,V39WEncodedTable.control,V39WEncodedTable.initial S (B L k)⟩:
          TM2.Cfg (fun _ : V39WEncodedTable.Stack => Bool) _ _)=
        ⟨none,v,V39WEncodedTable.final S WB m m (B L k) (MatrixMaterialization.rowMajor f)⟩ ∧
      V39WEncodedTable.final S WB m m (B L k) (MatrixMaterialization.rowMajor f)
        V39WEncodedTable.outputPort=fullWord g hg L r hq k hN bits := by
  intro m z S f WB
  obtain ⟨t,ht,v,hr⟩:=V39WEncodedTable.physical_encoded g hg
    (NeZero.pos (seedWidth L)) (by have h:=fullS_ge_256 L; omega) r hq ξ k m (B L k) z.1 z.2
  refine ⟨t,ht,v,hr,?_⟩
  rw [V39WEncodedTable.final_word]
  exact (fullWord_literal g hg L r hq k hN bits).symm

#print axioms physical_same_word
end
end CurrentAdditive.V39ActualRandomizedReduction
