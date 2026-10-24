import CurrentAdditive.V39PhysicalPrintedWordJoin

set_option autoImplicit false

/-! YES/NO events of the exact reached output bank of the fixed physical
table/header controller. Its input source words are built from the actual
physical sampler's label pair; raw-bank routing is a separate physical join. -/

namespace CurrentAdditive.V39ActualRandomizedReduction
noncomputable section
open Paper2 V38Schedule V39PublicSchedule V39RecursiveGenerator V39BudgetSampleBounds
open EthInapproximability.CurrentPaper V39WEntry
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 16384

variable (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
variable (L r : ℕ) (hq : fullQ₂ L=LiteralEdgeEncoder.Width (fullS L) g.edges.length r)

def physicalFinalBank (k : ℕ)
    (hN : sampleDrawBudget (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L)
      (fullW L) (fullQ L) k (sampleSide L k)≤V39PhysicalSample.fullReservation L k)
    (bits : RoundedDraw.BitBlocks (V39PhysicalSample.fullPrecision g.vertices L k)
      (V39PhysicalSample.fullReservation L k)) : V39WEncodedTable.Stack → List Bool :=
  let m:=sampleSide L k
  let z:=V39PhysicalSample.sampleAtBudget g.vertices (seedWidth L) (fullQ₁ L) (fullQ₂ L)
    (fullS L) (fullW L) (fullQ L) (by have h:=fullS_ge_256 L; omega) rfl
    k m (V39PhysicalSample.fullReservation L k) hN bits
  let S:=V39WTablePrepare.sourceWords g r k m z.1 z.2
  let f:Fin m → Fin m → Bool:=fun i j => matrix g hg L r hq k (z.1 i) (z.2 j)
  let WB:=(MatrixTableWriter.ready (bankW g r k m m z.1 z.2) m m 0 0 0 0 []
    (MatrixMaterialization.rowMajor f)).contents
  V39WEncodedTable.final S WB m m (B L k) (MatrixMaterialization.rowMajor f)

def physicalWord (k : ℕ)
    (hN : sampleDrawBudget (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L)
      (fullW L) (fullQ L) k (sampleSide L k)≤V39PhysicalSample.fullReservation L k)
    (bits : RoundedDraw.BitBlocks (V39PhysicalSample.fullPrecision g.vertices L k)
      (V39PhysicalSample.fullReservation L k)) : List Bool :=
  physicalFinalBank g hg L r hq k hN bits V39WEncodedTable.outputPort

theorem physicalWord_eq (k : ℕ)
    (hN : sampleDrawBudget (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L)
      (fullW L) (fullQ L) k (sampleSide L k)≤V39PhysicalSample.fullReservation L k)
    (bits : RoundedDraw.BitBlocks (V39PhysicalSample.fullPrecision g.vertices L k)
      (V39PhysicalSample.fullReservation L k)) :
    physicalWord g hg L r hq k hN bits=fullWord g hg L r hq k hN bits := by
  unfold physicalWord physicalFinalBank
  rw [V39WEncodedTable.final_word]
  exact (fullWord_literal g hg L r hq k hN bits).symm

theorem physical_source_every_tape_yes (hL : L=Nat.clog 2 g.vertices) (Δ : ℕ) (hΔ : 0<Δ)
    (γ : ℚ) (hγ : 0<γ) (hnm : g.vertices≤2*g.edges.length)
    (hdeg : 2*g.edges.length≤Δ*g.vertices)
    (hlarge : V39FullCutoff.sourceCutoff γ Δ≤g.vertices) (k : ℕ)
    (colour : Fin g.vertices → Fin 3)
    (proper : ∀ e, colour (LiteralEdgeEncoder.edge g hg e false)≠colour (LiteralEdgeEncoder.edge g hg e true))
    (bits : RoundedDraw.BitBlocks (V39PhysicalSample.fullPrecision g.vertices L k)
      (V39PhysicalSample.fullReservation L k)) :
    physicalWord g hg L r hq k (source_reservation g L hL Δ hΔ γ hγ hnm hdeg hlarge k) bits
      ∈EncodedCommunication.Language := by
  rw [physicalWord_eq]
  exact source_every_tape_yes g hg L r hq hL Δ hΔ γ hγ hnm hdeg hlarge k colour proper bits

theorem physical_source_no_probability (hL : L=Nat.clog 2 g.vertices) (Δ : ℕ) (hΔ : 0<Δ)
    (hdegree : ∀ v, SourceItems.degree (LiteralEdgeEncoder.edge g hg) v≤Δ)
    (γ : ℚ) (hγ : 0<γ) (hnm : g.vertices≤2*g.edges.length)
    (hdeg : 2*g.edges.length≤Δ*g.vertices)
    (hlarge : V39FullCutoff.sourceCutoff γ Δ≤g.vertices)
    (gap : ∀ colour : Fin g.vertices → Fin 3, (γ:ℝ)*g.edges.length≤
      ((Finset.univ.filter (fun e => colour (LiteralEdgeEncoder.edge g hg e false)=
        colour (LiteralEdgeEncoder.edge g hg e true))).card:ℝ)) (k : ℕ) :
    (49:ℝ)/50≤
      (RoundedDraw.bitBlocksLaw (V39PhysicalSample.fullPrecision g.vertices L k)
        (V39PhysicalSample.fullReservation L k)).prob
        (fun bits => ExactWordCost (B L k+k)
          (physicalWord g hg L r hq k (source_reservation g L hL Δ hΔ γ hγ hnm hdeg hlarge k) bits)) := by
  simp_rw [physicalWord_eq]
  exact source_no_probability g hg L r hq hL Δ hΔ hdegree γ hγ hnm hdeg hlarge gap k

#print axioms physicalFinalBank
#print axioms physicalWord_eq
#print axioms physical_source_every_tape_yes
#print axioms physical_source_no_probability
end
end CurrentAdditive.V39ActualRandomizedReduction
