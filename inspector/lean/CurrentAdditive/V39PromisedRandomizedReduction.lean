import CurrentAdditive.V39ActualRandomizedReduction
import CurrentAdditive.V39IterationArithmetic

set_option autoImplicit false

/-! The source promise supplies the exact full reservation. The same
literal current printed word has an every-tape YES upper bound and the
high-probability NO exact cost; no rank, profile, draw cap or event is assumed. -/

namespace CurrentAdditive.V39ActualRandomizedReduction
noncomputable section
open Paper2 V38Schedule V39PublicSchedule V39RecursiveGenerator V39BudgetSampleBounds
open EthInapproximability.CurrentPaper
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 16384

variable (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
variable (L r : ℕ) (hq : fullQ₂ L=LiteralEdgeEncoder.Width (fullS L) g.edges.length r)

theorem source_reservation (hL : L=Nat.clog 2 g.vertices) (Δ : ℕ) (hΔ : 0<Δ)
    (γ : ℚ) (hγ : 0<γ) (hnm : g.vertices≤2*g.edges.length)
    (hdeg : 2*g.edges.length≤Δ*g.vertices)
    (hlarge : V39FullCutoff.sourceCutoff γ Δ≤g.vertices) (k : ℕ) :
    sampleDrawBudget (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L)
      (fullW L) (fullQ L) k (sampleSide L k)≤V39PhysicalSample.fullReservation L k := by
  have ht:=V39FullCutoff.fullPublicTests_all_large γ Δ g.vertices g.edges.length hγ hΔ
    (NeZero.pos g.vertices) hnm hdeg hlarge
  rw [←hL] at ht
  exact V39PhysicalSample.full_draws_le (fullConstant γ Δ g.vertices g.edges.length)
    L g.edges.length k (sourceDeltaV γ Δ g.vertices g.edges.length) (sourceZeta γ) ht

def fullWord (k : ℕ)
    (hN : sampleDrawBudget (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L)
      (fullW L) (fullQ L) k (sampleSide L k)≤V39PhysicalSample.fullReservation L k)
    (bits : RoundedDraw.BitBlocks (V39PhysicalSample.fullPrecision g.vertices L k)
      (V39PhysicalSample.fullReservation L k)) : List Bool :=
  word g hg L r hq k (V39PhysicalSample.fullReservation L k) hN bits

theorem fullWord_literal (k : ℕ)
    (hN : sampleDrawBudget (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L)
      (fullW L) (fullQ L) k (sampleSide L k)≤V39PhysicalSample.fullReservation L k)
    (bits : RoundedDraw.BitBlocks (V39PhysicalSample.fullPrecision g.vertices L k)
      (V39PhysicalSample.fullReservation L k)) :
    let z:=V39PhysicalSample.sampleAtBudget g.vertices (seedWidth L) (fullQ₁ L) (fullQ₂ L)
      (fullS L) (fullW L) (fullQ L) (by have h:=fullS_ge_256 L; omega) rfl
      k (sampleSide L k) (V39PhysicalSample.fullReservation L k) hN bits
    fullWord g hg L r hq k hN bits=EncodedCommunication.encodeInstance
      ⟨sampleSide L k,sampleSide L k,B L k,
        MatrixMaterialization.rowMajor (fun i j => matrix g hg L r hq k (z.1 i) (z.2 j))⟩ := by
  intro z
  exact V39BudgetSampleBounds.outputWord_rowMajor g.vertices (seedWidth L) (fullQ₁ L) (fullQ₂ L)
    (fullS L) (fullW L) (fullQ L) (activity g hg L r hq) k (sampleSide L k) (B L k) z

theorem source_every_tape_yes (hL : L=Nat.clog 2 g.vertices) (Δ : ℕ) (hΔ : 0<Δ)
    (γ : ℚ) (hγ : 0<γ) (hnm : g.vertices≤2*g.edges.length)
    (hdeg : 2*g.edges.length≤Δ*g.vertices)
    (hlarge : V39FullCutoff.sourceCutoff γ Δ≤g.vertices) (k : ℕ)
    (colour : Fin g.vertices → Fin 3)
    (proper : ∀ e, colour (LiteralEdgeEncoder.edge g hg e false)≠colour (LiteralEdgeEncoder.edge g hg e true))
    (bits : RoundedDraw.BitBlocks (V39PhysicalSample.fullPrecision g.vertices L k)
      (V39PhysicalSample.fullReservation L k)) :
    fullWord g hg L r hq k (source_reservation g L hL Δ hΔ γ hγ hnm hdeg hlarge k) bits
      ∈EncodedCommunication.Language := by
  exact every_tape_yes g hg L r hq k (V39PhysicalSample.fullReservation L k)
    (source_reservation g L hL Δ hΔ γ hγ hnm hdeg hlarge k) colour proper bits

theorem source_no_probability (hL : L=Nat.clog 2 g.vertices) (Δ : ℕ) (hΔ : 0<Δ)
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
          (fullWord g hg L r hq k (source_reservation g L hL Δ hΔ γ hγ hnm hdeg hlarge k) bits)) := by
  exact no_probability g hg L r hq hL Δ hΔ hdegree γ hγ hnm hdeg hlarge gap
    k (V39PhysicalSample.fullReservation L k)
    (source_reservation g L hL Δ hΔ γ hγ hnm hdeg hlarge k)

theorem square_power_of_two (L k : ℕ) :
    ∃ z, sampleSide L k=2^z ∧ sampleEntries L k=2^(2*z) := by
  obtain ⟨z,hm,hT,_⟩:=sample_square_dyadic L k
  exact ⟨z,hm,hT⟩

#print axioms source_reservation
#print axioms fullWord_literal
#print axioms source_every_tape_yes
#print axioms source_no_probability
end
end CurrentAdditive.V39ActualRandomizedReduction
