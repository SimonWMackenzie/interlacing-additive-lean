import CurrentAdditive.V39BudgetSampleBounds
import CurrentAdditive.V39GraphOwnerBounds
import CurrentAdditive.V39SelectorGraph
import CurrentAdditive.V39PhysicalFullSample

set_option autoImplicit false

/-! The literal graph activity, current complete-label law, actual rounded
sample and encoded row-major word in one semantic reduction. No cost/profile,
rank conclusion, success event or entry evaluator is a source hypothesis. -/

namespace CurrentAdditive.V39ActualRandomizedReduction
noncomputable section
open Paper2 V38Schedule V39PublicSchedule V39RecursiveGenerator
open V39BudgetPrintedLaw V39BudgetSampleBounds Workspace.Types.CommComplexity
open EthInapproximability.CurrentPaper
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 16384

variable (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
variable (L r : ℕ) (hq : fullQ₂ L=LiteralEdgeEncoder.Width (fullS L) g.edges.length r)

def activity := V39EdgeSourceFront.edgeActivity g hg
  (by have h:=fullS_ge_256 L; omega) r hq

def matrix (k : ℕ) :
    Row g.vertices (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L) (fullW L) (fullQ L) k →
      Column g.vertices (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L) (fullW L) (fullQ L) k → Bool :=
  V39RecursiveTable.matrix (activity g hg L r hq) k

theorem literal_D (k : ℕ) :
    D (matrix g hg L r hq k)=D (V39GraphOwnerBounds.matrix g hg L r hq k) := by
  exact V39SelectorTransport.graph_D (p:=seedWidth L) (q₁:=fullQ₁ L)
    (w:=fullW L) (Q:=fullQ L) g hg (by have h:=fullS_ge_256 L; omega) r hq k

theorem literal_rank (k : ℕ) :
    (RankLeaves.realMatrix (matrix g hg L r hq k)).rank=
      (RankLeaves.realMatrix (V39GraphOwnerBounds.matrix g hg L r hq k)).rank := by
  exact V39SelectorTransport.graph_rank (p:=seedWidth L) (q₁:=fullQ₁ L)
    (w:=fullW L) (Q:=fullQ L) g hg (by have h:=fullS_ge_256 L; omega) r hq k

theorem upper (k : ℕ) :
    D (matrix g hg L r hq k)≤H L k ∧
    (∀ colour : Fin g.vertices → Fin 3,
      (∀ e, colour (LiteralEdgeEncoder.edge g hg e false)≠colour (LiteralEdgeEncoder.edge g hg e true)) →
      D (matrix g hg L r hq k)≤B L k) := by
  rw [literal_D]
  exact V39GraphOwnerBounds.upper g hg L r hq k

theorem rank_bound (hn : g.vertices≤2^L) (k : ℕ) :
    (RankLeaves.realMatrix (matrix g hg L r hq k)).rank≤rankBound L k := by
  rw [literal_rank]
  exact V39GraphOwnerBounds.rank_bound g hg L r hq hn k

theorem no_bounds (hL : L=Nat.clog 2 g.vertices) (Δ : ℕ) (hΔ : 0<Δ)
    (hdegree : ∀ v, SourceItems.degree (LiteralEdgeEncoder.edge g hg) v≤Δ)
    (γ : ℚ) (hγ : 0<γ) (hnm : g.vertices≤2*g.edges.length)
    (hdeg : 2*g.edges.length≤Δ*g.vertices)
    (hlarge : V39FullCutoff.sourceCutoff γ Δ≤g.vertices)
    (gap : ∀ colour : Fin g.vertices → Fin 3, (γ:ℝ)*g.edges.length≤
      ((Finset.univ.filter (fun e => colour (LiteralEdgeEncoder.edge g hg e false)=
        colour (LiteralEdgeEncoder.edge g hg e true))).card:ℝ)) (k : ℕ) :
    D (matrix g hg L r hq k)=H L k ∧
    V38RestrictionProfiles.TwoThresholdProfile (matrix g hg L r hq k)
      (V39GraphOwnerBounds.rowLaw g L k).toFiniteLaw (V39GraphOwnerBounds.columnLaw g L k).toFiniteLaw
      ((fullRho L:ℚ):ℝ) (H L k:ℤ) := by
  have h:=V39GraphOwnerBounds.no_bounds g hg L r hq hL Δ hΔ hdegree γ hγ hnm hdeg hlarge gap k
  refine ⟨(literal_D g hg L r hq k).trans h.1,?_⟩
  apply (V39SelectorTransport.graph_profile_iff (p:=seedWidth L) (q₁:=fullQ₁ L)
    (w:=fullW L) (Q:=fullQ L) g hg (by have h:=fullS_ge_256 L; omega) r hq k _ _).2
  exact h.2

theorem sampleSide_eq_squareDraws (L k : ℕ) :
    sampleSide L k=V38RankCount.squareDrawsV38 (rankBound L k) (H L k) := by
  unfold sampleSide V38Schedule.pow2Ceil V38RankCount.squareDrawsV38 V38RankCount.leafBitsV38
  congr 2
  ring

theorem rho_le_three_fifths (L : ℕ) (hL : 1≤L) : ((fullRho L:ℚ):ℝ)≤3/5 := by
  have hp: (2:ℝ)≤2^L := by exact_mod_cast (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) hL)
  have hp0: (0:ℝ)<2^L := by positivity
  simp only [fullRho,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat]
  rw [div_le_iff₀ hp0]
  nlinarith

/-- This is exactly the complete encoded word produced from the current
rounded sample, with public YES threshold B and literal physical activity. -/
def word (k N : ℕ)
    (hN : sampleDrawBudget (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L)
      (fullW L) (fullQ L) k (sampleSide L k)≤N)
    (bits : RoundedDraw.BitBlocks
      (V39PhysicalSample.blockLength g.vertices (seedWidth L) (fullQ₂ L) (fullS L) (fullW L) (fullQ L) N) N) : List Bool :=
  printedWord g.vertices (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L) (fullW L) (fullQ L)
    (activity g hg L r hq) (by have h:=fullS_ge_256 L; omega) rfl k (sampleSide L k) (B L k) N hN bits

theorem every_tape_yes (k N : ℕ)
    (hN : sampleDrawBudget (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L)
      (fullW L) (fullQ L) k (sampleSide L k)≤N)
    (colour : Fin g.vertices → Fin 3)
    (proper : ∀ e, colour (LiteralEdgeEncoder.edge g hg e false)≠colour (LiteralEdgeEncoder.edge g hg e true))
    (bits : RoundedDraw.BitBlocks
      (V39PhysicalSample.blockLength g.vertices (seedWidth L) (fullQ₂ L) (fullS L) (fullW L) (fullQ L) N) N) :
    word g hg L r hq k N hN bits ∈ EncodedCommunication.Language := by
  exact printed_yes_membership g.vertices (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L)
    (fullW L) (fullQ L) (activity g hg L r hq) (by have h:=fullS_ge_256 L; omega) rfl
    k (sampleSide L k) N (B L k) (by unfold sampleSide V38Schedule.pow2Ceil; positivity)
    hN ((upper g hg L r hq k).2 colour proper) bits

theorem no_probability (hL : L=Nat.clog 2 g.vertices) (Δ : ℕ) (hΔ : 0<Δ)
    (hdegree : ∀ v, SourceItems.degree (LiteralEdgeEncoder.edge g hg) v≤Δ)
    (γ : ℚ) (hγ : 0<γ) (hnm : g.vertices≤2*g.edges.length)
    (hdeg : 2*g.edges.length≤Δ*g.vertices)
    (hlarge : V39FullCutoff.sourceCutoff γ Δ≤g.vertices)
    (gap : ∀ colour : Fin g.vertices → Fin 3, (γ:ℝ)*g.edges.length≤
      ((Finset.univ.filter (fun e => colour (LiteralEdgeEncoder.edge g hg e false)=
        colour (LiteralEdgeEncoder.edge g hg e true))).card:ℝ)) (k N : ℕ)
    (hN : sampleDrawBudget (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L)
      (fullW L) (fullQ L) k (sampleSide L k)≤N) :
    (49:ℝ)/50≤
      (RoundedDraw.bitBlocksLaw (V39PhysicalSample.blockLength g.vertices (seedWidth L)
        (fullQ₂ L) (fullS L) (fullW L) (fullQ L) N) N).prob
        (fun bits => ExactWordCost (B L k+k) (word g hg L r hq k N hN bits)) := by
  have ht:=V39FullCutoff.fullPublicTests_all_large γ Δ g.vertices g.edges.length hγ hΔ
    (NeZero.pos g.vertices) hnm hdeg hlarge
  rw [←hL] at ht
  have hL1:1≤L := by have hh:=ht.2.2.1; omega
  have hb:=no_bounds g hg L r hq hL Δ hΔ hdegree γ hγ hnm hdeg hlarge gap k
  have hrank:=rank_bound g hg L r hq (by rw [hL]; exact Nat.le_pow_clog (by decide) _) k
  have hrho:=rho_le_three_fifths L hL1
  have hrobust : ∀ U V, (3/5:ℝ)≤(V39GraphOwnerBounds.rowLaw g L k).toFiniteLaw.prob (·∈U) →
      (3/5:ℝ)≤(V39GraphOwnerBounds.columnLaw g L k).toFiniteLaw.prob (·∈V) →
      H L k≤Compression.restrictionD (matrix g hg L r hq k) U V := by
    intro U V hU hV
    have hh:=hb.2 (0:Fin 2) U V (hrho.trans hU) (by simpa using hV)
    simp only [Fin.val_zero,Nat.cast_zero,sub_zero] at hh
    exact_mod_cast hh
  have hH:1≤H L k := by unfold H B seedCost; omega
  have hsamp:=printed_exact_probability g.vertices (seedWidth L) (fullQ₁ L) (fullQ₂ L)
    (fullS L) (fullW L) (fullQ L) (activity g hg L r hq)
    (by have h:=fullS_ge_256 L; omega) rfl k (rankBound L k) (B L k) (H L k) N
    hH hrank hrobust hb.1.le (by simpa only [←sampleSide_eq_squareDraws] using hN)
  simpa only [sampleSide_eq_squareDraws,word] using hsamp

#print axioms literal_D
#print axioms no_bounds
#print axioms every_tape_yes
#print axioms no_probability
end
end CurrentAdditive.V39ActualRandomizedReduction
