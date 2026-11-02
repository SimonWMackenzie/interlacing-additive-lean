import CurrentAdditive.V40JointEstimatorLaw

set_option autoImplicit false

/-! Apply the fixed amplified estimator to the exact matrix projection of
the actual reached physical table word. Only ordinary estimator accuracy on
valid sampled tables and its numerical error gap remain as hypotheses. -/

namespace CurrentAdditive.V40PhysicalEstimatorConsumer
noncomputable section
open Paper2 V38Schedule V39PublicSchedule V39RecursiveGenerator
open V39BudgetSampleBounds V39ActualRandomizedReduction
open EthInapproximability.CurrentPaper
open Workspace.Types.CommComplexity
open V39ActualOutputMajority V40RandomPermittedFamily V40JointEstimatorLaw
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 16384

variable (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
variable (L r : ℕ) (hq : fullQ₂ L=LiteralEdgeEncoder.Width (fullS L) g.edges.length r)

abbrev Bits (n L k : ℕ) := RoundedDraw.BitBlocks (V39PhysicalSample.fullPrecision n L k)
  (V39PhysicalSample.fullReservation L k)

def constructionLaw (n L k : ℕ) : FiniteLaw (Bits n L k) :=
  RoundedDraw.bitBlocksLaw (V39PhysicalSample.fullPrecision n L k)
    (V39PhysicalSample.fullReservation L k)

abbrev Reservation (L k : ℕ) :=
  sampleDrawBudget (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L)
    (fullW L) (fullQ L) k (sampleSide L k)≤V39PhysicalSample.fullReservation L k

def table (k : ℕ) (hN : Reservation L k) (bits : Bits g.vertices L k) : Table L k :=
  let z:=V39PhysicalSample.sampleAtBudget g.vertices (seedWidth L) (fullQ₁ L) (fullQ₂ L)
    (fullS L) (fullW L) (fullQ L) (by have h:=fullS_ge_256 L; omega) rfl
    k (sampleSide L k) (V39PhysicalSample.fullReservation L k) hN bits
  fun i j => matrix g hg L r hq k (z.1 i) (z.2 j)

theorem projected_word (k : ℕ) (hN : Reservation L k) (bits : Bits g.vertices L k) :
    AFront.Projection.matrixPart (physicalWord g hg L r hq k hN bits)=
      matrixWord L k (table g hg L r hq k hN bits) := by
  rw [physicalWord_eq,fullWord_literal,AFront.Projection.matrixPart_encodeInstance]
  rfl

theorem exact_cost (k H : ℕ) (hN : Reservation L k) (bits : Bits g.vertices L k) :
    ExactWordCost H (physicalWord g hg L r hq k hN bits) ↔
      D (table g hg L r hq k hN bits)=H := by
  rw [physicalWord_eq]
  exact V39BudgetSampleBounds.exactWordCost_outputWord g.vertices (seedWidth L)
    (fullQ₁ L) (fullQ₂ L) (fullS L) (fullW L) (fullQ L) (activity g hg L r hq)
    k (sampleSide L k) (B L k) H (V40RandomPermittedFamily.side_pos L k) _

def accepts (E : ActualEstimator) (k : ℕ) (hN : Reservation L k)
    (bits : Bits g.vertices L k) (t : Fin (classifierLength E L k) → Bool) : Prop :=
  E.classifier.output (EncodedCommunication.natField (numerator L k) ++
    AFront.Projection.matrixPart (physicalWord g hg L r hq k hN bits)) (List.ofFn t)=[true]

theorem accepts_eq (E : ActualEstimator) (k : ℕ) (hN : Reservation L k)
    (bits : Bits g.vertices L k) (t : Fin (classifierLength E L k) → Bool) :
    accepts g hg L r hq E k hN bits t ↔
      V40JointEstimatorLaw.accepts E L k (table g hg L r hq k hN bits) t := by
  simp only [accepts,projected_word,V40JointEstimatorLaw.accepts,request]

def jointLaw (E : ActualEstimator) (n L k : ℕ) :=
  independentLaw (constructionLaw n L k) E L k

def Accurate (E : ActualEstimator) (L k : ℕ) (u : ℝ) : Prop :=
  ∀ f : Table L k, (2:ℝ)/3≤E.estimator.prob (matrixWord L k f)
    (fun out => |E.value out-(D f:ℝ)|≤u)

theorem yes (E : ActualEstimator) (k : ℕ) (hN : Reservation L k)
    (u : ℝ) (hu : 0≤u) (hgap : 2*u<(k:ℝ))
    (hcompare : ∀ f : Table L k, E.actualComparison (matrixWord L k f) (numerator L k))
    (haccurate : Accurate E L k u)
    (colour : Fin g.vertices → Fin 3)
    (proper : ∀ e, colour (LiteralEdgeEncoder.edge g hg e false)≠colour (LiteralEdgeEncoder.edge g hg e true)) :
    (99:ℝ)/100≤(jointLaw E g.vertices L k).prob
      (fun z => accepts g hg L r hq E k hN z.1 z.2) := by
  simp_rw [accepts_eq]
  apply yes_product (constructionLaw g.vertices L k) E L k
    (table g hg L r hq k hN) u hu hgap
    (fun bits => hcompare _) (fun bits => haccurate _)
  intro bits
  exact V39BudgetSampleBounds.every_tape_upper g.vertices (seedWidth L)
    (fullQ₁ L) (fullQ₂ L) (fullS L) (fullW L) (fullQ L) (activity g hg L r hq)
    (by have h:=fullS_ge_256 L; omega) rfl k (sampleSide L k)
    (V39PhysicalSample.fullReservation L k) (B L k) hN
    ((upper g hg L r hq k).2 colour proper) bits

theorem source_yes (hL : L=Nat.clog 2 g.vertices) (Δ : ℕ) (hΔ : 0<Δ)
    (γ : ℚ) (hγ : 0<γ) (hnm : g.vertices≤2*g.edges.length)
    (hdeg : 2*g.edges.length≤Δ*g.vertices)
    (hlarge : V39FullCutoff.sourceCutoff γ Δ≤g.vertices)
    (E : ActualEstimator) (k : ℕ) (u : ℝ) (hu : 0≤u) (hgap : 2*u<(k:ℝ))
    (hcompare : ∀ f : Table L k, E.actualComparison (matrixWord L k f) (numerator L k))
    (haccurate : Accurate E L k u)
    (colour : Fin g.vertices → Fin 3)
    (proper : ∀ e, colour (LiteralEdgeEncoder.edge g hg e false)≠colour (LiteralEdgeEncoder.edge g hg e true)) :
    (99:ℝ)/100≤(jointLaw E g.vertices L k).prob
      (fun z => accepts g hg L r hq E k
        (source_reservation g L hL Δ hΔ γ hγ hnm hdeg hlarge k) z.1 z.2) :=
  yes g hg L r hq E k _ u hu hgap hcompare haccurate colour proper

theorem source_no (hL : L=Nat.clog 2 g.vertices) (Δ : ℕ) (hΔ : 0<Δ)
    (hdegree : ∀ v, SourceItems.degree (LiteralEdgeEncoder.edge g hg) v≤Δ)
    (γ : ℚ) (hγ : 0<γ) (hnm : g.vertices≤2*g.edges.length)
    (hdeg : 2*g.edges.length≤Δ*g.vertices)
    (hlarge : V39FullCutoff.sourceCutoff γ Δ≤g.vertices)
    (gap : ∀ colour : Fin g.vertices → Fin 3, (γ:ℝ)*g.edges.length≤
      ((Finset.univ.filter (fun e => colour (LiteralEdgeEncoder.edge g hg e false)=
        colour (LiteralEdgeEncoder.edge g hg e true))).card:ℝ))
    (E : ActualEstimator) (k : ℕ) (u : ℝ) (hu : 0≤u) (hgap : 2*u<(k:ℝ))
    (hcompare : ∀ f : Table L k, E.actualComparison (matrixWord L k f) (numerator L k))
    (haccurate : Accurate E L k u) :
    (jointLaw E g.vertices L k).prob
      (fun z => accepts g hg L r hq E k
        (source_reservation g L hL Δ hΔ γ hγ hnm hdeg hlarge k) z.1 z.2)≤(3:ℝ)/100 := by
  let hN:=source_reservation g L hL Δ hΔ γ hγ hnm hdeg hlarge k
  have hp:=physical_source_no_probability g hg L r hq hL Δ hΔ hdegree γ hγ hnm hdeg hlarge gap k
  simp_rw [exact_cost] at hp
  simp_rw [accepts_eq]
  exact no_product (constructionLaw g.vertices L k) E L k
    (table g hg L r hq k hN) u hu hgap
    (fun bits => hcompare _) (fun bits => haccurate _) hp

/-- The permitted raw estimator is unchanged on every valid table, so its
ordinary approximation guarantee transfers to the single uniform extracted E. -/
theorem permitted_accuracy (A : V39PermittedNumericalExtraction.PermittedEstimator)
    (E : ActualEstimator) (hvalue : E.value=A.value)
    (hlaw : ∀ word, V39PermittedNumericalExtraction.ValidTable word →
      ∀ P : List Bool → Prop, E.estimator.prob word P=A.raw.prob word P)
    (k : ℕ) (u : ℝ)
    (ha : ∀ f : Table L k, (2:ℝ)/3≤A.raw.prob (matrixWord L k f)
      (fun out => |A.value out-(D f:ℝ)|≤u)) : Accurate E L k u := by
  intro f
  rw [hvalue,hlaw _ (V40RandomPermittedFamily.valid_table L k f)]
  exact ha f

#print axioms projected_word
#print axioms exact_cost
#print axioms source_yes
#print axioms source_no
#print axioms permitted_accuracy
end
end CurrentAdditive.V40PhysicalEstimatorConsumer
