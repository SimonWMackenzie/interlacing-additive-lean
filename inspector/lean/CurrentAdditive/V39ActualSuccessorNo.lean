import CurrentAdditive.V39RestorationWidth
import CurrentAdditive.V39NumberedProfile
import CurrentAdditive.V39GeneratedRestorationGuards
import CurrentAdditive.V39ActualGeneratedInternal

/-! The seventh actual source restores the current profile on the same
successor whose YES/encoding/count statements are already proved. All
internal-W conclusions are derived from the base profile, actual graph
promise and literal public tests, not assumed as final cost certificates.
-/

namespace CurrentAdditive.V39GeneratedConstruction.SourceData

open Paper2 Paper2.SourceMatrix Workspace.Types.CommComplexity V38Schedule
open CurrentAdditive.V39GeneratedSourceBridge
open CurrentAdditive.V39ActualGeneratedSource
open CurrentAdditive.V39ActualGeneratedInternal

variable {L n m nx ny rep : ℕ}
  [NeZero (generatedQ₁ L)] [NeZero (generatedQ₂ L)] [NeZero (generatedS L)]
  [NeZero (generatedW L)] [NeZero (generatedQ L)]
  {μX : PositiveRationalLaw (Fin nx)} {μY : PositiveRationalLaw (Fin ny)}
  (src : SourceData (D:=8192) (q₁:=generatedQ₁ L) (q₂:=generatedQ₂ L)
    (s:=generatedS L) μX μY)

theorem successor_no_of_tests
    (γ c : ℚ) (Δ : ℕ) (hc : 0 < c) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hn : 0 < n) (hm : 0 < m)
    (htests : GeneratedTests c L m (sourceDeltaV γ Δ n m) (sourceZeta γ))
    (hs : 4 ≤ generatedS L)
    (hwidth : generatedQ₂ L=LiteralEdgeEncoder.Width (generatedS L) m rep)
    (edge : Fin m → Bool → Fin n) (loopless : ∀ e, edge e false ≠ edge e true)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (gap : ∀ colour : Fin n → Fin 3, (γ:ℝ)*m ≤
      ((Finset.univ.filter (fun e => colour (edge e false)=colour (edge e true))).card:ℝ))
    (R : Fin nx → Fin ny → Bool) (d : ℕ) (hd : 2 ≤ d) (hD : D R=d)
    (hp : V38RestrictionProfiles.TwoThresholdProfile R μX.toFiniteLaw μY.toFiniteLaw
      ((generatedRho L:ℚ):ℝ) (d:ℤ))
    (st : src.Streams (w:=generatedW L)
      (μI:=LiteralEdgeEncoder.indexedItemLaw (generatedS L) n hs hn))
    (out : ExactList 8192 (generatedQ L) (Fin (generatedW L) × src.Column)
      (product (uniform (generatedW L)) src.columnLaw)) :
    D (src.successor st out R (activity hs hwidth edge)) =
      d+(12*L+2*quarterCeil L)+1 ∧
    V38RestrictionProfiles.TwoThresholdProfile
      (src.successor st out R (activity hs hwidth edge)) out.law.toFiniteLaw
      (product (uniform (generatedQ L)) (Streams.law src st)).toFiniteLaw
      ((generatedRho L:ℚ):ℝ) ((d+(12*L+2*quarterCeil L)+1:ℕ):ℤ) := by
  have hW := internal_of_tests src γ c Δ hc hγ hΔ hn hm htests hs hwidth
    edge loopless hdegree gap R d hd hD hp st
  have g := V39GeneratedRestorationGuards.guards_of_tests c
    (sourceDeltaV γ Δ n m) (sourceZeta γ) L m hc htests
  let C := sourceCost d L+2*L
  have hC : 3 ≤ C := by dsimp [C,sourceCost]; omega
  have hprofile : V38RestrictionProfiles.TwoThresholdProfile
      (W src st R (activity hs hwidth edge)) (Streams.law src st).toFiniteLaw
      (product (uniform (generatedW L)) src.columnLaw).toFiniteLaw
      (V39GeneratedAlignmentGuards.Theta L) ((C-1:ℕ):ℤ) := by
    convert hW.2.1 using 1 <;> dsimp [C] <;> omega
  have hθpos : 0 < V39GeneratedAlignmentGuards.Theta L := by
    rw [V39GeneratedAlignmentGuards.theta_eq_dyadic]
    exact V39ExceptionBudget.dyadic_pos _
  have hrest := V39TwoThresholdRestoration.restored_width
    (Streams.law src st) (product (uniform (generatedW L)) src.columnLaw)
    (W src st R (activity hs hwidth edge)) (generatedQ L) (6*L) C
    (V39GeneratedAlignmentGuards.Theta L) (V39GeneratedRestorationGuards.Rho L)
    (V39GeneratedRestorationGuards.Delta c L) out.source
    (generatedQ_pow L) hC hW.1 hθpos
    g.phi_pos g.phi_le_one g.delta_pos g.width g.theta_budget hW.2.2 hprofile
  change D (src.successor st out R (activity hs hwidth edge)) = C+6*L ∧
    V38RestrictionProfiles.TwoThresholdProfile
      (src.successor st out R (activity hs hwidth edge)) out.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin (generatedQ L))).prod (Streams.law src st)).toFiniteLaw
      ((generatedRho L:ℚ):ℝ) ((C+6*L:ℕ):ℤ) at hrest
  have hlaw : ((PositiveRationalLaw.uniform (Fin (generatedQ L))).prod
      (Streams.law src st)) = product (uniform (generatedQ L)) (Streams.law src st) := by
    rw [← uniform_eq]
    exact (product_eq _ _).symm
  rw [hlaw] at hrest
  have hsum : C+6*L=d+(12*L+2*quarterCeil L)+1 := by dsimp [C,sourceCost]; omega
  simpa only [hsum] using hrest

end CurrentAdditive.V39GeneratedConstruction.SourceData

#print axioms CurrentAdditive.V39GeneratedConstruction.SourceData.successor_no_of_tests
