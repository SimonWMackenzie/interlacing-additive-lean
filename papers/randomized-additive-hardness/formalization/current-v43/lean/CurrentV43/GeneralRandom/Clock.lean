import CurrentV43.GeneralRandom.Algorithm
import CurrentV43.ResourceTotal

set_option autoImplicit false

namespace CurrentV43.GeneralRandom
noncomputable section
open CurrentAdditive Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition Unit4Shell.T10Finite
open ParametricSource TimeTradeoff
open CurrentAdditive.V42RandomizedETHEndpoint
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 32768
variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- Every charge is paid: the router, gap printer, physical carrier,
all fair bits, table construction, estimation and midpoint comparison. -/
theorem algorithm_clock (C0 : Nat) (hC0 : sourceConstant D ≤ C0)
    (C : SelectedTape.Algorithm) (G : Schedule) (cs cutoff : Nat)
    (hcut : 1 ≤ cutoff) (hsource : V42SourceGeometry.originalCutoff D B (cs+2) ≤ cutoff) :
    ∃ c d N₁ : Nat, ∀ Φ : ValidFormula, Φ.val.clauses.length ≤ cs*Φ.val.variables →
      N₁ ≤ Φ.val.variables →
      (algorithm D B C G cs cutoff hcut hsource).totalTime (EncodedCNF.encode Φ.val) ≤
        c*(randomizedSize C0 Φ.val.variables (G.gap Φ.val.variables))^d := by
  let E := ResourceFit.resourceExponent D B C
  let R := resource D B C G
  have hC01 : 1 ≤ C0 := (sourceConstant_pos D).trans hC0
  have hE : ResourceFit.sourceExponent D B ≤ E := by
    dsimp [E,ResourceFit.resourceExponent]; omega
  have hE1 : 1 ≤ E := ResourceFit.resourceExponent_pos D B C
  obtain ⟨a,d,had⟩ := ResourceFit.total_clock_manuscript_polynomial D B C G cs C0 E hC01 hE hE1
  let q := 3000+30*AEth4.phiLen cutoff
  refine ⟨4*a+2*q,d+9,max cutoff (28*cs+9),?_⟩
  intro Φ hsp hN
  have hcutΦ : cutoff ≤ Φ.val.variables := (le_max_left _ _).trans hN
  have hencΦ : 28*cs+9 ≤ Φ.val.variables := (le_max_right _ _).trans hN
  have hρ : routedSource cs cutoff hcut (EncodedCNF.encode Φ.val)=Φ := by
    apply Subtype.ext
    exact AEth4.routed4_encode (cs+2) cutoff Φ.val Φ.property
      (hsp.trans (Nat.mul_le_mul_right _ (by omega))) hcutΦ
  have ht := RandomizedRate.routedTests D B cs cutoff hcut hsource (EncodedCNF.encode Φ.val)
  rw [hρ] at ht
  have htotal := had Φ hsp hencΦ (RandomizedRate.sourceCoefficient D B Φ)
    (RandomizedRate.sourceDeltaV D B Φ) (RandomizedRate.sourceZeta D B) ht
  let Q := randomizedSize C0 Φ.val.variables (G.gap Φ.val.variables)
  have hQ : 1 ≤ Q := Nat.one_le_pow _ _ (by omega)
  have hdom : Φ.val.variables+2 ≤ Q := by
    have h := randomizedSize_dominates C0 Φ.val.variables (G.gap Φ.val.variables) hC01
    omega
  have henc := Unit4Shell.T24RuntimeComposed.encode_length_cube cs Φ hsp hencΦ
  have hin : (EncodedCNF.encode Φ.val).length+1 ≤ Q^3 :=
    (show (EncodedCNF.encode Φ.val).length+1 ≤ (Φ.val.variables+2)^3 by omega).trans
      (Nat.pow_le_pow_left hdom 3)
  have hroute : AEth4.route3Time (cs+2) cutoff (EncodedCNF.encode Φ.val) ≤ q*Q^9 := by
    change q*((EncodedCNF.encode Φ.val).length+1)^3 ≤ _
    have hp := Nat.mul_le_mul_left q (Nat.pow_le_pow_left hin 3)
    simpa only [←pow_mul] using hp
  have hexact := RandomizedRate.routedAlgorithm_totalTime_large D B C G R cs cutoff hcut hsource
    (fun w => concrete_resources D B C G (routedSource cs cutoff hcut w)
      (RandomizedRate.routedTests D B cs cutoff hcut hsource w)) Φ hsp hcutΦ
  have hactual : (algorithm D B C G cs cutoff hcut hsource).totalTime (EncodedCNF.encode Φ.val) ≤
      4*ResourceFit.totalClock D B C G E Φ+2*AEth4.route3Time (cs+2) cutoff (EncodedCNF.encode Φ.val) := by
    change (RandomizedRate.routedAlgorithm D B C G R cs cutoff hcut hsource _).totalTime _ ≤ _
    rw [hexact]
    dsimp [ResourceFit.totalClock]
    change (carrierProducer R).clock (EncodedCNF.encode Φ.val)+uniformClock D B C G R Φ+
      2*AEth4.route3Time (cs+2) cutoff (EncodedCNF.encode Φ.val)+14*(EncodedCNF.encode Φ.val).length+
      7*carrierLength R (EncodedCNF.encode Φ.val)+16 ≤
      4*((carrierProducer R).clock (EncodedCNF.encode Φ.val)+carrierLength R (EncodedCNF.encode Φ.val)+
        4*((EncodedCNF.encode Φ.val).length+carrierLength R (EncodedCNF.encode Φ.val)+1)+
          uniformClock D B C G R Φ)+2*AEth4.route3Time (cs+2) cutoff (EncodedCNF.encode Φ.val)
    omega
  have hp1 : Q^d ≤ Q^(d+9) := Nat.pow_le_pow_right hQ (by omega)
  have hp2 : Q^9 ≤ Q^(d+9) := Nat.pow_le_pow_right hQ (by omega)
  have h1 := htotal.trans (Nat.mul_le_mul_left a hp1)
  have h2 := hroute.trans (Nat.mul_le_mul_left q hp2)
  change _ ≤ (4*a+2*q)*Q^(d+9)
  nlinarith

#print axioms algorithm_clock
end
end CurrentV43.GeneralRandom
