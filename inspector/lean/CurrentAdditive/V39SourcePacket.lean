import Paper2.A4Kof
import Paper2.AFrontT10
import CurrentAdditive.DeterministicETHSourceBridge

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

namespace CurrentAdditive.V39SourceFront
noncomputable section
open Paper2
open EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition
open Paper2.Unit4Shell Paper2.Unit4Shell.T10Finite

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

def formula {cutoff : ℕ} (hcutoff : 1 ≤ cutoff) (w : List Bool) : ValidFormula :=
  AFront.T10.routed hcutoff w

def graph {cutoff : ℕ} (hcutoff : 1 ≤ cutoff) (w : List Bool) : EncodedGraph.Graph :=
  t10Graph D B (formula hcutoff w)

def gap {cutoff : ℕ} (hcutoff : 1 ≤ cutoff) (w : List Bool) : ℕ :=
  Asymptotics.kOf (formula hcutoff w).val.variables

def packet {cutoff : ℕ} (hcutoff : 1 ≤ cutoff) (w tape : List Bool) : List Bool :=
  BitMachineBankCodec.encode ![EncodedGraph.encode (graph D B hcutoff w),
    List.replicate (gap hcutoff w) true,tape]

private theorem route_budget (X m K CF EF T1 : ℕ) (hm : m ≤ X+2*K)
    (hT1 : T1 ≤ (300+2*K)*(X+1)^3) :
    T1+2*m+2+CF*(m+1)^EF ≤
      ((300+2*K)+2*(1+2*K)+2+CF*(1+2*K)^EF)*(X+1)^(3+EF) := by
  have h1 : 1 ≤ (X+1)^EF := Nat.one_le_pow _ _ (by omega)
  have h3 : (X+1)^3 ≤ (X+1)^(3+EF) := Nat.pow_le_pow_right (by omega) (by omega)
  have hX : X+1 ≤ (X+1)^(3+EF) := by
    simpa using (Nat.pow_le_pow_right (show 0<X+1 by omega) (show 1≤3+EF by omega))
  have hm1 : m+1 ≤ (1+2*K)*(X+1) := by nlinarith
  have hpow : (m+1)^EF ≤ (1+2*K)^EF*(X+1)^(3+EF) := by
    calc
      _ ≤ ((1+2*K)*(X+1))^EF := Nat.pow_le_pow_left hm1 EF
      _ = (1+2*K)^EF*(X+1)^EF := by rw [mul_pow]
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  have hA := hT1.trans (Nat.mul_le_mul_left (300+2*K) h3)
  have hB : 2*m+2 ≤ (2*(1+2*K)+2)*(X+1)^(3+EF) := by nlinarith
  have hC : CF*(m+1)^EF ≤ CF*(1+2*K)^EF*(X+1)^(3+EF) := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hpow
  nlinarith

/-- One fixed physical compiler on every original raw formula word and
every raw tape. The routed formula, source copies and k are all computed;
no graph, unary parameter, constructor bank or completed run is supplied. -/
theorem all_input_packet {cutoff : ℕ} (hcutoff : 1 ≤ cutoff) :
    ∃ (M : BitMachine.Machine) (C E : ℕ), ∀ w tape : List Bool,
      M.OutputsWithin (EncodedComplexity.pair w tape) (packet D B hcutoff w tape)
        (C*((EncodedComplexity.pair w tape).length+1)^E) := by
  obtain ⟨MF,CF,EF,hF⟩ := KofFront.front_T24_raw D B
  let K := (Front.phi cutoff true).length+(Front.phi cutoff false).length
  refine ⟨BitMachineComposition.composition (AFront.Route.frontRoute cutoff) MF,
    (300+2*K)+2*(1+2*K)+2+CF*(1+2*K)^EF,3+EF,?_⟩
  intro w tape
  have h1 := AFront.Route.frontRoute_outputs_poly hcutoff w tape
  have h2 := hF (formula hcutoff w) tape
  have he : EncodedCNF.encode (formula hcutoff w).val = Front.scanTarget cutoff w :=
    (AFront.Route.scanTarget_eq_encode cutoff w).symm
  rw [he] at h2
  have h := BitMachineComposition.composition_outputsWithin _ _ h1 h2
  apply BitMachine.outputsWithin_mono _ h
  apply route_budget
  · have hl := Front.scanTarget_length hcutoff w
    simp only [EncodedComplexity.pair_length]
    dsimp only [K]
    omega
  · exact le_rfl

theorem formula_variables {cutoff : ℕ} (hcutoff : 1 ≤ cutoff) (w : List Bool) :
    cutoff ≤ (formula hcutoff w).val.variables :=
  AFront.Route.routedFormula_variables (N:=cutoff) w

theorem formula_sat_iff {cutoff : ℕ} (hcutoff : 1 ≤ cutoff) (w : List Bool) :
    EncodedCNF.Satisfiable (formula hcutoff w).val ↔ w ∈ EncodedCNF.Language :=
  AFront.Route.routedFormula_sat_iff hcutoff w

theorem formula_large {cutoff : ℕ} (hcutoff : 1 ≤ cutoff) (Φ : ValidFormula)
    (hlarge : cutoff ≤ Φ.val.variables) : formula hcutoff (EncodedCNF.encode Φ.val) = Φ := by
  apply Subtype.ext
  exact AFront.T10.routed_large hcutoff (EncodedCNF.decode_encode Φ.val Φ.property) hlarge

theorem packet_large {cutoff : ℕ} (hcutoff : 1 ≤ cutoff) (Φ : ValidFormula)
    (hlarge : cutoff ≤ Φ.val.variables) (tape : List Bool) :
    packet D B hcutoff (EncodedCNF.encode Φ.val) tape =
      BitMachineBankCodec.encode ![EncodedGraph.encode (t10Graph D B Φ),
        List.replicate (Asymptotics.kOf Φ.val.variables) true,tape] := by
  unfold packet graph gap
  rw [formula_large hcutoff Φ hlarge]

theorem graph_valid {cutoff : ℕ} (hcutoff : 1 ≤ cutoff) (w : List Bool) :
    (graph D B hcutoff w).Valid := t10Graph_valid D B _

/-- The prescribed disjoint source-copy normalization provides the
original-variable floor in the exact graph printed by the compiler. -/
theorem source_size_floor {cutoff : ℕ} (hcutoff : 1 ≤ cutoff) (w : List Bool) :
    0 < (graph D B hcutoff w).edges.length ∧
    (formula hcutoff w).val.variables ≤ (graph D B hcutoff w).edges.length :=
  ⟨(t10_source D B _).1,(t10_source D B _).2.1⟩

end
end CurrentAdditive.V39SourceFront

#print axioms CurrentAdditive.V39SourceFront.all_input_packet
#print axioms CurrentAdditive.V39SourceFront.packet_large
#print axioms CurrentAdditive.V39SourceFront.source_size_floor
