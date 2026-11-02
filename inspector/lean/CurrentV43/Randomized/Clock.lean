import CurrentV43.Randomized.Source
import CurrentV43.PowerSchedulePaid

namespace CurrentV43.RandomizedRate
noncomputable section
open CurrentAdditive Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition
open Unit4Shell.T10Finite Unit4Shell.Asymptotics
open CurrentAdditive.V43RandomizedRate
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768

/-- Explicit encoding bytes are bounded by a fixed source-graph power.
The constant accounts for the fixed clause density and source degree. -/
def inputPower (Δ cs : ℕ) := (14*cs+5)*(Δ+1)^2+2

theorem input_length_source_power (Δ cs n : ℕ) (Φ : ValidFormula)
    (hsp : Φ.val.clauses.length ≤ cs*Φ.val.variables) (hn : 1 ≤ n)
    (hlow : Φ.val.variables ≤ Δ*n) :
    (EncodedCNF.encode Φ.val).length+2 ≤ (n+2)^inputPower Δ cs := by
  have hi := V43PowerSchedule.sparse_input_bound cs Φ hsp
  have h1 : 1 ≤ (Φ.val.variables+1)^2 := Nat.one_le_pow _ _ (by omega)
  have hm : (EncodedCNF.encode Φ.val).length+2 ≤ (14*cs+5)*(Φ.val.variables+1)^2 := by nlinarith
  have hN : Φ.val.variables+1 ≤ (Δ+1)*(n+2) := by nlinarith
  have hsq := Nat.pow_le_pow_left hN 2
  let A := (14*cs+5)*(Δ+1)^2
  have ha : A ≤ (n+2)^A :=
    (Nat.le_of_lt Nat.lt_two_pow_self).trans (Nat.pow_le_pow_left (by omega) _)
  calc
    _ ≤ (14*cs+5)*((Δ+1)*(n+2))^2 := hm.trans (Nat.mul_le_mul_left _ hsq)
    _ = A*(n+2)^2 := by dsimp [A]; rw [mul_pow]; ring
    _ ≤ (n+2)^A*(n+2)^2 := Nat.mul_le_mul_right _ ha
    _ = _ := by rw [←pow_add]; rfl

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))
include D B

/-- Every fixed polynomial clock of input bytes and the physically printed
resource word has the required exponential-power rate in the original N.
This is numerical closure, with all sparse-source geometry discharged. -/
theorem input_polynomial_clock_power_time (a b E C d cs : ℕ)
    (ha : 0 < a) (hb : 0 < b) (α : ℝ)
    (hβα : (a:ℝ)/(b:ℝ) ≤ α) (hβ1 : (a:ℝ)/(b:ℝ) ≤ 1) :
    ∃ K N₀ : ℕ, ∀ Φ : ValidFormula,
      Φ.val.clauses.length ≤ cs*Φ.val.variables → N₀ ≤ Φ.val.variables →
      C*((EncodedCNF.encode Φ.val).length+
        ((EncodedCNF.encode Φ.val).length+2)^(E*(iterations a b Φ.val.variables+1))+1)^d ≤
        ⌈(2:ℝ)^((K:ℝ)*(Φ.val.variables:ℝ)^α)⌉₊ := by
  let Q := inputPower B.degreeBound cs
  obtain ⟨K,Nt,ht⟩ := polynomial_clock_power_time a b (E*Q) (D.sizeExponent+2) C d Q
    ha hb α hβα hβ1
  refine ⟨K,max Nt (V42SourceGeometry.originalCutoff D B cs),?_⟩
  intro Φ hsp hN
  obtain ⟨facts,_,hsize⟩ := V42SourceGeometry.source_all_large D B cs Φ hsp
    ((le_max_right _ _).trans hN)
  let n := (t10Graph D B Φ).vertices
  let k := iterations a b Φ.val.variables
  have hbase : 1 ≤ n+2 := by omega
  have hi := input_length_source_power B.degreeBound cs n Φ hsp facts.vertices_pos facts.original_degree_bound
  have hm : (EncodedCNF.encode Φ.val).length ≤ (n+2)^(Q*(k+1)) :=
    (show (EncodedCNF.encode Φ.val).length ≤ (EncodedCNF.encode Φ.val).length+2 by omega).trans
      (hi.trans (Nat.pow_le_pow_right hbase (by nlinarith)))
  have hr : ((EncodedCNF.encode Φ.val).length+2)^(E*(k+1)) ≤ (n+2)^((E*Q)*(k+1)) := by
    calc
      _ ≤ ((n+2)^Q)^(E*(k+1)) := Nat.pow_le_pow_left hi _
      _ = _ := by rw [←pow_mul]; congr 1; ring
  have hc := ht Φ.val.variables ((le_max_left _ _).trans hN) n (EncodedCNF.encode Φ.val).length
    facts.vertices_pos hsize hm
  exact (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (Nat.add_le_add_right
    (Nat.add_le_add_left hr _) _) d)).trans hc

#print axioms input_length_source_power
#print axioms input_polynomial_clock_power_time
end
end CurrentV43.RandomizedRate
