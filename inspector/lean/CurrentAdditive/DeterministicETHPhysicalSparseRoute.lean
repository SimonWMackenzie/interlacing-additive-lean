import CurrentAdditive.DeterministicETHPhysicalDynamicIndexedMain
import CurrentAdditive.DeterministicSparseETHEventual
import Paper2.E4Front

/-! A charged density guard for the indexed deterministic ETH machine. The
inherited router maps every word to a valid, large, sparse canonical formula.
The expensive main machine is consequently required only on sparse formulas. -/

namespace CurrentAdditive.DeterministicETHPhysicalSparseRoute

open EthInapproximability.CurrentPaper
open CurrentAdditive.DeterministicSparseETH
open CurrentAdditive.DeterministicSparseETHEventual
open CurrentAdditive.DeterministicETHFullSubexp

noncomputable def fullMachine (cs cutoff : ℕ)
    (producer Me : BitMachine.Machine) : BitMachine.Machine :=
  BitMachineComposition.composition (Paper2.AEth4.route3 cs cutoff)
    (CurrentAdditive.DeterministicETHPhysicalDynamicIndexedMain.machine producer Me)

noncomputable def routedClock (cs cutoff : ℕ) (Tmain : List Bool → ℕ)
    (w : List Bool) : ℕ :=
  Paper2.AEth4.route3Time cs cutoff w +
    2 * (Paper2.AEth4.route3Out cs cutoff w).length + 2 +
      Tmain (Paper2.AEth4.route3Out cs cutoff w)

theorem fullMachine_outputs (cs cutoff : ℕ) (hcutoff : 1 ≤ cutoff)
    (hsparseWitness : 2 ≤ cs * cutoff)
    (producer Me : BitMachine.Machine) (Tmain : List Bool → ℕ)
    (hmain : ∀ f : EncodedCNF.Formula, f.Valid →
      f.clauses.length ≤ cs * f.variables → cutoff ≤ f.variables →
      (CurrentAdditive.DeterministicETHPhysicalDynamicIndexedMain.machine producer Me).OutputsWithin
        (EncodedCNF.encode f) [EncodedETHTail.satAnswer (EncodedCNF.encode f)]
        (Tmain (EncodedCNF.encode f)))
    (w : List Bool) :
    (fullMachine cs cutoff producer Me).OutputsWithin w
      [EncodedETHTail.satAnswer (Paper2.AEth4.route3Out cs cutoff w)]
      (routedClock cs cutoff Tmain w) := by
  have hroute := Paper2.AEth4.route3_outputs cs cutoff hcutoff w
  let f := Paper2.AEth4.routed4 cs cutoff w
  have hmain' := hmain f (Paper2.AEth4.routed4_valid cs hcutoff w)
    (Paper2.AEth4.routed4_sparse cs cutoff hsparseWitness w)
    (Paper2.AEth4.routed4_variables cs cutoff w)
  rw [← Paper2.AEth4.route3Out_eq cs cutoff w] at hmain'
  have hc := BitMachineComposition.composition_outputsWithin
    (Paper2.AEth4.route3 cs cutoff)
    (CurrentAdditive.DeterministicETHPhysicalDynamicIndexedMain.machine producer Me)
    hroute hmain'
  exact hc

noncomputable def algorithm (cs cutoff : ℕ) (hcutoff : 1 ≤ cutoff)
    (hsparseWitness : 2 ≤ cs * cutoff)
    (producer Me : BitMachine.Machine) (Tmain : List Bool → ℕ)
    (hmain : ∀ f : EncodedCNF.Formula, f.Valid →
      f.clauses.length ≤ cs * f.variables → cutoff ≤ f.variables →
      (CurrentAdditive.DeterministicETHPhysicalDynamicIndexedMain.machine producer Me).OutputsWithin
        (EncodedCNF.encode f) [EncodedETHTail.satAnswer (EncodedCNF.encode f)]
        (Tmain (EncodedCNF.encode f))) : Algorithm where
  machine := fullMachine cs cutoff producer Me
  answer w := EncodedETHTail.satAnswer (Paper2.AEth4.route3Out cs cutoff w)
  time := routedClock cs cutoff Tmain
  run := fullMachine_outputs cs cutoff hcutoff hsparseWitness producer Me Tmain hmain

theorem algorithm_correct (cs cutoff : ℕ) (hcutoff : 1 ≤ cutoff)
    (hsparseWitness : 2 ≤ cs * cutoff)
    (producer Me : BitMachine.Machine) (Tmain : List Bool → ℕ)
    (hmain : ∀ f : EncodedCNF.Formula, f.Valid →
      f.clauses.length ≤ cs * f.variables → cutoff ≤ f.variables →
      (CurrentAdditive.DeterministicETHPhysicalDynamicIndexedMain.machine producer Me).OutputsWithin
        (EncodedCNF.encode f) [EncodedETHTail.satAnswer (EncodedCNF.encode f)]
        (Tmain (EncodedCNF.encode f)))
    (Φ : EncodedETHSource.ValidFormula)
    (hsp : Φ.val.clauses.length ≤ cs * Φ.val.variables) :
    ((algorithm cs cutoff hcutoff hsparseWitness producer Me Tmain hmain).answer
      (EncodedCNF.encode Φ.val) = true ↔ EncodedCNF.Satisfiable Φ.val) := by
  change EncodedETHTail.satAnswer
      (Paper2.AEth4.route3Out cs cutoff (EncodedCNF.encode Φ.val)) = true ↔ _
  rw [Paper2.AEth4.route3Out_eq]
  simp only [EncodedETHTail.satAnswer, decide_eq_true_eq]
  have hs := Paper2.AEth4.routed4_sat_iff cs hcutoff Φ.val Φ.property hsp
  exact (EncodedCNF.encode_mem_iff _
    (Paper2.AEth4.routed4_valid cs hcutoff (EncodedCNF.encode Φ.val))).trans
      (hs.trans (EncodedCNF.encode_mem_iff Φ.val Φ.property))

theorem route3Out_sparse_large (cs cutoff : ℕ)
    (Φ : EncodedETHSource.ValidFormula)
    (hsp : Φ.val.clauses.length ≤ cs * Φ.val.variables)
    (hlarge : cutoff ≤ Φ.val.variables) :
    Paper2.AEth4.route3Out cs cutoff (EncodedCNF.encode Φ.val) =
      EncodedCNF.encode Φ.val := by
  rw [Paper2.AEth4.route3Out_eq,
    Paper2.AEth4.routed4_encode cs cutoff Φ.val Φ.property hsp hlarge]

theorem routedClock_polynomial_absorption
    (cs cutoff K B p d : ℕ) (Tmain : List Bool → ℕ)
    (w : List Bool) (hroute : Paper2.AEth4.route3Out cs cutoff w = w)
    (hB : 1 ≤ B)
    (hmainClock : Tmain w ≤ K * B^p * (w.length+1)^d) :
    routedClock cs cutoff Tmain w ≤
      (K + 3000 + 30*Paper2.AEth4.phiLen cutoff + 2) *
        B^p * (w.length+1)^(d+3) := by
  let X := w.length+1
  let Q := B^p * X^(d+3)
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hBp : 1 ≤ B^p := Nat.one_le_pow _ _ hB
  have hX3 : X^3 ≤ Q := by
    calc
      X^3 ≤ X^(d+3) := Nat.pow_le_pow_right hX (by omega)
      _ = 1 * X^(d+3) := by omega
      _ ≤ B^p * X^(d+3) := Nat.mul_le_mul_right _ hBp
  have hXQ : X ≤ Q := by
    have h1 : X ≤ X^3 := Nat.le_self_pow (by omega) X
    omega
  have hXd : B^p * X^d ≤ Q :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX (by omega))
  have hT : Tmain w ≤ K * Q := by
    have hh := Nat.mul_le_mul_left K hXd
    have hc : Tmain w ≤ K * (B^p * X^d) := by
      simpa only [X, Nat.mul_assoc] using hmainClock
    exact hc.trans hh
  rw [routedClock, hroute]
  simp only [Paper2.AEth4.route3Time]
  have hR := Nat.mul_le_mul_left (3000 + 30*Paper2.AEth4.phiLen cutoff) hX3
  have h2 := Nat.mul_le_mul_left 2 hXQ
  dsimp [Q, X] at *
  nlinarith

theorem sparse_decider_of_mainClock
    (cs cutoff a C₀ b p K d m₁ : ℕ)
    (hcutoff : 1 ≤ cutoff) (hsparseWitness : 2 ≤ cs * cutoff)
    (ha : 1 ≤ a) (hC₀ : 1 ≤ C₀) (hb : 1 ≤ b)
    (hp : 1 ≤ p)
    (producer Me : BitMachine.Machine) (Tmain : List Bool → ℕ)
    (hmain : ∀ f : EncodedCNF.Formula, f.Valid →
      f.clauses.length ≤ cs * f.variables → cutoff ≤ f.variables →
      (CurrentAdditive.DeterministicETHPhysicalDynamicIndexedMain.machine producer Me).OutputsWithin
        (EncodedCNF.encode f) [EncodedETHTail.satAnswer (EncodedCNF.encode f)]
        (Tmain (EncodedCNF.encode f)))
    (hmainClock : ∀ Φ : EncodedETHSource.ValidFormula,
      Φ.val.clauses.length ≤ cs * Φ.val.variables →
      m₁ ≤ Φ.val.variables →
        Tmain (EncodedCNF.encode Φ.val) ≤
          K * (tableBound a C₀ b Φ.val.variables)^p *
            ((EncodedCNF.encode Φ.val).length+1)^d) :
    SparseDecider cs
      (algorithm cs cutoff hcutoff hsparseWitness producer Me Tmain hmain) := by
  apply sparse_decider_of_eventual_tableBound_clock
    cs a C₀ b p
    (K + 3000 + 30*Paper2.AEth4.phiLen cutoff + 2) (d+3)
    (max cutoff m₁)
    (algorithm cs cutoff hcutoff hsparseWitness producer Me Tmain hmain)
    ha hC₀ hb hp
  · intro Φ hsparse
    exact algorithm_correct cs cutoff hcutoff hsparseWitness
      producer Me Tmain hmain Φ hsparse
  · intro Φ hsparse hlarge
    have hcut : cutoff ≤ Φ.val.variables := (le_max_left _ _).trans hlarge
    have hm₁ : m₁ ≤ Φ.val.variables := (le_max_right _ _).trans hlarge
    have hm : 1 ≤ Φ.val.variables := hcutoff.trans hcut
    have hB : 1 ≤ tableBound a C₀ b Φ.val.variables := by
      unfold tableBound
      exact Nat.one_le_pow _ _ hm
    exact routedClock_polynomial_absorption cs cutoff K
      (tableBound a C₀ b Φ.val.variables) p d Tmain
      (EncodedCNF.encode Φ.val)
      (route3Out_sparse_large cs cutoff Φ hsparse hcut)
      hB (hmainClock Φ hsparse hm₁)

#print axioms fullMachine_outputs
#print axioms algorithm_correct
#print axioms routedClock_polynomial_absorption
#print axioms sparse_decider_of_mainClock

end CurrentAdditive.DeterministicETHPhysicalSparseRoute
