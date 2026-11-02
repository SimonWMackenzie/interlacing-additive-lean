import CurrentAdditive.DeterministicETHPhysicalFixedMain
import CurrentAdditive.DeterministicSparseETHEventual
import EthInapproximability.CurrentPaper.FrontSpec

/-! The inherited validator/scanner is the physical all-input front. It
routes malformed and finitely small words to fixed valid witness formulas,
then calls the same fixed main machine. The large-arm premise below must be
discharged by `actual_t10_fixed_physical_main` for the supplied rectangle
producer; it is not a semantic branching oracle. -/

namespace CurrentAdditive.DeterministicETHPhysicalFront

open EthInapproximability.CurrentPaper
open CurrentAdditive.DeterministicSparseETH
open CurrentAdditive.DeterministicSparseETHEventual
open CurrentAdditive.DeterministicETHFullSubexp

noncomputable def fullMachine (cutoff : ℕ)
    (producer Me : BitMachine.Machine) (u : ℝ) : BitMachine.Machine :=
  Front.front cutoff
    (CurrentAdditive.DeterministicETHPhysicalFixedMain.machine producer Me u)

def frontClock (cutoff : ℕ) (Tmain : List Bool → ℕ)
    (w : List Bool) : ℕ :=
  250 * (w.length + 1)^3 + 2 * (w.length + 1) + 2 +
    (2 * w.length + 3) +
    2 * (w.length + (Front.phi cutoff true).length +
      (Front.phi cutoff false).length) + 2 +
    (Tmain w + Tmain (Front.phi cutoff true) +
      Tmain (Front.phi cutoff false))

theorem fullMachine_outputs (cutoff : ℕ) (hcutoff : 1 ≤ cutoff)
    (producer Me : BitMachine.Machine) (u : ℝ)
    (Tmain : List Bool → ℕ)
    (hmain : ∀ f : EncodedCNF.Formula, f.Valid → cutoff ≤ f.variables →
      (CurrentAdditive.DeterministicETHPhysicalFixedMain.machine producer Me u).OutputsWithin
        (EncodedCNF.encode f) [EncodedETHTail.satAnswer (EncodedCNF.encode f)]
        (Tmain (EncodedCNF.encode f)))
    (w : List Bool) :
    (fullMachine cutoff producer Me u).OutputsWithin w
      [EncodedETHTail.satAnswer w] (frontClock cutoff Tmain w) := by
  exact Front.front_outputs hcutoff
    (CurrentAdditive.DeterministicETHPhysicalFixedMain.machine producer Me u)
    Tmain hmain w

noncomputable def algorithm (cutoff : ℕ) (hcutoff : 1 ≤ cutoff)
    (producer Me : BitMachine.Machine) (u : ℝ)
    (Tmain : List Bool → ℕ)
    (hmain : ∀ f : EncodedCNF.Formula, f.Valid → cutoff ≤ f.variables →
      (CurrentAdditive.DeterministicETHPhysicalFixedMain.machine producer Me u).OutputsWithin
        (EncodedCNF.encode f) [EncodedETHTail.satAnswer (EncodedCNF.encode f)]
        (Tmain (EncodedCNF.encode f))) : Algorithm where
  machine := fullMachine cutoff producer Me u
  answer := EncodedETHTail.satAnswer
  time := frontClock cutoff Tmain
  run := fullMachine_outputs cutoff hcutoff producer Me u Tmain hmain

theorem algorithm_correct (cutoff : ℕ) (hcutoff : 1 ≤ cutoff)
    (producer Me : BitMachine.Machine) (u : ℝ)
    (Tmain : List Bool → ℕ)
    (hmain : ∀ f : EncodedCNF.Formula, f.Valid → cutoff ≤ f.variables →
      (CurrentAdditive.DeterministicETHPhysicalFixedMain.machine producer Me u).OutputsWithin
        (EncodedCNF.encode f) [EncodedETHTail.satAnswer (EncodedCNF.encode f)]
        (Tmain (EncodedCNF.encode f)))
    (Φ : EncodedETHSource.ValidFormula) :
    ((algorithm cutoff hcutoff producer Me u Tmain hmain).answer
      (EncodedCNF.encode Φ.val) = true ↔ EncodedCNF.Satisfiable Φ.val) := by
  change EncodedETHTail.satAnswer (EncodedCNF.encode Φ.val) = true ↔ _
  simp only [EncodedETHTail.satAnswer]
  simpa only [decide_eq_true_eq] using EncodedCNF.encode_mem_iff Φ.val Φ.property

/-- The validator/router and its two fixed witness calls are absorbed into
one polynomial factor. This bound charges those calls; it does not declare
them free or assume a formula-dependent machine. -/
theorem frontClock_polynomial_absorption
    (cutoff K B p d : ℕ) (Tmain : List Bool → ℕ)
    (w : List Bool) (hB : 1 ≤ B)
    (hmainClock : Tmain w ≤ K * B^p * (w.length+1)^d) :
    frontClock cutoff Tmain w ≤
      (K + 263 + 2*((Front.phi cutoff true).length+
        (Front.phi cutoff false).length) +
        Tmain (Front.phi cutoff true) +
        Tmain (Front.phi cutoff false)) *
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
  have hXd : B^p * X^d ≤ Q := by
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX (by omega))
  have hXQ : X ≤ Q := by
    have h1 : X ≤ X^3 := Nat.le_self_pow (by omega) X
    omega
  have hQ : 1 ≤ Q := by omega
  have hT : Tmain w ≤ K * Q := by
    have hh := Nat.mul_le_mul_left K hXd
    have hc : Tmain w ≤ K * (B^p * X^d) := by
      simpa only [X, Nat.mul_assoc] using hmainClock
    exact hc.trans hh
  have hshort : frontClock cutoff Tmain w ≤
      250*X^3 + 6*X +
        (7 + 2*((Front.phi cutoff true).length+
          (Front.phi cutoff false).length) +
          Tmain (Front.phi cutoff true) +
          Tmain (Front.phi cutoff false)) + Tmain w := by
    dsimp [frontClock, X]
    omega
  calc
    frontClock cutoff Tmain w ≤
        250*X^3 + 6*X +
          (7 + 2*((Front.phi cutoff true).length+
            (Front.phi cutoff false).length) +
            Tmain (Front.phi cutoff true) +
            Tmain (Front.phi cutoff false)) + Tmain w := hshort
    _ ≤ 250*Q + 6*Q +
          (7 + 2*((Front.phi cutoff true).length+
            (Front.phi cutoff false).length) +
            Tmain (Front.phi cutoff true) +
            Tmain (Front.phi cutoff false))*Q + K*Q := by
      have h₁ := Nat.mul_le_mul_left 250 hX3
      have h₂ := Nat.mul_le_mul_left 6 hXQ
      have h₃ := Nat.mul_le_mul_left
        (7 + 2*((Front.phi cutoff true).length+
          (Front.phi cutoff false).length) +
          Tmain (Front.phi cutoff true) +
          Tmain (Front.phi cutoff false)) hQ
      omega
    _ = (K + 263 + 2*((Front.phi cutoff true).length+
          (Front.phi cutoff false).length) +
          Tmain (Front.phi cutoff true) +
          Tmain (Front.phi cutoff false))*Q := by ring
    _ = (K + 263 + 2*((Front.phi cutoff true).length+
          (Front.phi cutoff false).length) +
          Tmain (Front.phi cutoff true) +
          Tmain (Front.phi cutoff false)) *
          B^p * (w.length+1)^(d+3) := by
      simp only [Q, X, Nat.mul_assoc]

/-- The single all-input physical machine violates sparse ETH whenever its
large canonical rectangle producer has an eventual charged table-bound clock.
The zero-variable and other finite formulas are resolved by the front's
all-input correctness, so no impossible zero-time condition is introduced. -/
theorem sparse_decider_of_mainClock
    (cutoff cs a C₀ b p K d m₁ : ℕ)
    (hcutoff : 1 ≤ cutoff)
    (ha : 1 ≤ a) (hC₀ : 1 ≤ C₀) (hb : 1 ≤ b)
    (hp : 1 ≤ p) (hm₁ : 1 ≤ m₁)
    (producer Me : BitMachine.Machine) (u : ℝ)
    (Tmain : List Bool → ℕ)
    (hmain : ∀ f : EncodedCNF.Formula, f.Valid → cutoff ≤ f.variables →
      (CurrentAdditive.DeterministicETHPhysicalFixedMain.machine producer Me u).OutputsWithin
        (EncodedCNF.encode f) [EncodedETHTail.satAnswer (EncodedCNF.encode f)]
        (Tmain (EncodedCNF.encode f)))
    (hmainClock : ∀ Φ : EncodedETHSource.ValidFormula,
      Φ.val.clauses.length ≤ cs * Φ.val.variables →
      m₁ ≤ Φ.val.variables →
        Tmain (EncodedCNF.encode Φ.val) ≤
          K * (tableBound a C₀ b Φ.val.variables)^p *
            ((EncodedCNF.encode Φ.val).length+1)^d) :
    SparseDecider cs (algorithm cutoff hcutoff producer Me u Tmain hmain) := by
  let K' := K + 263 + 2*((Front.phi cutoff true).length+
    (Front.phi cutoff false).length) +
    Tmain (Front.phi cutoff true) + Tmain (Front.phi cutoff false)
  apply sparse_decider_of_eventual_tableBound_clock
    cs a C₀ b p K' (d+3) m₁
    (algorithm cutoff hcutoff producer Me u Tmain hmain)
    ha hC₀ hb hp
  · intro Φ _
    exact algorithm_correct cutoff hcutoff producer Me u Tmain hmain Φ
  · intro Φ hsparse hlarge
    have hm : 1 ≤ Φ.val.variables := hm₁.trans hlarge
    have hB : 1 ≤ tableBound a C₀ b Φ.val.variables := by
      unfold tableBound
      exact Nat.one_le_pow _ _ hm
    exact frontClock_polynomial_absorption cutoff K
      (tableBound a C₀ b Φ.val.variables) p d Tmain
      (EncodedCNF.encode Φ.val) hB (hmainClock Φ hsparse hlarge)

#print axioms fullMachine_outputs
#print axioms algorithm_correct
#print axioms frontClock_polynomial_absorption
#print axioms sparse_decider_of_mainClock

end CurrentAdditive.DeterministicETHPhysicalFront
