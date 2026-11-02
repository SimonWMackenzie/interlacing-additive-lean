import EthInapproximability.CurrentPaper.EncodedETHTail
import Paper2.SubexpLen
import CurrentAdditive.DeterministicETHFullSubexp

/-! Deterministic sparse ETH in the adopted finite Boolean-stack machine
model. Correctness is required on every sparse canonical formula, including
the finitely many below a runtime cutoff. The time bound is eventual, with
one fixed machine and constants chosen after the exponent scale. -/

namespace CurrentAdditive.DeterministicSparseETH

open EthInapproximability.CurrentPaper

structure Algorithm where
  machine : BitMachine.Machine
  answer : List Bool → Bool
  time : List Bool → ℕ
  run : ∀ w, machine.OutputsWithin w [answer w] (time w)

def SparseDecider (cs : ℕ) (A : Algorithm) : Prop :=
  (∀ Φ : EncodedETHSource.ValidFormula,
    Φ.val.clauses.length ≤ cs * Φ.val.variables →
      (A.answer (EncodedCNF.encode Φ.val) = true ↔
        EncodedCNF.Satisfiable Φ.val)) ∧
  ∀ ε : ℝ, 0 < ε → ∃ C d m₀ : ℕ,
    ∀ Φ : EncodedETHSource.ValidFormula,
      Φ.val.clauses.length ≤ cs * Φ.val.variables →
      m₀ ≤ Φ.val.variables →
      A.time (EncodedCNF.encode Φ.val) ≤
        C * ⌈(2:ℝ) ^ (ε * Φ.val.variables)⌉₊ *
          ((EncodedCNF.encode Φ.val).length + 1)^d

/-- The sparse form of deterministic ETH: one fixed clause-density
bound resists every all-input deterministic subexponential SAT machine. -/
def Holds : Prop := ∃ cs : ℕ, ¬∃ A : Algorithm, SparseDecider cs A

theorem contradiction_of_decider (hETH : Holds)
    (hall : ∀ cs : ℕ, ∃ A : Algorithm, SparseDecider cs A) : False := by
  obtain ⟨cs, hno⟩ := hETH
  exact hno (hall cs)

/-- Once the one physical solver has the source-correct all-input answer and
its charged clock is a fixed polynomial in the actual generated-table bound,
it violates the sparse deterministic ETH carrier. Finite formulas remain in
`hanswer`; the asymptotic estimate is used only above its explicit cutoff. -/
theorem sparse_decider_of_tableBound_clock
    (cs a C₀ b p K d : ℕ) (A : Algorithm)
    (ha : 1 ≤ a) (hC₀ : 1 ≤ C₀) (hb : 1 ≤ b) (hp : 1 ≤ p)
    (hanswer : ∀ Φ : EncodedETHSource.ValidFormula,
      Φ.val.clauses.length ≤ cs * Φ.val.variables →
        (A.answer (EncodedCNF.encode Φ.val) = true ↔
          EncodedCNF.Satisfiable Φ.val))
    (hclock : ∀ Φ : EncodedETHSource.ValidFormula,
      Φ.val.clauses.length ≤ cs * Φ.val.variables →
        A.time (EncodedCNF.encode Φ.val) ≤
          K * (CurrentAdditive.DeterministicETHFullSubexp.tableBound
            a C₀ b Φ.val.variables)^p *
            ((EncodedCNF.encode Φ.val).length + 1)^d) :
    SparseDecider cs A := by
  refine ⟨hanswer, ?_⟩
  intro ε hε
  obtain ⟨C, d₀, m₀, hsub⟩ :=
    CurrentAdditive.DeterministicETHFullSubexp.tableBound_power_subexp
      a C₀ b p ha hC₀ hb hp ε hε
  refine ⟨K*C, d+d₀, m₀, ?_⟩
  intro Φ hsparse hlarge
  let m := Φ.val.variables
  let X := (EncodedCNF.encode Φ.val).length + 1
  let Z := ⌈(2:ℝ)^(ε*(m:ℝ))⌉₊
  have hlen : m+1 ≤ X := by
    have hl := EncodedCNF.encode_length_lower Φ.val
    dsimp [X, m]
    omega
  have hmon : (m+1)^d₀ ≤ X^d₀ := Nat.pow_le_pow_left hlen d₀
  have hs := hsub m hlarge
  have hc := hclock Φ hsparse
  calc
    A.time (EncodedCNF.encode Φ.val)
        ≤ K * (CurrentAdditive.DeterministicETHFullSubexp.tableBound
          a C₀ b m)^p * X^d := hc
    _ ≤ K * (C*Z*(m+1)^d₀) * X^d := by
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left K hs)
    _ = K*C*Z*((m+1)^d₀*X^d) := by ring
    _ ≤ K*C*Z*(X^d₀*X^d) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hmon)
    _ = K*C*Z*X^(d+d₀) := by rw [pow_add]; ring

#print axioms sparse_decider_of_tableBound_clock

#print axioms contradiction_of_decider

end CurrentAdditive.DeterministicSparseETH
