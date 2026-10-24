import CurrentAdditive.DeterministicSparseETH

/-! A finite-exception-correct sparse ETH bridge. The generated-table clock
is required only beyond one fixed positive cutoff. Correctness still covers
every valid sparse formula, including the zero-variable case. -/

namespace CurrentAdditive.DeterministicSparseETHEventual

open EthInapproximability.CurrentPaper
open CurrentAdditive.DeterministicSparseETH
open CurrentAdditive.DeterministicETHFullSubexp

theorem sparse_decider_of_eventual_tableBound_clock
    (cs a C₀ b p K d m₁ : ℕ) (A : Algorithm)
    (ha : 1 ≤ a) (hC₀ : 1 ≤ C₀) (hb : 1 ≤ b) (hp : 1 ≤ p)
    (hanswer : ∀ Φ : EncodedETHSource.ValidFormula,
      Φ.val.clauses.length ≤ cs * Φ.val.variables →
        (A.answer (EncodedCNF.encode Φ.val) = true ↔
          EncodedCNF.Satisfiable Φ.val))
    (hclock : ∀ Φ : EncodedETHSource.ValidFormula,
      Φ.val.clauses.length ≤ cs * Φ.val.variables →
      m₁ ≤ Φ.val.variables →
        A.time (EncodedCNF.encode Φ.val) ≤
          K * (tableBound a C₀ b Φ.val.variables)^p *
            ((EncodedCNF.encode Φ.val).length + 1)^d) :
    SparseDecider cs A := by
  refine ⟨hanswer, ?_⟩
  intro ε hε
  obtain ⟨C, d₀, m₀, hsub⟩ :=
    tableBound_power_subexp a C₀ b p ha hC₀ hb hp ε hε
  refine ⟨K*C, d+d₀, max m₀ m₁, ?_⟩
  intro Φ hsparse hlarge
  let m := Φ.val.variables
  let X := (EncodedCNF.encode Φ.val).length + 1
  let Z := ⌈(2:ℝ)^(ε*(m:ℝ))⌉₊
  have hm₀ : m₀ ≤ m := (le_max_left _ _).trans hlarge
  have hm₁ : m₁ ≤ m := (le_max_right _ _).trans hlarge
  have hlen : m+1 ≤ X := by
    have hl := EncodedCNF.encode_length_lower Φ.val
    dsimp [X, m]
    omega
  have hmon : (m+1)^d₀ ≤ X^d₀ := Nat.pow_le_pow_left hlen d₀
  have hs := hsub m hm₀
  have hc := hclock Φ hsparse hm₁
  calc
    A.time (EncodedCNF.encode Φ.val)
        ≤ K * (tableBound a C₀ b m)^p * X^d := hc
    _ ≤ K * (C*Z*(m+1)^d₀) * X^d := by
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left K hs)
    _ = K*C*Z*((m+1)^d₀*X^d) := by ring
    _ ≤ K*C*Z*(X^d₀*X^d) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hmon)
    _ = K*C*Z*X^(d+d₀) := by rw [pow_add]; ring

#print axioms sparse_decider_of_eventual_tableBound_clock

end CurrentAdditive.DeterministicSparseETHEventual
