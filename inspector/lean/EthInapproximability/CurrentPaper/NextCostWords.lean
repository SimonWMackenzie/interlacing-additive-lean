import EthInapproximability.CurrentPaper.PhysicalLevelWords

/-! Lane owner:b-weighted-level-5, unit 2, segment 2 (levels j > 0), piece 2b:
the level-`j+1` cost word in a form computable from SHORT unary words
available at level `j` (no unary `outerWidth = 2^(1000 λ²)` word is needed):

  cost_{j+1} = cost_j + 2256·λ² + 10000·(clog₂ λ)² + clog₂(12·s·|E|)
               + clog₂(1280·b·c·s) + 1,

with `λ = Parameters.scale p` (the word `prepProgram` computes with the admitted
scale controller), `s = Parameters.bins p` (writer 28), `b = p.nextDepth`,
`c = p.sourceConstant`, `|E| = p.edges`, for `b, c ≥ 1`. Target identities
only; NO machine claim. -/

namespace EthInapproximability.CurrentPaper.NextCostWords

open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open Iteration EffectiveIteration PhysicalLevelRun

theorem clog_mul_two_pow (x e : ℕ) (hx : 1 ≤ x) :
    Nat.clog 2 (x * 2 ^ e) = Nat.clog 2 x + e := by
  apply le_antisymm
  · rw [Nat.clog_le_iff_le_pow (by norm_num), pow_add]
    exact Nat.mul_le_mul_right _ (Nat.le_pow_clog (by norm_num) x)
  · have hk := Nat.le_pow_clog (by norm_num : 1 < 2) (x * 2 ^ e)
    generalize hK : Nat.clog 2 (x * 2 ^ e) = k at hk ⊢
    have hek : e ≤ k := by
      by_contra h
      push_neg at h
      have h1 : 2 ^ k < 2 ^ e := Nat.pow_lt_pow_right (by norm_num) h
      have h2 : 2 ^ e ≤ x * 2 ^ e := Nat.le_mul_of_pos_left _ hx
      omega
    obtain ⟨m, hm⟩ : ∃ m, k = e + m := ⟨k - e, by omega⟩
    rw [hm] at hk ⊢
    have hx' : x ≤ 2 ^ m := by
      rw [pow_add, mul_comm (2 ^ e)] at hk
      exact Nat.le_of_mul_le_mul_right hk (by positivity)
    have := (Nat.clog_le_iff_le_pow (by norm_num)).2 hx'
    omega

/-- The restoration exponent splits off the outer exponent. -/
theorem restorationExponent_split (i : Parameters.Input)
    (hb : 1 ≤ i.nextDepth) (hc : 1 ≤ i.sourceConstant) :
    Parameters.restorationExponent i =
      Nat.clog 2 (1280 * i.nextDepth * i.sourceConstant * Parameters.bins i) +
        Parameters.outerExponent i := by
  unfold Parameters.restorationExponent Parameters.restorationTarget Parameters.outerWidth
  apply clog_mul_two_pow
  have hs : 1 ≤ Parameters.bins i := Nat.one_le_two_pow
  have h1 : 1 ≤ 1280 * i.nextDepth := by omega
  have h2 : 1 ≤ 1280 * i.nextDepth * i.sourceConstant := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (by omega))
  exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))

/-- The five-exponent overhead plus one, in short-word form. -/
theorem overhead_short (i : Parameters.Input)
    (hb : 1 ≤ i.nextDepth) (hc : 1 ≤ i.sourceConstant) :
    Parameters.firstExponent i + Parameters.secondExponent i + Parameters.binExponent i +
        Parameters.outerExponent i + Parameters.restorationExponent i + 1 =
      2256 * Parameters.scale i ^ 2 + 10000 * Nat.clog 2 (Parameters.scale i) ^ 2 +
        Nat.clog 2 (12 * Parameters.bins i * i.edges) +
        Nat.clog 2 (1280 * i.nextDepth * i.sourceConstant * Parameters.bins i) + 1 := by
  rw [restorationExponent_split i hb hc]
  unfold Parameters.firstExponent Parameters.secondExponent Parameters.binExponent
    Parameters.outerExponent Parameters.auxiliaryLog
  ring

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The level-`j+1` cost word of the physical run, from short level-`j` words. -/
theorem cost_word_succ (G : EndpointGraph V E) (c b j : ℕ) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    ETHParameterScaleMachineInput.words (runParameters G c b (seedState b) (j + 1)) 2 =
      List.replicate ((runParameters G c b (seedState b) j).cost +
        (2256 * Parameters.scale (runParameters G c b (seedState b) j) ^ 2 +
          10000 * Nat.clog 2 (Parameters.scale (runParameters G c b (seedState b) j)) ^ 2 +
          Nat.clog 2 (12 * Parameters.bins (runParameters G c b (seedState b) j) *
            Fintype.card E) +
          Nat.clog 2 (1280 * b * c * Parameters.bins (runParameters G c b (seedState b) j)) +
          1)) true := by
  have hw := (PhysicalLevelWords.words_succ G c b j).2.2.1
  rw [hw]
  have hnd : (runParameters G c b (seedState b) j).nextDepth = b := rfl
  have hsc : (runParameters G c b (seedState b) j).sourceConstant = c :=
    rfl
  have hed : (runParameters G c b (seedState b) j).edges = Fintype.card E :=
    rfl
  have ho := overhead_short (runParameters G c b (seedState b) j) (by omega) (by omega)
  rw [hnd, hsc, hed] at ho
  congr 1
  omega

#print axioms clog_mul_two_pow
#print axioms restorationExponent_split
#print axioms overhead_short
#print axioms cost_word_succ

end EthInapproximability.CurrentPaper.NextCostWords
