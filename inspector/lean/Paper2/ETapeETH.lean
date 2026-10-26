import Paper2.ETape
import Paper2.SubexpETH

/-!
# Paper A (lock v12), lane `owner:a-eth-2`, segment 1: randomized sparse ETH in the R20 carrier

Lock v12 `sections/06-reduction.tex:95-102` (`def:reth`):
"Randomized sparse ETH asserts that, for some fixed constant $c_s$, there is no bounded-error
randomized algorithm deciding $3$-SAT on $N$ variables and at most $c_sN$ clauses in worst-case
time $2^{o(N)}$. The sparse source assumption is made directly; no deterministic ETH assumption
is being silently extended to randomized algorithms."

Author decision **D-A6**: "The DRAFT `RandomizedSparseETH` shape: exists c_s; no randomized
decider with error <= 1/3 on well-formed 3-CNF inputs with clauses <= c_s N, with time <=
2^(eps N) (|input| + 1)^(O(1)) for every eps > 0 eventually (promise form, explicit polynomial
factor)." ROOT DECISION R20: the carrier is the R20-repaired `ETape.Algorithm`.

`SparseDeciderR20 cs A` is token-for-token `Paper2.AEth.SparseDecider cs` (a-eth-owner-1, itself
the admitted `AModel.RandomizedSparseETH` shape) on the R20 carrier; `sparseDeciderR20_iff` shows
it IS `SparseDecider cs A.toOld` (Iff.rfl). Relations: the a-eth-owner-1 assumption, the admitted
prefix assumption and the admitted DRAFT shape each imply `RandomizedSparseETH_R20`; so
`¬ RandomizedSparseETH_R20` refutes all three (it is the strongest refutation).

`whole_budget` (D-A6 for the whole decider, R20): for every R20 sparse decider, the decider's
clock PLUS the length machine's budget `lenCap` (within which the length machine either halts with
the tape length or certifies `time x < tapeLen |x|`, `lenCap_decides`; no machine computes
`lenCap`) is `≤ C ⌈2^(εN)⌉ (|input|+1)^d` eventually, for every `ε > 0`.

No ledger row is closed.
-/

noncomputable section

namespace Paper2.AEth2

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedComplexity

/-- **D-A6 decision at density `cs` in the R20 carrier.** -/
def SparseDeciderR20 (cs : ℕ) (A : ETape.Algorithm) : Prop :=
  (∀ input, Paper2.AModel.WellFormedCNF input →
    Paper2.AModel.cnfClauseCount input ≤ cs * EncodedETHTail.variableCount input →
    (input ∈ EncodedCNF.Language → 1 - 1 / 3 ≤ A.prob input (· = [true])) ∧
    (input ∉ EncodedCNF.Language → A.prob input (· = [true]) ≤ 1 / 3)) ∧
  ∀ ε : ℝ, 0 < ε → ∃ C d N₀ : ℕ, ∀ input, Paper2.AModel.WellFormedCNF input →
    Paper2.AModel.cnfClauseCount input ≤ cs * EncodedETHTail.variableCount input →
    N₀ ≤ EncodedETHTail.variableCount input →
    A.time input ≤ C * ⌈(2 : ℝ) ^ (ε * EncodedETHTail.variableCount input)⌉₊ *
      (input.length + 1) ^ d

/-- **D-A6, randomized sparse ETH in the R20 carrier** (lock `def:reth`). -/
def RandomizedSparseETH_R20 : Prop :=
  ∃ cs : ℕ, ¬ ∃ A : ETape.Algorithm, SparseDeciderR20 cs A

theorem sparseDeciderR20_iff (cs : ℕ) (A : ETape.Algorithm) :
    SparseDeciderR20 cs A ↔ Paper2.AEth.SparseDecider cs A.toOld := Iff.rfl

/-- The a-eth-owner-1 effective assumption implies the R20 one. -/
theorem old_implies_R20 (h : Paper2.AEth.RandomizedSparseETH_effective) :
    RandomizedSparseETH_R20 := by
  obtain ⟨cs, hno⟩ := h
  exact ⟨cs, fun ⟨A, hA⟩ => hno ⟨A.toOld, hA⟩⟩

theorem prefix_implies_R20 (h : Paper2.AModel.RandomizedSparseETH) : RandomizedSparseETH_R20 :=
  old_implies_R20 (Paper2.AEth.prefix_implies_effective h)

theorem draft_implies_R20
    (h : Paper2.Unit4Shell.Definitions.RandomizedSparseETH EncodedCNF.Language
      Paper2.AModel.WellFormedCNF EncodedETHTail.variableCount Paper2.AModel.cnfClauseCount
      (1 / 3) true) :
    RandomizedSparseETH_R20 :=
  old_implies_R20 (Paper2.AEth.draft_implies_effective h)

theorem not_old_of_not_R20 (h : ¬ RandomizedSparseETH_R20) :
    ¬ Paper2.AEth.RandomizedSparseETH_effective := fun h' => h (old_implies_R20 h')

theorem not_prefix_of_not_R20 (h : ¬ RandomizedSparseETH_R20) :
    ¬ Paper2.AModel.RandomizedSparseETH := fun h' => h (prefix_implies_R20 h')

theorem not_draft_of_not_R20 (h : ¬ RandomizedSparseETH_R20) :
    ¬ Paper2.Unit4Shell.Definitions.RandomizedSparseETH EncodedCNF.Language
      Paper2.AModel.WellFormedCNF EncodedETHTail.variableCount Paper2.AModel.cnfClauseCount
      (1 / 3) true := fun h' => h (draft_implies_R20 h')

theorem not_R20_iff :
    ¬ RandomizedSparseETH_R20 ↔ ∀ cs : ℕ, ∃ A : ETape.Algorithm, SparseDeciderR20 cs A := by
  unfold RandomizedSparseETH_R20
  constructor
  · intro h cs
    by_contra hc
    exact h ⟨cs, hc⟩
  · rintro h ⟨cs, hc⟩
    exact hc (h cs)

theorem sparseDeciderR20_mono {cs cs' : ℕ} (h : cs ≤ cs') {A : ETape.Algorithm}
    (hA : SparseDeciderR20 cs' A) : SparseDeciderR20 cs A :=
  (sparseDeciderR20_iff cs A).2 (Paper2.AEth.sparseDecider_mono (A := A.toOld) h ((sparseDeciderR20_iff cs' A).1 hA))

/-- Pure arithmetic of the whole-decider budget. -/
theorem budget_arith (lenC E C X Y P m T : ℕ) (hT : T ≤ C * X * P) (hX1 : 1 ≤ X) (hP1 : 1 ≤ P)
    (hXE : X ^ E ≤ 2 ^ E * Y) (hXY : X ≤ Y) :
    lenC * (m + T + 1) ^ E + T ≤ (lenC * ((C + 1) ^ E * 2 ^ E) + C) * Y * ((P * (m + 1)) ^ E * P) := by
  have hXP : 1 ≤ X * P := by simpa using Nat.mul_le_mul hX1 hP1
  have h1 : (m + 1) * 1 ≤ (m + 1) * (X * P) := Nat.mul_le_mul_left _ hXP
  have h2 : C * X * P * 1 ≤ C * X * P * (m + 1) := Nat.mul_le_mul_left _ (by omega)
  have hbase : m + T + 1 ≤ (C + 1) * X * (P * (m + 1)) := by
    have e : (C + 1) * X * (P * (m + 1)) = C * X * P * (m + 1) + (m + 1) * (X * P) := by ring
    rw [e]
    omega
  have hQ1 : 1 ≤ (P * (m + 1)) ^ E := Nat.one_le_pow _ _ (by
    have : 1 ≤ P * (m + 1) := by simpa using Nat.mul_le_mul hP1 (by omega : 1 ≤ m + 1)
    omega)
  generalize hQ : (P * (m + 1)) ^ E = Q at hQ1
  have hA : lenC * (m + T + 1) ^ E ≤ lenC * ((C + 1) ^ E * 2 ^ E) * Y * Q := by
    have hs : (m + T + 1) ^ E ≤ ((C + 1) * X * (P * (m + 1))) ^ E := Nat.pow_le_pow_left hbase E
    rw [mul_pow, mul_pow, hQ] at hs
    calc lenC * (m + T + 1) ^ E ≤ lenC * ((C + 1) ^ E * X ^ E * Q) := Nat.mul_le_mul_left _ hs
      _ ≤ lenC * ((C + 1) ^ E * (2 ^ E * Y) * Q) := by
          apply Nat.mul_le_mul_left
          apply Nat.mul_le_mul_right
          exact Nat.mul_le_mul_left _ hXE
      _ = lenC * ((C + 1) ^ E * 2 ^ E) * Y * Q := by ring
  have hB : T ≤ C * Y * (Q * P) := by
    calc T ≤ C * X * P := hT
      _ ≤ C * Y * P := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hXY)
      _ = C * Y * P * 1 := by ring
      _ ≤ C * Y * P * Q := Nat.mul_le_mul_left _ hQ1
      _ = C * Y * (Q * P) := by ring
  have hA' : lenC * ((C + 1) ^ E * 2 ^ E) * Y * Q * 1 ≤ lenC * ((C + 1) ^ E * 2 ^ E) * Y * Q * P :=
    Nat.mul_le_mul_left _ hP1
  have e : (lenC * ((C + 1) ^ E * 2 ^ E) + C) * Y * (Q * P) =
      lenC * ((C + 1) ^ E * 2 ^ E) * Y * Q * P + C * Y * (Q * P) := by ring
  rw [e]
  omega

/-- **D-A6 budget for the R20 decider's clock plus the length budget `lenCap`** (R20, as
corrected by R22 point 4: the whole *simulation*, including deciding whether the tape ends
before the machine could reach it, runs within the D-A6 budget; under the `extend` field even
that query is unnecessary). For every R20 sparse decider and every `ε > 0` there are constants with
`lenCap input + time input ≤ C ⌈2^(εN)⌉ (|input|+1)^d` on the promise inputs with `N ≥ N₀`;
within `lenCap input` steps the fixed length machine either halts with the tape length or
certifies `time x < tapeLen |x|` (`ETape.Algorithm.lenCap_decides`); no machine computes
`lenCap`. -/
theorem whole_budget (cs : ℕ) (A : ETape.Algorithm) (hA : SparseDeciderR20 cs A) :
    ∀ ε : ℝ, 0 < ε → ∃ C d N₀ : ℕ, ∀ input, Paper2.AModel.WellFormedCNF input →
      Paper2.AModel.cnfClauseCount input ≤ cs * EncodedETHTail.variableCount input →
      N₀ ≤ EncodedETHTail.variableCount input →
      A.lenCap input + A.time input ≤
        C * ⌈(2 : ℝ) ^ (ε * EncodedETHTail.variableCount input)⌉₊ * (input.length + 1) ^ d := by
  intro ε hε
  have hε₀ : 0 < ε / (A.lenE + 1) := by positivity
  obtain ⟨C, d, N₀, hC⟩ := hA.2 (ε / (A.lenE + 1)) hε₀
  refine ⟨A.lenC * ((C + 1) ^ A.lenE * 2 ^ A.lenE) + C, (d + 1) * A.lenE + d, N₀,
    fun input h1 h2 h3 => ?_⟩
  have hT := hC input h1 h2 h3
  set N := EncodedETHTail.variableCount input
  have hX1 := one_le_ceil_two_rpow (ε / (A.lenE + 1) * N)
  have hXE := ceil_pow_le (x := (N : ℝ)) A.lenE hε₀.le (Nat.cast_nonneg N)
    (eps_div_mul_le ε hε A.lenE)
  have hXY : ⌈(2 : ℝ) ^ (ε / (A.lenE + 1) * N)⌉₊ ≤ ⌈(2 : ℝ) ^ (ε * N)⌉₊ := by
    apply Nat.ceil_mono
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg N)
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hP1 : 1 ≤ (input.length + 1) ^ d := Nat.one_le_pow _ _ (by omega)
  have hcap : A.lenCap input ≤ A.lenC * (input.length + A.time input + 1) ^ A.lenE := by
    unfold ETape.Algorithm.lenCap
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    have := min_le_right (A.tapeLen input.length) (A.time input)
    omega
  have key := budget_arith A.lenC A.lenE C _ _ _ input.length (A.time input) hT hX1 hP1 hXE hXY
  have hpow : (input.length + 1) ^ ((d + 1) * A.lenE + d) =
      ((input.length + 1) ^ d * (input.length + 1)) ^ A.lenE * (input.length + 1) ^ d := by
    rw [pow_add, pow_mul, pow_succ]
  rw [hpow]
  omega

end Paper2.AEth2

end

#print axioms Paper2.AEth2.sparseDeciderR20_iff
#print axioms Paper2.AEth2.old_implies_R20
#print axioms Paper2.AEth2.prefix_implies_R20
#print axioms Paper2.AEth2.draft_implies_R20
#print axioms Paper2.AEth2.not_old_of_not_R20
#print axioms Paper2.AEth2.not_prefix_of_not_R20
#print axioms Paper2.AEth2.not_draft_of_not_R20
#print axioms Paper2.AEth2.not_R20_iff
#print axioms Paper2.AEth2.sparseDeciderR20_mono
#print axioms Paper2.AEth2.budget_arith
#print axioms Paper2.AEth2.whole_budget
