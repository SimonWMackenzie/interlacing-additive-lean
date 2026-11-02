import EthInapproximability.CurrentPaper.EncodedCNF
import EthInapproximability.CurrentPaper.CutoffBitMachine

/-!
# Exact encoded targets of the ETH conclusion

Source: frozen v8 `06-eth.tex`, ordered 3-CNF and raw square truth-table
conventions, the truth-table reduction, and the final midpoint test.

The ETH hypothesis below quantifies over actual finite Boolean-stack machines
deciding the existing concrete CNF language. Polynomial approximations also
quantify over those machines, with an explicit signed-integer output codec.
No opaque proposition stands in for either computational statement. The
branch theorem is only a semantic composition lemma; construction/runtime of
its input list remain separate obligations and are not claimed here.
-/

namespace EthInapproximability.CurrentPaper.EncodedETHTail

open Workspace.Types.CommComplexity
open BitMachine EncodedCommunication

def variableCount (input : List Bool) : ℕ :=
  match EncodedCNF.decode input with
  | none => 0
  | some f => f.variables

noncomputable def satAnswer (input : List Bool) : Bool :=
  @decide (input ∈ EncodedCNF.Language) (Classical.propDecidable _)

/-- The input-length factor is retained: ordered formulas may repeat clauses
arbitrarily often. Malformed strings have variable parameter zero and reject. -/
noncomputable def TimeBound (δ : ℝ) (c d : ℕ) (input : List Bool) : ℕ :=
  c * ⌈(2 : ℝ) ^ (δ * variableCount input)⌉₊ * (input.length + 1) ^ d

def HasSATSolver (δ : ℝ) : Prop :=
  ∃ M : Machine, ∃ c d : ℕ, ∀ input,
    M.OutputsWithin input [satAnswer input] (TimeBound δ c d input)

/-- The fixed-exponent ETH assumption, for the exact language and machine
model used in this formalisation. Standard source theorems are distinct. -/
def ETH : Prop := ∃ δ : ℝ, 0 < δ ∧ ¬ HasSATSolver δ

theorem satAnswer_malformed {input : List Bool} (h : EncodedCNF.decode input = none) :
    satAnswer input = false := by
  simp only [satAnswer, decide_eq_false_iff_not]
  exact EncodedCNF.malformed_not_mem h

theorem variableCount_encode (f : EncodedCNF.Formula) (hf : f.Valid) :
    variableCount (EncodedCNF.encode f) = f.variables := by
  simp [variableCount, EncodedCNF.decode_encode f hf]

/-- Negative values use a sign bit followed by a canonical magnitude field.
Zero always uses the nonnegative sign. -/
def encodeInteger (a : ℤ) : List Bool := decide (a < 0) :: natField a.natAbs

def readInteger : List Bool → Option ℤ
  | [] => none
  | negative :: bits => do
      let (magnitude, rest) ← readNat bits
      if rest = [] ∧ (negative = true → magnitude ≠ 0) then
        pure (if negative then -(magnitude : ℤ) else (magnitude : ℤ))
      else none

theorem readInteger_encode (a : ℤ) : readInteger (encodeInteger a) = some a := by
  have hread (n : ℕ) : readNat (natField n) = some (n, []) := by
    simpa only [List.append_nil] using readNat_append n []
  cases a with
  | ofNat n =>
      have hn : ¬(Int.ofNat n < 0) := not_lt_of_ge (Int.ofNat_zero_le n)
      simp [encodeInteger, readInteger, hread, hn]
  | negSucc n =>
      have hn : Int.negSucc n < 0 := by omega
      simp [encodeInteger, readInteger, hread, hn, Int.natAbs_negSucc]
      omega

theorem encodeInteger_injective : Function.Injective encodeInteger := by
  intro a b h
  have := congrArg readInteger h
  simpa only [readInteger_encode, Option.some.injEq] using this

/-- Truth tables have no header; exact length determines the square domain. -/
def rawMatrix (p : ℕ) (bits : List Bool) (i j : Fin (2 ^ p)) : Bool :=
  bits.getD (i.val * 2 ^ p + j.val) false

theorem rawMatrix_table {m r : ℕ} (R : Fin m → Fin r → Bool) (p : ℕ)
    (hm : 0 < m) (hr : 0 < r) :
    rawMatrix p (FinalPadding.table R p hm hr) = FinalPadding.matrix R p hm hr := by
  funext i j
  have h := FinalPadding.table_entry R p hm hr i j
  change ((FinalPadding.table R p hm hr)[i.val * 2 ^ p + j.val]?).getD false = _
  rw [h]
  rfl

theorem rawMatrix_table_cost {m r : ℕ} (R : Fin m → Fin r → Bool) (p : ℕ)
    (hm : 0 < m) (hr : 0 < r) (hrows : m ≤ 2 ^ p) (hcols : r ≤ 2 ^ p) :
    D (rawMatrix p (FinalPadding.table R p hm hr)) = D R := by
  rw [rawMatrix_table]
  exact FinalPadding.D_matrix R p hm hr hrows hcols

def PolynomialApproximation (allowance : ℕ → ℕ) : Prop :=
  ∃ answer : List Bool → ℤ, Polytime (fun input => encodeInteger (answer input)) ∧
    ∀ (p : ℕ) (input : List Bool), input.length = 2 ^ (2 * p) →
      |answer input - (D (rawMatrix p input) : ℤ)| ≤ (allowance input.length : ℤ)

structure Branch where
  exponent : ℕ
  table : List Bool
  threshold : ℕ
  length_eq : table.length = 2 ^ (2 * exponent)

noncomputable def Branch.cost (b : Branch) : ℕ := D (rawMatrix b.exponent b.table)

def paddedBranch {m r : ℕ} (R : Fin m → Fin r → Bool) (p Y : ℕ)
    (hm : 0 < m) (hr : 0 < r) : Branch :=
  ⟨p, FinalPadding.table R p hm hr, Y, FinalPadding.table_length R p hm hr⟩

theorem paddedBranch_cost {m r : ℕ} (R : Fin m → Fin r → Bool) (p Y : ℕ)
    (hm : 0 < m) (hr : 0 < r) (hrows : m ≤ 2 ^ p) (hcols : r ≤ 2 ^ p) :
    (paddedBranch R p Y hm hr).cost = D R :=
  rawMatrix_table_cost R p hm hr hrows hcols

def branchAccept (answer : List Bool → ℤ) (k : ℕ) (b : Branch) : Bool :=
  decide (2 * answer b.table < 2 * (b.threshold : ℤ) + (k : ℤ))

def listAccept (answer : List Bool → ℤ) (k : ℕ) (branches : List Branch) : Bool :=
  branches.any (branchAccept answer k)

/-- The source reduction's existential YES and universal NO quantifiers
give the exact encoded satisfiability answer. No gap or machine construction
is inferred from this interface lemma. -/
theorem listAccept_correct (input : List Bool) (branches : List Branch)
    (answer : List Bool → ℤ) (k A : ℕ)
    (herror : ∀ b ∈ branches, |answer b.table - (b.cost : ℤ)| ≤ (A : ℤ))
    (hgap : 2 * A < k)
    (hyes : input ∈ EncodedCNF.Language → ∃ b ∈ branches, b.cost ≤ b.threshold)
    (hno : input ∉ EncodedCNF.Language → ∀ b ∈ branches, b.cost = b.threshold + k) :
    listAccept answer k branches = satAnswer input := by
  classical
  by_cases hsat : input ∈ EncodedCNF.Language
  · obtain ⟨b, hb, hc⟩ := hyes hsat
    have hm := FinalPadding.midpoint_yes (answer b.table) b.cost b.threshold A k hc
      (herror b hb) hgap
    simp only [satAnswer, hsat, decide_true, listAccept, List.any_eq_true]
    exact ⟨b, hb, by simp [branchAccept, hm]⟩
  · have hall : ∀ b ∈ branches, branchAccept answer k b = false := by
      intro b hb
      have he := herror b hb
      rw [hno hsat b hb] at he
      have hm := FinalPadding.midpoint_no (answer b.table) b.threshold A k he hgap
      simp only [branchAccept, decide_eq_false_iff_not]
      omega
    simp only [satAnswer, hsat, decide_false, listAccept, List.any_eq_false]
    intro b hb
    rw [hall b hb]
    decide

end EthInapproximability.CurrentPaper.EncodedETHTail
