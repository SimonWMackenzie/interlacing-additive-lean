import CurrentAdditive.QuarticConstructor
import Paper2.EncodedSelectedOutput

/-! The v27 selected table in the exact communication-instance codec. -/

namespace Paper2.CurrentAdditive.QuarticConstructor

open Paper2.EncodedSelectedOutput
open EthInapproximability.CurrentPaper
open Workspace.Types.CommComplexity

theorem select27_dimensions_pos {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ) :
    0 < (select27 hn edge Δ γ k).rows ∧
    0 < (select27 hn edge Δ γ k).cols := by
  by_cases hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ
  · rw [select27_good hn edge Δ γ k hc]
    have hL : 1 ≤ Nat.clog 2 n := by
      have h := hc
      dsimp only [CurrentAdditive.QuarticSchedule.Checks27] at h
      omega
    constructor
    · change 0 < rows27 n m (Nat.clog 2 n) Δ γ k
      unfold rows27 SourceRecursiveNoSampling.sourceRows
      exact compressionRowDraws_pos _ _ hL
    · change 0 < cols27 n m (Nat.clog 2 n) Δ γ k
      unfold cols27 SourceRecursiveNoSampling.sourceCols compressionColumnDraws
      omega
  · rw [select27_bad hn edge Δ γ k hc]
    change 0 < FiniteFallbackOutput.rows k ∧ 0 < FiniteFallbackOutput.cols k
    cases k with
    | zero => decide
    | succ k =>
      cases k with
      | zero => decide
      | succ k =>
        simp only [FiniteFallbackOutput.rows, FiniteFallbackOutput.cols]
        constructor <;> positivity

def selectedInstance27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (t : (select27 hn edge Δ γ k).Tape) : EncodedCommunication.Instance :=
  instanceOf ((select27 hn edge Δ γ k).table t)
    (select27 hn edge Δ γ k).budget

def outputBits27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (t : (select27 hn edge Δ γ k).Tape) : List Bool :=
  EncodedCommunication.encodeInstance
    (selectedInstance27 hn edge Δ γ k t)

theorem decode_outputBits27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (t : (select27 hn edge Δ γ k).Tape) :
    EncodedCommunication.decodeInstance (outputBits27 hn edge Δ γ k t) =
      some (selectedInstance27 hn edge Δ γ k t) := by
  have hp := select27_dimensions_pos hn edge Δ γ k
  exact EncodedCommunication.decode_encode _
    (instanceOf_valid _ _ hp.1 hp.2)

theorem outputBits27_language_iff {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (t : (select27 hn edge Δ γ k).Tape) :
    outputBits27 hn edge Δ γ k t ∈ EncodedCommunication.Language ↔
      D ((select27 hn edge Δ γ k).table t).matrix ≤
        (select27 hn edge Δ γ k).budget := by
  have hp := select27_dimensions_pos hn edge Δ γ k
  exact encode_instance_language_iff _ _ hp.1 hp.2

theorem outputBits27_length {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (t : (select27 hn edge Δ γ k).Tape) :
    let o := select27 hn edge Δ γ k
    (outputBits27 hn edge Δ γ k t).length =
      2 * (o.rows.bits.length + o.cols.bits.length + o.budget.bits.length) +
        3 + o.rows * o.cols := by
  rw [outputBits27, EncodedCommunication.encodeInstance_length]
  simp only [selectedInstance27, instanceOf, YaoMaterialization.SerializedTable.length]

#print axioms decode_outputBits27
#print axioms outputBits27_language_iff
#print axioms outputBits27_length

end Paper2.CurrentAdditive.QuarticConstructor
