import Paper2.EncodedSelectedOutput
import Paper2.RecursiveSamplingMaterialization
import EthInapproximability.CurrentPaper.MatrixMaterialization

/-!
# Unit 3 endpoint assembly, segment 1: the exact branches of `select`

Lane `owner:a-h-a3-assembly-1` (private, 26 September 2026). Production imports only.

`TotalFiniteConstructorScratch.select hn edge Δ γ k` has exactly TWO definitional branches
(`TotalFiniteConstructor.lean` lines 73-80):

* (S) `hc : CompletePublicScheduleScratch.Checks (Nat.clog 2 n) Δ γ` — `scheduledOutput`:
  rows `sourceRows`, cols `sourceCols`, budget `sourceBudget`, tape the literal fair-bit list,
  table `ParameterizedCanonicalSource.output … hc hn k bits
  = CanonicalDefaultSource.canonicalSourceOutput … = RecursiveSamplingMaterialization.materializeTapeList …`.
  Inside (S) the capped generator decides two sub-outcomes of ONE table expression:
  (S-some) the capped run returns `some` — the sampled table;
  (S-none) the capped run returns `none` — the all-false `mX × mY` table
  (`RecursiveSamplingExecution.run_eq_zero_of_abort`), still with budget `sourceBudget`.
* (U) `¬ hc` — `fallbackOutput`: rows `FiniteFallbackOutput.rows k`, cols `cols k`, budget `0`,
  tape `Unit` with `tapeBits = []`, table `tabulate (fallbackMatrix edge k)`.

The theorems below state these identities for the consumer word `EncodedSelectedOutput.outputBits`.
-/

namespace Paper2.A3Assembly.Branch

open EthInapproximability.CurrentPaper
open Paper2.TotalFiniteConstructorScratch
open Paper2.RecursiveSamplingMaterialization
open Paper2.RecursiveSamplingExecution

/-- Branch (U): on a failed public schedule the consumer word is the encoded fallback instance
with zero budget, and the tape word is empty. -/
theorem outputBits_unscheduled {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : ¬ CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) (Nat.clog 2 n) Δ γ)
    (t : (select hn edge Δ γ k).Tape) :
    EncodedSelectedOutput.outputBits hn edge Δ γ k t =
      EncodedCommunication.encodeInstance
        ⟨FiniteFallbackOutput.rows k, FiniteFallbackOutput.cols k, 0,
          MatrixMaterialization.rowMajor (FiniteFallbackOutput.fallbackMatrix edge k)⟩ ∧
    (select hn edge Δ γ k).tapeBits t = [] := by
  have key : ∀ (o : SelectedOutput) (_ : o = fallbackOutput edge k) (t : o.Tape),
      EncodedCommunication.encodeInstance
          (EncodedSelectedOutput.instanceOf (o.table t) o.budget) =
        EncodedCommunication.encodeInstance
          ⟨FiniteFallbackOutput.rows k, FiniteFallbackOutput.cols k, 0,
            MatrixMaterialization.rowMajor (FiniteFallbackOutput.fallbackMatrix edge k)⟩ ∧
      o.tapeBits t = [] := by
    intro o h t
    subst h
    exact ⟨rfl, rfl⟩
  exact key _ (select_bad hn edge Δ γ k hc) t

/-- Branch (S): on a passing public schedule the consumer word is the encoded scheduled
instance of the same tape (transported along `select_good`), and the tape word is unchanged. -/
theorem outputBits_scheduled {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) (Nat.clog 2 n) Δ γ)
    (t : (select hn edge Δ γ k).Tape) :
    EncodedSelectedOutput.outputBits hn edge Δ γ k t =
      EncodedCommunication.encodeInstance
        (EncodedSelectedOutput.instanceOf
          ((scheduledOutput hn edge Δ γ k hc).table
            (cast (congrArg SelectedOutput.Tape (select_good hn edge Δ γ k hc)) t))
          (scheduledOutput hn edge Δ γ k hc).budget) ∧
    (select hn edge Δ γ k).tapeBits t =
      (scheduledOutput hn edge Δ γ k hc).tapeBits
        (cast (congrArg SelectedOutput.Tape (select_good hn edge Δ γ k hc)) t) := by
  have key : ∀ (o : SelectedOutput) (h : o = scheduledOutput hn edge Δ γ k hc) (t : o.Tape),
      EncodedCommunication.encodeInstance
          (EncodedSelectedOutput.instanceOf (o.table t) o.budget) =
        EncodedCommunication.encodeInstance
          (EncodedSelectedOutput.instanceOf
            ((scheduledOutput hn edge Δ γ k hc).table (cast (congrArg SelectedOutput.Tape h) t))
            (scheduledOutput hn edge Δ γ k hc).budget) ∧
      o.tapeBits t = (scheduledOutput hn edge Δ γ k hc).tapeBits
        (cast (congrArg SelectedOutput.Tape h) t) := by
    intro o h t
    subst h
    exact ⟨rfl, rfl⟩
  exact key _ (select_good hn edge Δ γ k hc) t

/-- The dimensions and budget of branch (S), literally. -/
theorem scheduled_fields {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) (Nat.clog 2 n) Δ γ) :
    (scheduledOutput hn edge Δ γ k hc).rows =
        SourceRecursiveNoSampling.sourceRows (Nat.clog 2 n)
          (ParameterizedCanonicalSource.restorationDepth (Nat.clog 2 n))
          (ParameterizedCanonicalSource.coverDepth n m (Nat.clog 2 n) Δ γ) k ∧
    (scheduledOutput hn edge Δ γ k hc).cols =
        SourceRecursiveNoSampling.sourceCols (Nat.clog 2 n)
          (ParameterizedCanonicalSource.restorationDepth (Nat.clog 2 n))
          (ParameterizedCanonicalSource.coverDepth n m (Nat.clog 2 n) Δ γ) k ∧
    (scheduledOutput hn edge Δ γ k hc).budget =
        SourceRecursiveNoSampling.sourceBudget (Nat.clog 2 n)
          (ParameterizedCanonicalSource.restorationDepth (Nat.clog 2 n))
          (ParameterizedCanonicalSource.coverDepth n m (Nat.clog 2 n) Δ γ) k :=
  ⟨rfl, rfl, rfl⟩

variable {V : Type} [Fintype V] [Nonempty V]
  {s q₁ q₂ w Q : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q]

/-- Sub-outcome (S-none): when the actual capped run on the read tape returns `none`, the printed
table word is the all-false row-major word of the announced dimensions. -/
theorem materializeTapeList_abort (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (p : ℕ) (hp : 0 < p)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : RecursiveEntries.Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s V)
      s q₁ q₂ w Q)
    (k mX mY : ℕ) (bits : TapeList V s q₁ q₂ w Q p k mX mY)
    (h : RecursiveSamplingCapped.run _ _ le_rfl _
      (state order hs p hp activity ξ k mX mY) (RecursiveSamplingTape.readTape _ _ _ bits) = none) :
    (materializeTapeList order hs p hp activity ξ k mX mY bits).bits =
      MatrixMaterialization.rowMajor (fun (_ : Fin mX) (_ : Fin mY) => false) := by
  unfold materializeTapeList materialize
  rw [run_eq_zero_of_abort order hs p hp activity ξ k mX mY _ h]
  rfl

end Paper2.A3Assembly.Branch

#print axioms Paper2.A3Assembly.Branch.outputBits_unscheduled
#print axioms Paper2.A3Assembly.Branch.outputBits_scheduled
#print axioms Paper2.A3Assembly.Branch.scheduled_fields
#print axioms Paper2.A3Assembly.Branch.materializeTapeList_abort
