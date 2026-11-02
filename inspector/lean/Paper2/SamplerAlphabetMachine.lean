import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps
import EthInapproximability.CurrentPaper.SourceClauseFixedUnary
import EthInapproximability.CurrentPaper.BitMachineRawSequence
import Paper2.RecursiveSamplingExecution

set_option maxHeartbeats 8000000

namespace Paper2.SamplerAlphabetMachine

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineRawSequence

abbrev Stack := Fin 9
abbrev Source := Fin 7

def input (q₁ q₂ s w Q n p : Nat) : Stack → List Bool :=
  ![List.replicate q₁ true, List.replicate q₂ true,
    List.replicate s true, List.replicate w true,
    List.replicate Q true, List.replicate n true,
    List.replicate p true, [], []]

def count (q₁ q₂ s w Q n p : Nat) : Source → Nat :=
  ![q₁, q₂, s, w, Q, n, p]

def slots : List Source := [0, 1, 2, 2, 2, 2, 3, 4, 5, 6]

def select (i : Source) : Fin 3 ↪ Stack where
  toFun := ![⟨i.val, by omega⟩, 7, 8]
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp at h ⊢
    all_goals
      have hi := i.isLt
      have hv := congrArg Fin.val h
      simp at hv
      omega

def Label : List Source → Type
  | [] => SourceClauseFixedUnary.Label 514
  | _ :: xs => BitMachineRawSequence.Label (Label xs) BitMachineCopy.Label

def Control : List Source → Type
  | [] => Unit
  | _ :: xs => Control xs × Option Bool

def first : (xs : List Source) → Label xs
  | [] => (⟨0, by omega⟩ : SourceClauseFixedUnary.Label 514)
  | _ :: xs => .inl (first xs)

def initialControl : (xs : List Source) → Control xs
  | [] => ()
  | _ :: xs => (initialControl xs, none)

def program : (xs : List Source) →
    Label xs → TM2.Stmt (fun _ : Stack => Bool) (Label xs) (Control xs)
  | [] => SourceClauseFixedUnary.program 7 514
  | i :: xs => BitMachineRawSequence.program
      (program xs)
      (MatrixStage4ScalarPreparationOps.copyProgram (select i))
      .scan (initialControl xs) none

def sumCounts (f : Source → Nat) : List Source → Nat
  | [] => 0
  | i :: xs => sumCounts f xs + f i

def cost (f : Source → Nat) : List Source → Nat
  | [] => 515
  | i :: xs => cost f xs + (2 * f i + 2) + 1

theorem run_slots (f : Source → Nat) (S : Stack → List Bool)
    (hsource : ∀ i, S ⟨i.val, by omega⟩ = List.replicate (f i) true)
    (hout : S 7 = []) (hscratch : S 8 = []) :
    ∀ xs : List Source,
      ∃ t ≤ cost f xs,
        ((advance (program xs))^[t])
          (⟨some (first xs), initialControl xs, S⟩ :
            TM2.Cfg (fun _ : Stack => Bool) (Label xs) (Control xs)) =
          ⟨none, initialControl xs,
            Function.update S 7 (List.replicate (514 + sumCounts f xs) true)⟩ := by
  intro xs
  induction xs with
  | nil =>
      refine ⟨515, by rfl, ?_⟩
      simpa only [program, first, initialControl, cost, sumCounts, Nat.add_zero]
        using SourceClauseFixedUnary.run (7 : Stack) S 514 hout
  | cons i xs ih =>
      obtain ⟨ta, hta, ha⟩ := ih
      let T := Function.update S 7
        (List.replicate (514 + sumCounts f xs) true)
      have htSource : T (select i 0) = List.replicate (f i) true := by
        have hne : (⟨i.val, by omega⟩ : Stack) ≠ 7 := by
          intro h
          have hv := congrArg Fin.val h
          have hi := i.isLt
          simp at hv
          omega
        change T ⟨i.val, by omega⟩ = _
        simp only [T, Function.update_of_ne hne]
        exact hsource i
      have htScratch : T (select i 2) = [] := by
        simpa [T, select] using hscratch
      have hb := MatrixStage4ScalarPreparationOps.copy_run (select i) T htScratch
      have hlen : (T (select i 0)).length = f i := by simp [htSource]
      rw [hlen] at hb
      have htail :
          Function.update T (select i 1)
            (T (select i 0) ++ T (select i 1)) =
          Function.update S 7
            (List.replicate (514 + sumCounts f (i :: xs)) true) := by
        funext j
        by_cases hj : j = 7
        · subst j
          change T (select i 0) ++ T 7 =
            List.replicate (514 + sumCounts f (i :: xs)) true
          rw [htSource]
          simp only [T, Function.update_self,
            List.replicate_append_replicate]
          simp only [sumCounts]
          congr 1
          omega
        · simp [T, select, Function.update_of_ne hj]
      obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
        (program xs)
        (MatrixStage4ScalarPreparationOps.copyProgram (select i))
        (first xs) BitMachineCopy.Label.scan
        (initialControl xs) (initialControl xs) none none
        S T
        (Function.update T (select i 1)
          (T (select i 0) ++ T (select i 1)))
        ta (2 * f i + 2) ha hb
      refine ⟨t, ?_, ?_⟩
      · change t ≤ cost f xs + (2 * f i + 2) + 1
        omega
      · simpa only [program, first, initialControl, htail] using hr

theorem exact_alphabet (q₁ q₂ s w Q n p : Nat) :
    ∃ t ≤ 515 + 10 * 3 +
      2 * (q₁ + q₂ + 4*s + w + Q + n + p),
      ((advance (program slots))^[t])
        (⟨some (first slots), initialControl slots,
          input q₁ q₂ s w Q n p⟩ :
          TM2.Cfg (fun _ : Stack => Bool) (Label slots) (Control slots)) =
        ⟨none, initialControl slots,
          Function.update (input q₁ q₂ s w Q n p) 7
            (List.replicate
              (RecursiveSamplingExecution.alphabetCap s q₁ q₂ w Q n p) true)⟩ := by
  have hs : ∀ i : Source,
      input q₁ q₂ s w Q n p ⟨i.val, by omega⟩ =
        List.replicate (count q₁ q₂ s w Q n p i) true := by
    intro i; fin_cases i <;> rfl
  obtain ⟨t, ht, hr⟩ := run_slots (count q₁ q₂ s w Q n p)
    (input q₁ q₂ s w Q n p) hs rfl rfl slots
  refine ⟨t, ?_, ?_⟩
  · simp [cost, slots, count] at ht
    omega
  · have heq : 514 + sumCounts (count q₁ q₂ s w Q n p) slots =
        RecursiveSamplingExecution.alphabetCap s q₁ q₂ w Q n p := by
      simp [slots, sumCounts, count, RecursiveSamplingExecution.alphabetCap]
      omega
    simpa only [heq] using hr

#print axioms exact_alphabet
#print axioms program

end Paper2.SamplerAlphabetMachine
