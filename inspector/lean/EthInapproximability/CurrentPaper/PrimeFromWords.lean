import EthInapproximability.CurrentPaper.PrimeWordExact
import EthInapproximability.CurrentPaper.WeightedThresholdArithmetic

/-!
# Unary q, t, m to the unary chosen prime, exact exit bank

Lane owner:b-stage4-entry-program, segment 1 (prime operand word from words).

ONE fixed controller: the admitted threshold machine
`Paper2.WeightedThresholdArithmetic.program` (whole-bank exit; its output
cell 8 is placed directly on the prime search's candidate stack), then the
checked `PrimeWordExact.program`. Inputs: unary `q, t, m` only. Exit: the
same `q, t, m` words, the unary prime in the target cell, everything else
blank.
-/

namespace EthInapproximability.CurrentPaper.PrimeFromWords

open Turing BitMachineEncoding BitMachineStackEmbedding

noncomputable section

abbrev TStack := Paper2.WeightedThresholdArithmetic.Stack
abbrev Stack := PrimeWordExact.Stack ⊕ TStack

def candidate : Stack := .inl (.inl (.inr 0))

def thrMap (j : TStack) : Stack := if j = 8 then candidate else .inr j

def thrSlots : TStack ↪ Stack :=
  ⟨thrMap, by
    intro a b h
    unfold thrMap at h
    by_cases ha : a = 8 <;> by_cases hb : b = 8 <;> simp_all [candidate]⟩

def primeSlots : PrimeWordExact.Stack ↪ Stack := ⟨Sum.inl, Sum.inl_injective⟩

def thrProgram (l : _) := stackStmt thrSlots (Paper2.WeightedThresholdArithmetic.program l)
def primeProgram (l : PrimeWordExact.Label) :
    TM2.Stmt (fun _ : Stack => Bool) PrimeWordExact.Label PrimeWordExact.Control :=
  stackStmt primeSlots (PrimeWordExact.program l)

/-- The single fixed controller. -/
def program := BitMachineRawSequence.program thrProgram primeProgram
  PrimeWordExact.start Paper2.WeightedThresholdArithmetic.controlFinal
  PrimeWordExact.initControl

def start := BitMachineRawSequence.leftLabel (LB := PrimeWordExact.Label)
  Paper2.WeightedThresholdArithmetic.start

def startBank (q t m : ℕ) : Stack → List Bool :=
  Sum.elim (fun _ => []) (Paper2.WeightedThresholdArithmetic.initial q t m)

def exitBank (q t m : ℕ) : Stack → List Bool :=
  Sum.elim (PrimeWordExact.exitBank (PrimeSampler.prime q t m))
    (fun j => if j = 8 then [] else Paper2.WeightedThresholdArithmetic.finalBank q t m j)

def fromBound (q t m : ℕ) : ℕ :=
  Paper2.WeightedThresholdArithmetic.totalTime q t m +
    PrimeWordExact.wordBound (PrimeSampler.threshold q t m) + 1

theorem thr_start (q t m : ℕ) :
    bank thrSlots (startBank q t m) (Paper2.WeightedThresholdArithmetic.initial q t m) =
      startBank q t m := by
  apply bank_eq_self
  intro k
  by_cases hk : k = 8
  · subst hk
    simp [thrSlots, thrMap, candidate, startBank, Paper2.WeightedThresholdArithmetic.initial]
  · simp [thrSlots, thrMap, hk, startBank]

theorem mid_bank (q t m : ℕ) :
    bank thrSlots (startBank q t m) (Paper2.WeightedThresholdArithmetic.finalBank q t m) =
      Sum.elim (PrimeWordExact.startBank (PrimeSampler.threshold q t m))
        (fun j => if j = 8 then [] else Paper2.WeightedThresholdArithmetic.finalBank q t m j) := by
  funext k
  rcases k with k | j
  · rcases k with (k | k) | k
    · rw [bank_outside]
      · rfl
      · rintro ⟨i, hi⟩
        simp only [thrSlots, thrMap, Function.Embedding.coeFn_mk] at hi
        split_ifs at hi
        simp [candidate] at hi
    · by_cases h0 : k = 0
      · subst h0
        have he : thrSlots 8 = Sum.inl (Sum.inl (Sum.inr 0)) := by
          simp [thrSlots, thrMap, candidate]
        have hb := bank_at thrSlots (startBank q t m)
          (Paper2.WeightedThresholdArithmetic.finalBank q t m) 8
        rw [he] at hb
        rw [hb]
        simp [PrimeWordExact.startBank, ChosenPrimeRaw.initial, PrimeSamplerSearch.adminCfg,
          PrimeSamplerSearch.cfg, Paper2.WeightedThresholdArithmetic.finalBank,
          Paper2.WeightedThresholdArithmetic.unary]
      · rw [bank_outside]
        · fin_cases k <;>
            simp_all [startBank, PrimeWordExact.startBank, ChosenPrimeRaw.initial,
              PrimeSamplerSearch.adminCfg, PrimeSamplerSearch.cfg]
        · rintro ⟨i, hi⟩
          simp only [thrSlots, thrMap, Function.Embedding.coeFn_mk] at hi
          split_ifs at hi
          · simp only [candidate, Sum.inl.injEq, Sum.inr.injEq] at hi
            exact h0 hi.symm
    · rw [bank_outside]
      · rfl
      · rintro ⟨i, hi⟩
        simp only [thrSlots, thrMap, Function.Embedding.coeFn_mk] at hi
        split_ifs at hi
        simp [candidate] at hi
  · by_cases hj : j = 8
    · subst hj
      rw [bank_outside]
      · simp [startBank, Paper2.WeightedThresholdArithmetic.initial]
      · rintro ⟨i, hi⟩
        simp only [thrSlots, thrMap, Function.Embedding.coeFn_mk] at hi
        split_ifs at hi with h8
        · simp [candidate] at hi
        · simp only [Sum.inr.injEq] at hi
          exact h8 hi
    · have he : thrSlots j = Sum.inr j := by simp [thrSlots, thrMap, hj]
      have hb := bank_at thrSlots (startBank q t m)
        (Paper2.WeightedThresholdArithmetic.finalBank q t m) j
      rw [he] at hb
      rw [hb]
      simp [hj]

theorem prime_from_words (q t m : ℕ) :
    ∃ u ≤ fromBound q t m,
      ((advance program)^[u])
        (⟨some start, (Paper2.WeightedThresholdArithmetic.controlFinal,
            PrimeWordExact.initControl), startBank q t m⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, (Paper2.WeightedThresholdArithmetic.controlFinal,
            PrimeWordExact.initControl), exitBank q t m⟩ := by
  obtain ⟨u1, hu1, h1⟩ := Paper2.WeightedThresholdArithmetic.threshold_run q t m
  have hA0 := BitMachineStackRun.run thrSlots (startBank q t m)
    Paper2.WeightedThresholdArithmetic.program
    ⟨some Paper2.WeightedThresholdArithmetic.start,
      Paper2.WeightedThresholdArithmetic.controlFinal,
      Paper2.WeightedThresholdArithmetic.initial q t m⟩ u1
  rw [h1] at hA0
  simp only [stackCfg, thr_start, mid_bank] at hA0
  obtain ⟨u2, hu2, h2⟩ := PrimeWordExact.prime_word q t m
  let B1 : Stack → List Bool :=
    Sum.elim (PrimeWordExact.startBank (PrimeSampler.threshold q t m))
      (fun j => if j = 8 then [] else Paper2.WeightedThresholdArithmetic.finalBank q t m j)
  have hB0 := BitMachineStackRun.run primeSlots B1 PrimeWordExact.program
    ⟨some PrimeWordExact.start, PrimeWordExact.initControl,
      PrimeWordExact.startBank (PrimeSampler.threshold q t m)⟩ u2
  rw [h2] at hB0
  have hs : bank primeSlots B1 (PrimeWordExact.startBank (PrimeSampler.threshold q t m)) = B1 := by
    apply bank_eq_self
    intro k
    rfl
  have hf : bank primeSlots B1 (PrimeWordExact.exitBank (PrimeSampler.prime q t m)) =
      exitBank q t m := by
    funext k
    rcases k with k | j
    · exact bank_at primeSlots B1 _ k
    · rw [bank_outside]
      · rfl
      · rintro ⟨i, hi⟩
        cases hi
  simp only [stackCfg, hs, hf] at hB0
  obtain ⟨u, hu, hrun⟩ := BitMachineRawSequence.runs thrProgram primeProgram
    Paper2.WeightedThresholdArithmetic.start PrimeWordExact.start
    Paper2.WeightedThresholdArithmetic.controlFinal
    Paper2.WeightedThresholdArithmetic.controlFinal
    PrimeWordExact.initControl PrimeWordExact.initControl
    (startBank q t m) B1 (exitBank q t m) u1 u2 hA0 hB0
  refine ⟨u, ?_, hrun⟩
  unfold fromBound
  omega

theorem exit_slots (q t m : ℕ) :
    exitBank q t m (.inl (.inr 0)) = List.replicate (PrimeSampler.prime q t m) true ∧
    exitBank q t m (.inr 0) = List.replicate q true ∧
    exitBank q t m (.inr 1) = List.replicate t true ∧
    exitBank q t m (.inr 2) = List.replicate m true ∧
    (∀ k, exitBank q t m (.inl (.inl k)) = []) ∧
    exitBank q t m (.inl (.inr 1)) = [] ∧
    (∀ j : TStack, j ≠ 0 → j ≠ 1 → j ≠ 2 → exitBank q t m (.inr j) = []) := by
  obtain ⟨h0, h1, h2, h8, hr⟩ := Paper2.WeightedThresholdArithmetic.final_slots q t m
  refine ⟨rfl, ?_, ?_, ?_, fun _ => rfl, rfl, ?_⟩
  · simpa [exitBank] using h0
  · simpa [exitBank] using h1
  · simpa [exitBank] using h2
  · intro j hj0 hj1 hj2
    by_cases hj8 : j = 8
    · simp [exitBank, hj8]
    · simp [exitBank, hj8, hr j hj0 hj1 hj2 hj8]

#print axioms mid_bank
#print axioms prime_from_words
#print axioms exit_slots

end

end EthInapproximability.CurrentPaper.PrimeFromWords
