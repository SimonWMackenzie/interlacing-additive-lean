import EthInapproximability.CurrentPaper.SourceCSPNextRowBridge
import EthInapproximability.CurrentPaper.BitMachineStackGrowth

/-! Noncircular all-word bound at the actual next-row parser output. -/

namespace EthInapproximability.CurrentPaper.SourceGenericNextParserGrowth

open Turing BitMachineEncoding BitMachineStackEmbedding
open scoped Classical

theorem parsed_word_growth {a q : ℕ}
    (B : SourceCSPNextRowBridge.Stack q → List Bool)
    (rest cap : List Bool)
    (V : SourceCSPRowQueryFrame.Stack q → List Bool)
    (t : ℕ)
    (v : SourceCSPRowController.Control × SourceCSPQueryBank.Control)
    (hrun :
      ((advance (SourceCSPNextRowBridge.parseProgram q a))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (.start 0 : SourceCSPRowController.Label q (a ^ q))),
          ((none, none), (((none, none), (none, false)), none)),
          SourceCSPNextRowBridge.resetResult B rest cap⟩ :
          TM2.Cfg (fun _ : SourceCSPNextRowBridge.Stack q => Bool) _ _) =
        ⟨none, v,
          SourceCSPNextRowBridge.parsedResult B rest cap V⟩)
    (x : SourceCSPRowQueryFrame.Stack q) :
    (V x).length ≤
      (SourceCSPRowQueryFrame.initial rest cap x).length +
        BitMachineStackGrowth.perStep
          (SourceCSPNextRowBridge.parseProgram q a) * t := by
  have hg := BitMachineStackGrowth.run_growth
    (SourceCSPNextRowBridge.parseProgram q a)
    (⟨some (BitMachineRawSequence.leftLabel
        (.start 0 : SourceCSPRowController.Label q (a ^ q))),
      ((none, none), (((none, none), (none, false)), none)),
      SourceCSPNextRowBridge.resetResult B rest cap⟩ :
      TM2.Cfg (fun _ : SourceCSPNextRowBridge.Stack q => Bool) _ _)
    t (SourceCSPNextRowBridge.rowEmbedding x)
  rw [hrun] at hg
  simpa only [SourceCSPNextRowBridge.parsedResult, bank_at,
    SourceCSPNextRowBridge.reset_row_initial] using hg

theorem initial_word_le {q H : ℕ} (rest cap : List Bool)
    (hrest : rest.length ≤ H) (hcap : cap.length ≤ H)
    (x : SourceCSPRowQueryFrame.Stack q) :
    (SourceCSPRowQueryFrame.initial rest cap x).length ≤ H := by
  cases x with
  | inl x => simp [SourceCSPRowQueryFrame.initial]
  | inr x =>
      fin_cases x <;>
        simp only [SourceCSPRowQueryFrame.initial, Sum.elim_inr] at * <;>
        aesop

def parseBudget (a q : ℕ) (rest : List Bool) (L : ℕ) : ℕ :=
  q * (2 * rest.length + 4) + 2 * a ^ q + 3 +
    q * (100 * (L + 1) ^ 2) + 2

def parseClockCoefficient (a q : ℕ) : ℕ :=
  106 * q + 2 * a ^ q + 5

theorem parseBudget_le {a q H L : ℕ} (rest : List Bool)
    (hrest : rest.length ≤ H) (hL : L ≤ H) :
    parseBudget a q rest L ≤ parseClockCoefficient a q * (H + 1) ^ 2 := by
  have hM : 1 ≤ (H + 1) ^ 2 := by nlinarith
  have hpart : 2 * rest.length + 4 ≤ 6 * (H + 1) ^ 2 := by
    nlinarith
  have hpart' := Nat.mul_le_mul_left q hpart
  have hsq := Nat.pow_le_pow_left (by omega : L + 1 ≤ H + 1) 2
  have hsq' := Nat.mul_le_mul_left (100 * q) hsq
  have hconst := Nat.mul_le_mul_left (2 * a ^ q + 5) hM
  dsimp [parseBudget, parseClockCoefficient]
  nlinarith

noncomputable def parseWordCoefficient (a q : ℕ) : ℕ :=
  1 + BitMachineStackGrowth.perStep
    (SourceCSPNextRowBridge.parseProgram q a) * parseClockCoefficient a q

theorem parsed_word_le_quadratic {a q H L : ℕ}
    (B : SourceCSPNextRowBridge.Stack q → List Bool)
    (rest cap : List Bool)
    (V : SourceCSPRowQueryFrame.Stack q → List Bool)
    (t : ℕ)
    (v : SourceCSPRowController.Control × SourceCSPQueryBank.Control)
    (hrest : rest.length ≤ H) (hcap : cap.length ≤ H) (hL : L ≤ H)
    (ht : t ≤ parseBudget a q rest L)
    (hrun :
      ((advance (SourceCSPNextRowBridge.parseProgram q a))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (.start 0 : SourceCSPRowController.Label q (a ^ q))),
          ((none, none), (((none, none), (none, false)), none)),
          SourceCSPNextRowBridge.resetResult B rest cap⟩ :
          TM2.Cfg (fun _ : SourceCSPNextRowBridge.Stack q => Bool) _ _) =
        ⟨none, v,
          SourceCSPNextRowBridge.parsedResult B rest cap V⟩)
    (x : SourceCSPRowQueryFrame.Stack q) :
    (V x).length ≤ parseWordCoefficient a q * (H + 1) ^ 2 := by
  have hg := parsed_word_growth B rest cap V t v hrun x
  have hi := initial_word_le rest cap hrest hcap x
  have hc := parseBudget_le (a := a) (q := q) rest hrest hL
  have htc : t ≤ parseClockCoefficient a q * (H + 1) ^ 2 := ht.trans hc
  have hp := Nat.mul_le_mul_left
    (BitMachineStackGrowth.perStep (SourceCSPNextRowBridge.parseProgram q a))
    htc
  have hH : H ≤ (H + 1) ^ 2 := by nlinarith
  dsimp [parseWordCoefficient]
  nlinarith

theorem parse_next_row_all_words {n a q H : ℕ}
    (next : SourceCSPCodec.Row n a q)
    (B : SourceCSPNextRowBridge.Stack q → List Bool)
    (rest tail : List Bool) (L : ℕ)
    (hn : 0 < n)
    (hrest : rest = SourceCSPCodec.rowFields next ++ tail)
    (hword : ∀ j : Fin q, (next.1 j).val.bits.length ≤ L)
    (hcapL : n - 1 ≤ L)
    (hrestLen : rest.length ≤ H) (hL : L ≤ H) :
    ∃ (t : ℕ)
      (v : SourceCSPRowController.Control × SourceCSPQueryBank.Control)
      (V : SourceCSPRowQueryFrame.Stack q → List Bool),
      t ≤ parseBudget a q rest L ∧
      ((advance (SourceCSPNextRowBridge.parseProgram q a))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (.start 0 : SourceCSPRowController.Label q (a ^ q))),
          ((none, none), (((none, none), (none, false)), none)),
          SourceCSPNextRowBridge.resetResult B rest
            (List.replicate (n - 1) true)⟩ :
          TM2.Cfg (fun _ : SourceCSPNextRowBridge.Stack q => Bool) _ _) =
        ⟨none, v,
          SourceCSPNextRowBridge.parsedResult B rest
            (List.replicate (n - 1) true) V⟩ ∧
      (∀ x, (V x).length ≤ parseWordCoefficient a q * (H + 1) ^ 2) ∧
      V (.inr 0) = tail ∧ V (.inr 4) = [true] ∧
      (∀ j : Fin q, V (.inl (j, 1)) =
        List.replicate (next.1 j).val true) ∧
      V (.inr 2) = true :: List.ofFn next.2 := by
  obtain ⟨t, v, V, ht, hrun, hsource, hstatus, hquery, htruth⟩ :=
    SourceCSPNextRowBridge.parse_next_row next B rest tail L
      hn hrest hword hcapL
  have hcap : (List.replicate (n - 1) true).length ≤ H := by
    simp only [List.length_replicate]
    omega
  refine ⟨t, v, V, ?_, hrun, ?_, hsource, hstatus, hquery, htruth⟩
  · simpa only [parseBudget, hrest] using ht
  · intro x
    exact parsed_word_le_quadratic B rest
      (List.replicate (n - 1) true) V t v
      hrestLen hcap hL (by simpa only [parseBudget, hrest] using ht)
      hrun x

theorem bank_words_le {K J : Type*} (ι : K ↪ J)
    (foreign : J → List Bool) (S : K → List Bool) (H : ℕ)
    (hf : ∀ j, (foreign j).length ≤ H)
    (hs : ∀ k, (S k).length ≤ H) (j : J) :
    (bank ι foreign S j).length ≤ H := by
  by_cases h : ∃ k, ι k = j
  · obtain ⟨k, hk⟩ := h
    subst j
    rw [bank_at]
    exact hs k
  · rw [bank_outside ι foreign S j h]
    exact hf j

theorem resetResult_words_le {q H : ℕ}
    (B : SourceCSPNextRowBridge.Stack q → List Bool)
    (rest cap : List Bool)
    (hB : ∀ x, (B x).length ≤ H)
    (hrest : rest.length ≤ H) (hcap : cap.length ≤ H)
    (x : SourceCSPNextRowBridge.Stack q) :
    (SourceCSPNextRowBridge.resetResult B rest cap x).length ≤ H := by
  apply bank_words_le SourceCSPNextRowBridge.resetEmbedding B _ H hB
  intro k
  cases k with
  | inl y => exact initial_word_le rest cap hrest hcap y
  | inr i =>
      exact hB (SourceCSPNextRowBridge.resetEmbedding (.inr i))

theorem parsedResult_words_le {q H P : ℕ}
    (B : SourceCSPNextRowBridge.Stack q → List Bool)
    (rest cap : List Bool)
    (V : SourceCSPRowQueryFrame.Stack q → List Bool)
    (hB : ∀ x, (B x).length ≤ H)
    (hrest : rest.length ≤ H) (hcap : cap.length ≤ H)
    (hV : ∀ x, (V x).length ≤ P)
    (x : SourceCSPNextRowBridge.Stack q) :
    (SourceCSPNextRowBridge.parsedResult B rest cap V x).length ≤ H + P := by
  apply bank_words_le SourceCSPNextRowBridge.rowEmbedding _ V (H + P)
  · intro y
    exact (resetResult_words_le B rest cap hB hrest hcap y).trans
      (Nat.le_add_right _ _)
  · intro y
    exact (hV y).trans (Nat.le_add_left _ _)

noncomputable def steppedWordCoefficient (a q : ℕ) : ℕ :=
  1 + parseWordCoefficient a q +
    2 * BitMachineStackGrowth.perStep
      (SourceCSPNextRowBridge.advanceProgram q)

theorem steppedResult_words_le {a q H : ℕ}
    (B : SourceCSPNextRowBridge.Stack q → List Bool)
    (rest cap : List Bool)
    (V : SourceCSPRowQueryFrame.Stack q → List Bool)
    (hB : ∀ x, (B x).length ≤ H)
    (hrest : rest.length ≤ H) (hcap : cap.length ≤ H)
    (hV : ∀ x, (V x).length ≤ parseWordCoefficient a q * (H + 1) ^ 2)
    (x : SourceCSPNextRowBridge.Stack q) :
    (SourceCSPNextRowBridge.steppedResult B rest cap V x).length ≤
      steppedWordCoefficient a q * (H + 1) ^ 2 := by
  have hrun := SourceCSPNextRowBridge.advance_run q
    (SourceCSPNextRowBridge.parsedResult B rest cap V)
  have hg := BitMachineStackGrowth.run_growth
    (SourceCSPNextRowBridge.advanceProgram q)
    (⟨some .push, (),
      SourceCSPNextRowBridge.parsedResult B rest cap V⟩ :
      TM2.Cfg (fun _ : SourceCSPNextRowBridge.Stack q => Bool) _ _)
    2 x
  rw [hrun] at hg
  have hp := parsedResult_words_le B rest cap V hB hrest hcap hV x
  have hM : 1 ≤ (H + 1) ^ 2 := by nlinarith
  have hH : H ≤ (H + 1) ^ 2 := by nlinarith
  have hstep := Nat.mul_le_mul_left
    (2 * BitMachineStackGrowth.perStep
      (SourceCSPNextRowBridge.advanceProgram q)) hM
  dsimp [SourceCSPNextRowBridge.steppedResult,
    steppedWordCoefficient] at *
  nlinarith

end EthInapproximability.CurrentPaper.SourceGenericNextParserGrowth
