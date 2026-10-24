import EthInapproximability.CurrentPaper.SourceOriginalListPacketizerCounter

/-! Exact reusable bank shape at the binary-counter loop head. -/

namespace EthInapproximability.CurrentPaper.SourceOriginalListPacketizer

open EncodedCommunication

noncomputable section

def readyBank (n : ℕ) (source q accumulator : List Bool) : Stack → List Bool :=
  fun k => if k = .inl SourceOriginalPacketFraming.nStack then
    List.replicate n true
  else if k = .inr 0 then source
  else if k = .inr 2 then q
  else if k = .inr 4 then accumulator
  else []

theorem readyBank_n (n : ℕ) (source q accumulator : List Bool) :
    readyBank n source q accumulator (.inl SourceOriginalPacketFraming.nStack) =
      List.replicate n true := by simp [readyBank]

theorem readyBank_source (n : ℕ) (source q accumulator : List Bool) :
    readyBank n source q accumulator (.inr 0) = source := by
  simp [readyBank]

theorem readyBank_count (n : ℕ) (source q accumulator : List Bool) :
    readyBank n source q accumulator (.inr 2) = q := by
  simp [readyBank]

theorem readyBank_accumulator (n : ℕ) (source q accumulator : List Bool) :
    readyBank n source q accumulator (.inr 4) = accumulator := by
  simp [readyBank]

theorem readyBank_other_frame (n : ℕ) (source q accumulator : List Bool)
    (k : FrameStack) (hk : k ≠ SourceOriginalPacketFraming.nStack) :
    readyBank n source q accumulator (.inl k) = [] := by
  simp [readyBank, hk]

theorem readyBank_other_aux (n : ℕ) (source q accumulator : List Bool)
    (k : Fin 10) (h0 : k ≠ 0) (h2 : k ≠ 2) (h4 : k ≠ 4) :
    readyBank n source q accumulator (.inr k) = [] := by
  simp [readyBank, h0, h2, h4]

theorem initialized_eq_ready (n : ℕ) (xs : List (List Bool)) :
    initBanks n (SourceListEncoding.encode xs)
      {input := SourceListEncoding.fields xs,
       count := xs.length.bits,
       output := (natField xs.length).reverse} =
    readyBank n (SourceListEncoding.fields xs) xs.length.bits
      (natField xs.length).reverse := by
  funext k
  cases k with
  | inl k =>
      have hk : ¬ ∃ i : SourceListMachineInitialize.Stack, initStack i =
          (.inl k : Stack) := by
        rintro ⟨i,hi⟩
        fin_cases i <;> cases hi
      rw [initBanks, BitMachineStackEmbedding.bank_outside initStack _ _ _ hk]
      by_cases hnk : k = SourceOriginalPacketFraming.nStack
      · subst k
        simp [startBank, readyBank]
      · simp [startBank, readyBank, hnk]
  | inr k =>
      fin_cases k
      · change (initBanks n (SourceListEncoding.encode xs) _)
          (initStack 0) = _
        rw [initBanks, BitMachineStackEmbedding.bank_at]
        rfl
      · change (initBanks n (SourceListEncoding.encode xs) _)
          (initStack 1) = _
        rw [initBanks, BitMachineStackEmbedding.bank_at]
        rfl
      · change (initBanks n (SourceListEncoding.encode xs) _)
          (initStack 2) = _
        rw [initBanks, BitMachineStackEmbedding.bank_at]
        rfl
      · change (initBanks n (SourceListEncoding.encode xs) _)
          (initStack 3) = _
        rw [initBanks, BitMachineStackEmbedding.bank_at]
        rfl
      · change (initBanks n (SourceListEncoding.encode xs) _)
          (initStack 4) = _
        rw [initBanks, BitMachineStackEmbedding.bank_at]
        rfl
      all_goals
        rw [initBanks, BitMachineStackEmbedding.bank_outside]
        · simp [startBank, readyBank]
        · rintro ⟨i,hi⟩
          fin_cases i <;> cases hi

end

end EthInapproximability.CurrentPaper.SourceOriginalListPacketizer
