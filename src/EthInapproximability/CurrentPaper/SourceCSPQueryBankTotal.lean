import EthInapproximability.CurrentPaper.SourceCSPQueryBankValid

/-!
# Total range validation for a fixed bank of raw canonical query words

The words may denote labels outside the vertex range. This is an actual
finite-control machine run: the first failed bounded-unary comparison writes
`false` and halts; otherwise every query is checked and `true` is written.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPQueryBank

open Turing BitMachineEncoding BitMachineStackEmbedding

structure RawReady {q : Nat} (query : Fin q → List Bool) (cap : List Bool)
    (i : Fin (q + 1)) (S : Stack q → List Bool) : Prop where
  cap_eq : S (.inr 0) = cap
  status : S (.inr 1) = []
  query_eq : ∀ j : Fin q, S (.inl (j, 0)) = query j
  future : ∀ j : Fin q, i.val ≤ j.val →
    S (.inl (j, 1)) = [] ∧ S (.inl (j, 2)) = [] ∧
      S (.inl (j, 3)) = [] ∧ S (.inl (j, 4)) = []

theorem raw_ready_initial {q : Nat} (query : Fin q → List Bool)
    (cap : List Bool) : RawReady query cap 0 (startBank query cap) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro j; rfl
  · intro j hj; exact ⟨rfl, rfl, rfl, rfl⟩

theorem raw_selected_ready {q : Nat} {query : Fin q → List Bool}
    {cap : List Bool} {i : Fin (q + 1)} {S : Stack q → List Bool}
    (hr : RawReady query cap i S) (hi : i.val < q) :
    ∀ k : SourceCSPQueryRange.Stack,
      S (select ⟨i.val, hi⟩ k) =
        SourceCSPQueryRange.contents (query ⟨i.val, hi⟩) cap [] [] [] [] k := by
  let j : Fin q := ⟨i.val, hi⟩
  have hf := hr.future j (by simp [j])
  intro k
  fin_cases k
  · simpa only [select, j, SourceCSPQueryRange.contents] using hr.query_eq j
  · simpa only [select, j, SourceCSPQueryRange.contents] using hr.cap_eq
  · simpa only [select, j, SourceCSPQueryRange.contents] using hf.2.1
  · simpa only [select, j, SourceCSPQueryRange.contents] using hf.2.2.1
  · simpa only [select, j, SourceCSPQueryRange.contents] using hf.2.2.2
  · simpa only [select, j, SourceCSPQueryRange.contents] using hf.1

/-- A literal call to the selected range subroutine, including the start
transition, reaches the flag dispatcher with the exact computed flag. -/
theorem raw_one_call {q : Nat} (query : Fin q → List Bool) (cap : List Bool)
    (i : Fin (q + 1)) (hi : i.val < q)
    (S : Stack q → List Bool) (hr : RawReady query cap i S) (v : Control) :
    ∃ (t : Nat) (d : SourceCSPQueryRange.Config), t ≤ 2 * (query ⟨i.val, hi⟩).length + 2 +
        (2 * cap.length + 2) + 1 +
        (cap.length + 1) * (4 * (query ⟨i.val, hi⟩).length + 5) + 2 ∧
      run t (⟨some (.start i), v, S⟩ : Config q) =
        ⟨some (.after ⟨i.val, hi⟩), (d.var, none),
          bank (select ⟨i.val, hi⟩) S d.stk⟩ ∧
      d.stk 0 = query ⟨i.val, hi⟩ ∧ d.stk 1 = cap ∧
      d.stk 5 = ProtocolBoundedUnary.result (query ⟨i.val, hi⟩) cap [] := by
  let j : Fin q := ⟨i.val, hi⟩
  obtain ⟨t, d, ht, hrun, hh, hq, hc, hs, ho⟩ :=
    one_query_framed j (query j) cap S (raw_selected_ready hr hi)
  have hcall : run t (⟨some (.check j
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))),
      (((none, none), (none, false)), none), S⟩ : Config q) =
      ⟨some (.after j), (d.var, none), bank (select j) S d.stk⟩ := by
    rw [hrun]
    simp [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg, hh]
  refine ⟨t + 1, d, ?_, ?_, hq, hc, ho⟩
  · dsimp [j] at ht
    omega
  · rw [show t + 1 = 1 + t by omega, run_add, run_one,
      start_step i hi v S, hcall]

theorem raw_success {q : Nat} (query : Fin q → List Bool) (cap : List Bool)
    (i : Fin (q + 1)) (hi : i.val < q)
    (S : Stack q → List Bool) (hr : RawReady query cap i S) (v : Control)
    (hgood : EncodedCommunication.bitsValue (query ⟨i.val, hi⟩) ≤ cap.length) :
    ∃ t v' S',
      t ≤ 2 * (query ⟨i.val, hi⟩).length + 2 +
        (2 * cap.length + 2) + 1 +
        (cap.length + 1) * (4 * (query ⟨i.val, hi⟩).length + 5) + 3 ∧
      run t (⟨some (.start i), v, S⟩ : Config q) =
        ⟨some (.start ⟨i.val + 1, by omega⟩), v', S'⟩ ∧
      RawReady query cap ⟨i.val + 1, by omega⟩ S' := by
  let j : Fin q := ⟨i.val, hi⟩
  obtain ⟨t, d, ht, hrun, hq, hc, ho⟩ :=
    raw_one_call query cap i hi S hr v
  let T := bank (select j) S d.stk
  let U := Function.update T (.inl (j, 1))
    (List.replicate (EncodedCommunication.bitsValue (query j)) true)
  have hval : T (.inl (j, 1)) =
      true :: List.replicate (EncodedCommunication.bitsValue (query j)) true := by
    change bank (select j) S d.stk (select j 5) = _
    rw [bank_at, ho]
    dsimp only [j]
    simp [ProtocolBoundedUnary.result, hgood]
  have hstep := after_success j (d.var, none) T _ hval
  refine ⟨t + 1, (d.var, some true), U, by omega, ?_, ?_⟩
  · rw [run_add, hrun, run_one, hstep]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · change U (.inr 0) = _
      rw [show U (.inr 0) = T (.inr 0) from Function.update_of_ne (by simp) _ _]
      change bank (select j) S d.stk (select j 1) = _
      rw [bank_at]
      exact hc
    · change U (.inr 1) = _
      rw [show U (.inr 1) = T (.inr 1) from Function.update_of_ne (by simp) _ _]
      exact (foreign_status j S d.stk).trans hr.status
    · intro k
      rw [show U (.inl (k, 0)) = T (.inl (k, 0)) from
        Function.update_of_ne (by simp) _ _]
      by_cases hk : k = j
      · subst k
        change bank (select j) S d.stk (select j 0) = _
        rw [bank_at]
        exact hq
      · change bank (select j) S d.stk (.inl (k, 0)) = _
        rw [foreign_query j k (Ne.symm hk) S d.stk 0]
        exact hr.query_eq k
    · intro k hk
      have hkj : k ≠ j := by
        intro he
        have hv := congrArg Fin.val he
        change i.val + 1 ≤ k.val at hk
        dsimp [j] at hv
        omega
      have hfi : i.val ≤ k.val := by
        change i.val + 1 ≤ k.val at hk
        omega
      have hf := hr.future k hfi
      have hne : (.inl (k, (1 : Fin 5)) : Stack q) ≠ .inl (j, 1) := by simp [hkj]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [show U (.inl (k, 1)) = T (.inl (k, 1)) from
          Function.update_of_ne hne _ _]
        change bank (select j) S d.stk (.inl (k, 1)) = _
        rw [foreign_query j k (Ne.symm hkj) S d.stk 1]
        exact hf.1
      · rw [show U (.inl (k, 2)) = T (.inl (k, 2)) from
          Function.update_of_ne (by simp) _ _]
        change bank (select j) S d.stk (.inl (k, 2)) = _
        rw [foreign_query j k (Ne.symm hkj) S d.stk 2]
        exact hf.2.1
      · rw [show U (.inl (k, 3)) = T (.inl (k, 3)) from
          Function.update_of_ne (by simp) _ _]
        change bank (select j) S d.stk (.inl (k, 3)) = _
        rw [foreign_query j k (Ne.symm hkj) S d.stk 3]
        exact hf.2.2.1
      · rw [show U (.inl (k, 4)) = T (.inl (k, 4)) from
          Function.update_of_ne (by simp) _ _]
        change bank (select j) S d.stk (.inl (k, 4)) = _
        rw [foreign_query j k (Ne.symm hkj) S d.stk 4]
        exact hf.2.2.2

theorem raw_failure {q : Nat} (query : Fin q → List Bool) (cap : List Bool)
    (i : Fin (q + 1)) (hi : i.val < q)
    (S : Stack q → List Bool) (hr : RawReady query cap i S) (v : Control)
    (hbad : ¬ EncodedCommunication.bitsValue (query ⟨i.val, hi⟩) ≤ cap.length) :
    ∃ t v' S',
      t ≤ 2 * (query ⟨i.val, hi⟩).length + 2 +
        (2 * cap.length + 2) + 1 +
        (cap.length + 1) * (4 * (query ⟨i.val, hi⟩).length + 5) + 3 ∧
      run t (⟨some (.start i), v, S⟩ : Config q) = ⟨none, v', S'⟩ ∧
      S' (.inr 1) = [false] := by
  let j : Fin q := ⟨i.val, hi⟩
  obtain ⟨t, d, ht, hrun, hq, hc, ho⟩ :=
    raw_one_call query cap i hi S hr v
  let T := bank (select j) S d.stk
  let U := Function.update
    (Function.update T (.inl (j, 1))
      (List.replicate cap.length true)) (.inr 1) (false :: T (.inr 1))
  have hval : T (.inl (j, 1)) = false :: List.replicate cap.length true := by
    change bank (select j) S d.stk (select j 5) = _
    rw [bank_at, ho]
    have hmin : cap.length ≤ EncodedCommunication.bitsValue
        (query ⟨i.val, hi⟩) := by omega
    simp [ProtocolBoundedUnary.result, hbad, hmin]
  have hstep := after_failure j (d.var, none) T _ hval
  refine ⟨t + 1, (d.var, some false), U, by omega, ?_, ?_⟩
  · rw [run_add, hrun, run_one, hstep]
  · change Function.update
      (Function.update T (.inl (j, 1)) (List.replicate cap.length true))
        (.inr 1) (false :: T (.inr 1)) (.inr 1) = _
    rw [Function.update_self]
    change false :: bank (select j) S d.stk (.inr 1) = [false]
    rw [foreign_status j S d.stk, hr.status]

/-- Every raw fixed-bank input halts, including out-of-range words. The
machine's Boolean answer is exactly the conjunction of range comparisons. -/
theorem raw_total_from {q : Nat} (query : Fin q → List Bool) (cap : List Bool)
    (L : Nat) (hword : ∀ j : Fin q, (query j).length ≤ L)
    (hcap : cap.length ≤ L) (i : Fin (q + 1))
    (S : Stack q → List Bool) (hr : RawReady query cap i S) (v : Control) :
    ∃ t v' S' b, t ≤ (q - i.val) * (100 * (L + 1) ^ 2) + 1 ∧
      run t (⟨some (.start i), v, S⟩ : Config q) = ⟨none, v', S'⟩ ∧
      S' (.inr 1) = [b] ∧
      (b = true ↔ ∀ j : Fin q, i.val ≤ j.val →
        EncodedCommunication.bitsValue (query j) ≤ cap.length) := by
  by_cases hi : i.val < q
  · let j : Fin q := ⟨i.val, hi⟩
    by_cases hg : EncodedCommunication.bitsValue (query j) ≤ cap.length
    · obtain ⟨t, v₁, S₁, ht, hrun, hs⟩ := raw_success query cap i hi S hr v hg
      obtain ⟨u, v₂, S₂, b, hu, hrun₂, hstatus, hb⟩ :=
        raw_total_from query cap L hword hcap
          ⟨i.val + 1, by omega⟩ S₁ hs v₁
      refine ⟨t + u, v₂, S₂, b, ?_, ?_, hstatus, ?_⟩
      · have htb := ht.trans (step_quadratic _ _ L (hword j) hcap)
        have hu' : u ≤ (q - (i.val + 1)) * (100 * (L + 1) ^ 2) + 1 := by
          simpa only [] using hu
        have hc : q - i.val = (q - (i.val + 1)) + 1 := by omega
        calc
          t + u ≤ 100 * (L + 1) ^ 2 +
              ((q - (i.val + 1)) * (100 * (L + 1) ^ 2) + 1) := by omega
          _ = (q - i.val) * (100 * (L + 1) ^ 2) + 1 := by rw [hc]; ring
      · rw [run_add, hrun]
        exact hrun₂
      · rw [hb]
        constructor
        · intro hall k hk
          by_cases he : k = j
          · subst k; exact hg
          · apply hall k
            have hne : k.val ≠ i.val := by
              intro hv
              exact he (Fin.ext hv)
            change i.val + 1 ≤ k.val
            omega
        · intro hall k hk
          apply hall k
          change i.val + 1 ≤ k.val at hk
          omega
    · obtain ⟨t, v₁, S₁, ht, hrun, hstatus⟩ :=
        raw_failure query cap i hi S hr v hg
      refine ⟨t, v₁, S₁, false, ?_, hrun, hstatus, ?_⟩
      · exact ht.trans (by
          have htb := step_quadratic _ _ L (hword j) hcap
          have : 0 < q - i.val := by omega
          nlinarith)
      · simp only [Bool.false_eq_true, false_iff]
        intro hall
        exact hg (hall j (by simp [j]))
  · have he : i = Fin.last q := by
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    subst i
    refine ⟨1, v, Function.update S (.inr 1) (true :: S (.inr 1)), true,
      by simp, ?_, ?_, ?_⟩
    · rw [run_one, finish_step]
    · rw [Function.update_self, hr.status]
    · simp only [true_iff]
      intro k hk
      have := k.isLt
      simp only [Fin.val_last] at hk
      omega
termination_by q - i.val

theorem raw_total {q : Nat} (query : Fin q → List Bool) (cap : List Bool)
    (L : Nat) (hword : ∀ j : Fin q, (query j).length ≤ L)
    (hcap : cap.length ≤ L) :
    ∃ t v S b, t ≤ q * (100 * (L + 1) ^ 2) + 1 ∧
      run t (⟨some (.start 0), (((none, none), (none, false)), none),
        startBank query cap⟩ : Config q) = ⟨none, v, S⟩ ∧
      S (.inr 1) = [b] ∧
      (b = true ↔ ∀ j : Fin q,
        EncodedCommunication.bitsValue (query j) ≤ cap.length) := by
  simpa only [Fin.val_zero, Nat.zero_le, forall_const] using
    raw_total_from query cap L hword hcap 0 (startBank query cap)
      (raw_ready_initial query cap) _

end EthInapproximability.CurrentPaper.SourceCSPQueryBank
