import EthInapproximability.CurrentPaper.SourceCSPQueryBank

/-!
# Valid-row invariant for physical query-range validation

The controller consumes one fixed-arity row's already parsed canonical query
words. At each stage it preserves the original words and vertex cap; previous
unary query outputs are exact, and all future work banks are untouched.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPQueryBank

open Turing BitMachineEncoding BitMachineStackEmbedding

structure Ready {n a q : Nat} (row : SourceCSPCodec.Row n a q)
    (i : Fin (q + 1)) (S : Stack q → List Bool) : Prop where
  cap : S (.inr 0) = List.replicate (n - 1) true
  status : S (.inr 1) = []
  query : ∀ j : Fin q, S (.inl (j, 0)) = (row.1 j).val.bits
  previous : ∀ j : Fin q, j.val < i.val →
    S (.inl (j, 1)) = List.replicate (row.1 j).val true
  future : ∀ j : Fin q, i.val ≤ j.val →
    S (.inl (j, 1)) = [] ∧ S (.inl (j, 2)) = [] ∧
      S (.inl (j, 3)) = [] ∧ S (.inl (j, 4)) = []

theorem ready_initial {n a q : Nat} (row : SourceCSPCodec.Row n a q) :
    Ready row 0 (startBank (fun j => (row.1 j).val.bits)
      (List.replicate (n - 1) true)) := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · intro j; rfl
  · intro j hj; simp at hj
  · intro j hj; exact ⟨rfl, rfl, rfl, rfl⟩

theorem selected_ready {n a q : Nat} {row : SourceCSPCodec.Row n a q}
    {i : Fin (q + 1)} {S : Stack q → List Bool} (hr : Ready row i S)
    (hi : i.val < q) :
    ∀ k : SourceCSPQueryRange.Stack,
      S (select ⟨i.val, hi⟩ k) =
        SourceCSPQueryRange.contents (row.1 ⟨i.val, hi⟩).val.bits
          (List.replicate (n - 1) true) [] [] [] [] k := by
  let j : Fin q := ⟨i.val, hi⟩
  have hf := hr.future j (by simp [j])
  intro k
  fin_cases k
  · simpa only [select, j, SourceCSPQueryRange.contents] using hr.query j
  · simpa only [select, j, SourceCSPQueryRange.contents] using hr.cap
  · simpa only [select, j, SourceCSPQueryRange.contents] using hf.2.1
  · simpa only [select, j, SourceCSPQueryRange.contents] using hf.2.2.1
  · simpa only [select, j, SourceCSPQueryRange.contents] using hf.2.2.2
  · simpa only [select, j, SourceCSPQueryRange.contents] using hf.1

theorem foreign_query {q : Nat} (i j : Fin q) (hij : i ≠ j)
    (S : Stack q → List Bool) (T : SourceCSPQueryRange.Stack → List Bool)
    (k : Fin 5) :
    bank (select i) S T (.inl (j, k)) = S (.inl (j, k)) := by
  apply bank_outside
  intro ⟨r, h⟩
  fin_cases r <;> simp [select, hij] at h

theorem foreign_status {q : Nat} (i : Fin q)
    (S : Stack q → List Bool) (T : SourceCSPQueryRange.Stack → List Bool) :
    bank (select i) S T (.inr 1) = S (.inr 1) := by
  apply bank_outside
  intro ⟨r, h⟩
  fin_cases r <;> simp [select] at h

theorem advance_valid {n a q : Nat} (row : SourceCSPCodec.Row n a q)
    (hn : 0 < n) (i : Fin (q + 1)) (hi : i.val < q)
    (S : Stack q → List Bool) (hr : Ready row i S) (v : Control) :
    ∃ t v' S',
      t ≤ 2 * (row.1 ⟨i.val, hi⟩).val.bits.length + 2 +
        (2 * (n - 1) + 2) + 1 +
        (n - 1 + 1) * (4 * (row.1 ⟨i.val, hi⟩).val.bits.length + 5) + 3 ∧
      run t (⟨some (.start i), v, S⟩ : Config q) =
        ⟨some (.start ⟨i.val + 1, by omega⟩), v', S'⟩ ∧
      Ready row ⟨i.val + 1, by omega⟩ S' := by
  let j : Fin q := ⟨i.val, hi⟩
  let word := (row.1 j).val.bits
  let cap := List.replicate (n - 1) true
  obtain ⟨t, d, ht, hrun, hh, hq, hc, hs, ho⟩ :=
    one_query_framed j word cap S (selected_ready hr hi)
  let T := bank (select j) S d.stk
  let U := Function.update T (.inl (j, 1)) (List.replicate (row.1 j).val true)
  have hval : T (.inl (j, 1)) = true :: List.replicate (row.1 j).val true := by
    change bank (select j) S d.stk (select j 5) = _
    rw [bank_at, ho, SourceCSPQueryRange.result_at_vertices _ _ n hn,
      EncodedCommunication.bitsValue_bits, if_pos (row.1 j).isLt]
    simp
  have hcall : run t (⟨some (.check j
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))),
      (((none, none), (none, false)), none), S⟩ : Config q) =
      ⟨some (.after j), (d.var, none), T⟩ := by
    rw [hrun]
    simp [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg, hh, T]
  have hstep := after_success j (d.var, none) T
    (List.replicate (row.1 j).val true) hval
  refine ⟨t + 2, (d.var, some true), U, ?_, ?_, ?_⟩
  · dsimp [word, cap, j] at ht
    simp only [List.length_replicate] at ht
    omega
  · rw [show t + 2 = 1 + t + 1 by omega,
      run_add, run_add]
    rw [show run 1 (⟨some (.start i), v, S⟩ : Config q) = _ from
      start_step i hi v S, hcall, run_one, hstep]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · change U (.inr 0) = _
      rw [show U (.inr 0) = T (.inr 0) from Function.update_of_ne (by simp) _ _]
      change bank (select j) S d.stk (select j 1) = _
      rw [bank_at]
      exact hc
    · change U (.inr 1) = _
      rw [show U (.inr 1) = T (.inr 1) from Function.update_of_ne (by simp) _ _]
      exact (foreign_status j S d.stk).trans hr.status
    · intro k
      have hne : (.inl (k, (0 : Fin 5)) : Stack q) ≠ .inl (j, 1) := by simp
      rw [show U (.inl (k, 0)) = T (.inl (k, 0)) from
        Function.update_of_ne hne _ _]
      by_cases hk : k = j
      · subst k
        change bank (select j) S d.stk (select j 0) = _
        rw [bank_at]
        exact hq
      · change bank (select j) S d.stk (.inl (k, 0)) = _
        rw [foreign_query j k (Ne.symm hk) S d.stk 0]
        exact hr.query k
    · intro k hk
      by_cases hkj : k = j
      · subst k
        exact Function.update_self _ _ _
      · have hne : (.inl (k, (1 : Fin 5)) : Stack q) ≠ .inl (j, 1) := by
          simp [hkj]
        rw [show U (.inl (k, 1)) = T (.inl (k, 1)) from
          Function.update_of_ne hne _ _]
        change bank (select j) S d.stk (.inl (k, 1)) = _
        rw [foreign_query j k (Ne.symm hkj) S d.stk 1]
        have hneq : k.val ≠ i.val := by
          intro he
          exact hkj (Fin.ext he)
        have hlt : k.val < i.val := by
          change k.val < i.val + 1 at hk
          omega
        exact hr.previous k hlt
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
      have hne : (.inl (k, (1 : Fin 5)) : Stack q) ≠ .inl (j, 1) := by
        simp [hkj]
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

theorem step_quadratic (x y L : Nat) (hx : x ≤ L) (hy : y ≤ L) :
    2 * x + 2 + (2 * y + 2) + 1 + (y + 1) * (4 * x + 5) + 3 ≤
      100 * (L + 1) ^ 2 := by
  have hm : (y + 1) * (4 * x + 5) ≤ (L + 1) * (4 * L + 5) :=
    Nat.mul_le_mul (by omega) (by omega)
  nlinarith [Nat.zero_le (L * L)]

/-- All fixed-arity canonical query positions are physically validated in
order. The bound is uniform in their supplied word lengths and the cap. -/
theorem run_until_end {n a q : Nat} (row : SourceCSPCodec.Row n a q)
    (hn : 0 < n) (L : Nat)
    (hword : ∀ j : Fin q, (row.1 j).val.bits.length ≤ L)
    (hcap : n - 1 ≤ L) (i : Fin (q + 1))
    (S : Stack q → List Bool) (hr : Ready row i S) (v : Control) :
    ∃ t v' S', t ≤ (q - i.val) * (100 * (L + 1) ^ 2) ∧
      run t (⟨some (.start i), v, S⟩ : Config q) =
        ⟨some (.start (Fin.last q)), v', S'⟩ ∧
      Ready row (Fin.last q) S' := by
  by_cases hi : i.val < q
  · let next : Fin (q + 1) := ⟨i.val + 1, by omega⟩
    obtain ⟨t₁, v₁, S₁, ht₁, hr₁, hs₁⟩ := advance_valid row hn i hi S hr v
    obtain ⟨t₂, v₂, S₂, ht₂, hr₂, hs₂⟩ :=
      run_until_end row hn L hword hcap next S₁ hs₁ v₁
    have hb : t₁ ≤ 100 * (L + 1) ^ 2 :=
      ht₁.trans (step_quadratic _ _ L (hword ⟨i.val, hi⟩) hcap)
    refine ⟨t₁ + t₂, v₂, S₂, ?_, ?_, hs₂⟩
    · have hc : q - i.val = (q - (i.val + 1)) + 1 := by omega
      calc
        t₁ + t₂ ≤ 100 * (L + 1) ^ 2 +
            (q - (i.val + 1)) * (100 * (L + 1) ^ 2) := by
              apply Nat.add_le_add hb
              simpa only [next] using ht₂
        _ = (q - i.val) * (100 * (L + 1) ^ 2) := by rw [hc]; ring
    · rw [run_add, hr₁]
      exact hr₂
  · have he : i = Fin.last q := by
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    subst i
    exact ⟨0, v, S, by simp, rfl, hr⟩
termination_by q - i.val

/-- Every query in a valid typed row is checked and retained in unary form;
the final success bit is physically written after the last query. -/
theorem valid_queries_run {n a q : Nat} (row : SourceCSPCodec.Row n a q)
    (hn : 0 < n) (L : Nat)
    (hword : ∀ j : Fin q, (row.1 j).val.bits.length ≤ L)
    (hcap : n - 1 ≤ L) :
    ∃ t v S, t ≤ q * (100 * (L + 1) ^ 2) + 1 ∧
      run t (⟨some (.start 0), (((none, none), (none, false)), none),
        startBank (fun j => (row.1 j).val.bits) (List.replicate (n - 1) true)⟩ :
        Config q) = ⟨none, v, S⟩ ∧
      S (.inr 1) = [true] ∧
      ∀ j : Fin q, S (.inl (j, 1)) = List.replicate (row.1 j).val true := by
  let S₀ := startBank (fun j => (row.1 j).val.bits) (List.replicate (n - 1) true)
  obtain ⟨t, v, S, ht, hr, hready⟩ :=
    run_until_end row hn L hword hcap 0 S₀ (ready_initial row) _
  refine ⟨t + 1, v, Function.update S (.inr 1) (true :: S (.inr 1)),
    by simpa only [Fin.val_zero, Nat.sub_zero] using Nat.add_le_add_right ht 1,
    ?_, ?_, ?_⟩
  · rw [run_add, hr, run_one, finish_step]
  · rw [Function.update_self, hready.status]
  · intro j
    rw [Function.update_of_ne (by simp : (.inl (j, 1) : Stack q) ≠ .inr 1)]
    exact hready.previous j (by simp)

end EthInapproximability.CurrentPaper.SourceCSPQueryBank
