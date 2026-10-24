import EthInapproximability.CurrentPaper.SourceCSPAllRowGrowth
import EthInapproximability.CurrentPaper.SourceCSPRowPairQuartic

/-! Uniform clock for the actual fixed-code checked all-row loop. -/

namespace EthInapproximability.CurrentPaper.SourceCSPAllRowLoopClock

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceCSPAllRowLoop SourceCSPAllRowClock
open SourceCSPRowPairQuarticProduction SourceCSPRowPairCostProduction
open SourceCSPNextParserGrowth
open scoped Classical

noncomputable def loopPairBudget (q G : Nat) : Nat :=
  pairCoefficient q * (G + 1) ^ 4 + 2

/-- The same fixed finite-control machine as `SourceCSPAllRowLoop.program`
consumes its physically stored remaining-row count within a uniform clock.
Saved/output/count are arbitrary prefix accumulators, bounded only in size. -/
theorem loop_from_check_clock {n M q H G : Nat}
    (rows : Fin M → SourceCSPCodec.Row n 2 q) (hq : 0 < q)
    (L : Nat) (hn : 0 < n)
    (hword : ∀ i : Fin M, ∀ j : Fin q,
      ((rows i).1 j).val.bits.length ≤ L)
    (hcapL : n - 1 ≤ L)
    (hnH : n ≤ H) (hmH : M ≤ H)
    (hHG : H ≤ G)
    (hparseG : parseWordCoefficient q * (H + 1) ^ 2 ≤ G)
    (ht : 1 + 2 ^ q ≤ H)
    (hL : L ≤ H)
    (r k : Nat) (hbound : r + 1 + k = M)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (saved output count : List Bool) (v : Control hq)
    (hS : ∀ x, (S x).length ≤ G)
    (hrow : ∀ x, (row x).length ≤ G)
    (hcount : S SourceCSPHeaderRowBridge.loopCount =
      List.replicate k true)
    (hcap : S SourceCSPHeaderRowBridge.capSource =
      List.replicate (n - 1) true)
    (hsource : row (.inr 0) = SourceCSPCodec.fnFields
      SourceCSPCodec.rowFields
        (remainingRows rows r k (by omega)))
    (hsourceLen : (row (.inr 0)).length ≤ H)
    (hsaved : saved.length + k * rowByteIncrement q H ≤ G)
    (houtput : output.length ≤ G)
    (hcountWords : count.length + k * rowCountIncrement q ≤ G) :
    let clauses := suffixClauses rows hq r k (by omega)
    ∃ (t : Nat) (lastRow : SourceCSPRowQueryFrame.Stack q → List Bool),
      t ≤ k * loopPairBudget q G + 3 ∧
      ((advance (program hq))^[t])
        (⟨some .check, v,
          SourceCSPNextRowBridge.callbackBank S row n r
            saved output count⟩ :
          TM2.Cfg (fun _ : Stack q => Bool) (Label hq) (Control hq)) =
        ⟨none, .done true,
          SourceCSPNextRowBridge.callbackBank (withRemaining S 0)
            lastRow n (M - 1)
            ((EncodedCNF.clauseFields clauses).reverse ++ saved)
            output (List.replicate clauses.length true ++ count)⟩ ∧
      lastRow (.inr 0) = [] := by
  induction k generalizing r S row saved output count v with
  | zero =>
      let B := SourceCSPNextRowBridge.callbackBank S row n r
        saved output count
      have hc : B remainingCount = [] := by
        change S SourceCSPHeaderRowBridge.loopCount = []
        simpa using hcount
      have hs : B rowSource = [] := by
        change SourceCSPNextRowBridge.callbackBank S row n r
          saved output count
          (SourceCSPNextRowBridge.rowEmbedding (.inr 0)) = []
        rw [SourceCSPNextRowBridge.callback_bank_row]
        simpa [SourceCSPCodec.fnFields_zero] using hsource
      have hrun : ((advance (program hq))^[3])
          (⟨some .check, v, B⟩ :
            TM2.Cfg (fun _ : Stack q => Bool) (Label hq) (Control hq)) =
          ⟨none, .done true, B⟩ := by
        change advance (program hq)
          (advance (program hq)
            (advance (program hq)
              (⟨some .check, v, B⟩ :
                TM2.Cfg (fun _ : Stack q => Bool)
                  (Label hq) (Control hq)))) = _
        rw [check_zero hq v B hc, eof_empty hq B hs, accept_step]
      have hS0 : withRemaining S 0 = S := by
        funext g
        by_cases hg : g = SourceCSPHeaderRowBridge.loopCount
        · subst g
          simpa [withRemaining] using hcount.symm
        · simp [withRemaining, Function.update_of_ne hg]
      have hr : r = M - 1 := by omega
      refine ⟨3, row, by simp [loopPairBudget], ?_, ?_⟩
      · simpa only [suffixClauses, List.ofFn_zero, List.flatten_nil,
          EncodedCNF.clauseFields, List.reverse_nil,
          List.nil_append, List.length_nil, List.replicate_zero,
          hS0, hr, B] using hrun
      · simpa [SourceCSPCodec.fnFields_zero] using hsource
  | succ k ih =>
      let rem := remainingRows rows r (k + 1) (by omega)
      let next : Fin M := ⟨r + 1, by omega⟩
      let S1 := withRemaining S k
      let B := SourceCSPNextRowBridge.callbackBank S row n r
        saved output count
      let B1 := SourceCSPNextRowBridge.callbackBank S1 row n r
        saved output count
      have hcB : B remainingCount = List.replicate (k + 1) true :=
        hcount
      have htwo : ((advance (program hq))^[2])
          (⟨some .check, v, B⟩ :
            TM2.Cfg (fun _ : Stack q => Bool) (Label hq) (Control hq)) =
          ⟨some (.row (rowPairCircuit hq).start),
            .row (rowPairCircuit hq).initial, B1⟩ := by
        change advance (program hq)
          (advance (program hq)
            (⟨some .check, v, B⟩ :
              TM2.Cfg (fun _ : Stack q => Bool)
                (Label hq) (Control hq))) = _
        rw [check_positive hq v B hcB,
          take_positive hq B hcB, decrement_callback_bank]
      have hcap1 : S1 SourceCSPHeaderRowBridge.capSource =
          List.replicate (n - 1) true := by
        have hne : SourceCSPHeaderRowBridge.capSource (q := q) ≠
            SourceCSPHeaderRowBridge.loopCount (q := q) := by
          simp [SourceCSPHeaderRowBridge.capSource,
            SourceCSPHeaderRowBridge.loopCount]
        change Function.update S SourceCSPHeaderRowBridge.loopCount
          (List.replicate k true) SourceCSPHeaderRowBridge.capSource = _
        rw [Function.update_of_ne hne]
        exact hcap
      have hS1 : ∀ x, (S1 x).length ≤ G :=
        withRemaining_words_le S hS (by omega : k ≤ H) hHG
      have hrem : row (.inr 0) =
          SourceCSPCodec.fnFields SourceCSPCodec.rowFields rem :=
        hsource
      have hremLen :
          (SourceCSPCodec.fnFields SourceCSPCodec.rowFields rem).length ≤ H :=
        hsource ▸ hsourceLen
      obtain ⟨tp, V, htp, hpair, hV, htail, _, _⟩ :=
        SourceCSPRowPairQuarticProduction.row_pair_run_quartic
          rows rem next r L S1 row saved output count hq hn
          (by rfl) (by exact (remainingRows_head rows (by omega)).symm)
          hrem hcap1 (hword next) hcapL
          hS1 hrow (hnH.trans hHG) (by omega)
          (by omega) houtput (by omega)
          hremLen hL hHG
      let headClauses := rowClauses rows hq next
      let saved1 := (EncodedCNF.clauseFields headClauses).reverse ++ saved
      let count1 := List.replicate headClauses.length true ++ count
      let B2 := SourceCSPNextRowBridge.callbackBank S1 V n (r + 1)
        saved1 output count1
      have hpair' : ((advance (rowPairCircuit hq).program)^[tp])
          (⟨some (rowPairCircuit hq).start,
            (rowPairCircuit hq).initial, B1⟩ :
            TM2.Cfg (fun _ : Stack q => Bool)
              (rowPairCircuit hq).Label
              (rowPairCircuit hq).Control) =
          ⟨none, (rowPairCircuit hq).initial, B2⟩ := by
        simpa only [rowPairCircuit, headClauses, saved1,
          count1, B1, B2] using hpair
      obtain ⟨up, hup, hrowHandoff⟩ :=
        row_handoff hq B1 B2 tp hpair'
      have hcount1 : S1 SourceCSPHeaderRowBridge.loopCount =
          List.replicate k true := by
        simp [S1, withRemaining]
      have hsource1 : V (.inr 0) = SourceCSPCodec.fnFields
          SourceCSPCodec.rowFields
            (remainingRows rows (r + 1) k (by omega)) := by
        rw [remainingRows_tail] at htail
        exact htail
      have hV1 : ∀ x, (V x).length ≤ G := by
        intro x
        exact (hV x).trans hparseG
      have hsourceLen1 : (V (.inr 0)).length ≤ H := by
        have hsplit := SourceCSPNextRowBridge.remaining_rows_succ rem
        rw [hsplit] at hremLen
        rw [htail]
        simp only [List.length_append] at hremLen
        omega
      have hsave1 : saved1.length + k * rowByteIncrement q H ≤ G :=
        saved_budget_step rows hq next hnH hmH ht saved hsaved
      have hcountW1 : count1.length + k * rowCountIncrement q ≤ G :=
        count_budget_step rows hq next count hcountWords
      obtain ⟨ut, lastRow, hut, htailRun, hfinalSource⟩ :=
        ih (r + 1) (by omega) S1 V saved1 output count1
          (.row (rowPairCircuit hq).initial)
          hS1 hV1 hcount1 hcap1 hsource1 hsourceLen1
          hsave1 houtput hcountW1
      have hseq : ((advance (program hq))^[ut + up + 2])
          (⟨some .check, v, B⟩ :
            TM2.Cfg (fun _ : Stack q => Bool) (Label hq) (Control hq)) =
          ⟨none, .done true,
            SourceCSPNextRowBridge.callbackBank (withRemaining S1 0)
              lastRow n (M - 1)
              ((EncodedCNF.clauseFields
                (suffixClauses rows hq (r + 1) k (by omega))).reverse ++
                saved1)
              output
              (List.replicate
                (suffixClauses rows hq (r + 1) k (by omega)).length true ++
                count1)⟩ := by
        rw [show ut + up + 2 = ut + (up + 2) by omega,
          Function.iterate_add_apply,
          show up + 2 = up + 2 by rfl,
          Function.iterate_add_apply, htwo, hrowHandoff]
        exact htailRun
      refine ⟨ut + up + 2, lastRow, ?_, ?_, hfinalSource⟩
      · dsimp [loopPairBudget] at hut ⊢
        simp only [Nat.succ_mul]
        omega
      · have hcountorder :
            List.replicate
                (suffixClauses rows hq (r + 1) k (by omega)).length true ++
              List.replicate headClauses.length true =
            List.replicate headClauses.length true ++
              List.replicate
                (suffixClauses rows hq (r + 1) k (by omega)).length true := by
          rw [← List.replicate_add, ← List.replicate_add,
            Nat.add_comm]
        rw [show withRemaining S1 0 = withRemaining S 0 from
          withRemaining_zero_idempotent S] at hseq
        dsimp only [count1, saved1] at hseq
        simp only [← List.append_assoc] at hseq
        rw [hcountorder] at hseq
        rw [suffixClauses_succ, clauseFields_append,
          List.reverse_append, List.length_append,
          List.replicate_add]
        simpa only [saved1, count1, List.append_assoc] using hseq

/-- Start the clocked loop from the exact post-first-row callback bank. The
header's unary `m` is copied to the physically exhausted validator counter,
then one mark is popped for the row already emitted. -/
theorem all_remaining_after_first_clock {n m q H : Nat}
    (rows : Fin m → SourceCSPCodec.Row n 2 q) (hq : 0 < q)
    (L : Nat) (hn : 0 < n) (hm : 0 < m)
    (hword : ∀ i : Fin m, ∀ j : Fin q,
      ((rows i).1 j).val.bits.length ≤ L)
    (hcapL : n - 1 ≤ L)
    (hnH : n ≤ H) (hmH : m ≤ H)
    (ht : 1 + 2 ^ q ≤ H) (hL : L ≤ H)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (saved output count : List Bool)
    (hS : ∀ x, (S x).length ≤ H)
    (hrow : ∀ x, (row x).length ≤ H)
    (hsaved : saved.length ≤ H)
    (houtput : output.length ≤ H)
    (hcountWords : count.length ≤ H)
    (hheader : S SourceCSPHeaderRowBridge.count =
      List.replicate m true)
    (hvalidatorDone : S SourceCSPHeaderRowBridge.loopCount = [])
    (hcap : S SourceCSPHeaderRowBridge.capSource =
      List.replicate (n - 1) true)
    (hsource : row (.inr 0) = SourceCSPCodec.fnFields
      SourceCSPCodec.rowFields
        (remainingRows rows 0 (m - 1) (by omega)))
    (hsourceLen : (row (.inr 0)).length ≤ H) :
    let G := loopEnvelope q H m
    let clauses := suffixClauses rows hq 0 (m - 1) (by omega)
    ∃ (tcopy tloop t : Nat)
      (lastRow : SourceCSPRowQueryFrame.Stack q → List Bool),
      tcopy ≤ 2 * m + 2 ∧
      tloop ≤ (m - 1) * loopPairBudget q G + 3 ∧
      t = tcopy + 1 + tloop ∧
      ((advance (program hq))^[t])
        (⟨some (.copy .scan), .copy none,
          SourceCSPNextRowBridge.callbackBank S row n 0
            saved output count⟩ :
          TM2.Cfg (fun _ : Stack q => Bool) (Label hq) (Control hq)) =
        ⟨none, .done true,
          SourceCSPNextRowBridge.callbackBank (withRemaining S 0)
            lastRow n (m - 1)
            ((EncodedCNF.clauseFields clauses).reverse ++ saved)
            output (List.replicate clauses.length true ++ count)⟩ ∧
      lastRow (.inr 0) = [] := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  let G := loopEnvelope q H (k + 1)
  let B := SourceCSPNextRowBridge.callbackBank S row n 0
    saved output count
  let S1 := withRemaining S k
  have hheaderB : B headerCount = List.replicate (k + 1) true :=
    hheader
  have hcountB : B remainingCount = [] := hvalidatorDone
  have hscratchB : B copyScratch = [] := rfl
  obtain ⟨tc, htc, hcopy⟩ := copy_handoff hq B
    hheaderB hcountB hscratchB
  have hcCopy : copiedCount B (k + 1) remainingCount =
      List.replicate (k + 1) true := by
    simp [copiedCount]
  have hpop := first_pop_positive hq (copiedCount B (k + 1))
    hcCopy
  have hbank : decremented (copiedCount B (k + 1)) k =
      SourceCSPNextRowBridge.callbackBank S1 row n 0
        saved output count := by
    change decremented (decremented B (k + 1)) k = _
    rw [decrement_callback_bank, decrement_callback_bank,
      withRemaining_overwrite]
  rw [hbank] at hpop
  have hcount1 : S1 SourceCSPHeaderRowBridge.loopCount =
      List.replicate k true := by
    simp [S1, withRemaining]
  have hcap1 : S1 SourceCSPHeaderRowBridge.capSource =
      List.replicate (n - 1) true := by
    have hne : SourceCSPHeaderRowBridge.capSource (q := q) ≠
        SourceCSPHeaderRowBridge.loopCount (q := q) := by
      simp [SourceCSPHeaderRowBridge.capSource,
        SourceCSPHeaderRowBridge.loopCount]
    change Function.update S SourceCSPHeaderRowBridge.loopCount
      (List.replicate k true) SourceCSPHeaderRowBridge.capSource = _
    rw [Function.update_of_ne hne]
    exact hcap
  have hHG : H ≤ G := base_le_envelope q H (k + 1)
  have hS1 : ∀ x, (S1 x).length ≤ G :=
    withRemaining_words_le S
      (fun x => (hS x).trans hHG)
      (by omega : k ≤ H) hHG
  have hrowG : ∀ x, (row x).length ≤ G :=
    fun x => (hrow x).trans hHG
  have hsaveG : saved.length + k * rowByteIncrement q H ≤ G :=
    saved_budget_le_envelope q H (k + 1) k saved hsaved (by omega)
  have hcountG : count.length + k * rowCountIncrement q ≤ G :=
    count_budget_le_envelope q H (k + 1) k count hcountWords
      (by omega)
  obtain ⟨tl, lastRow, htl, hloop, hfinalSource⟩ :=
    loop_from_check_clock rows hq L hn hword hcapL hnH hmH
      hHG (parser_le_envelope q H (k + 1)) ht hL
      0 k (by omega) S1 row saved output count
      (.idle (some true)) hS1 hrowG hcount1 hcap1 hsource
      hsourceLen hsaveG (houtput.trans hHG) hcountG
  refine ⟨tc, tl, tc + 1 + tl, lastRow,
    htc, htl, rfl, ?_, hfinalSource⟩
  have hrun : ((advance (program hq))^[tc + 1 + tl])
      (⟨some (.copy .scan), .copy none, B⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) (Label hq) (Control hq)) =
      ⟨none, .done true,
        SourceCSPNextRowBridge.callbackBank (withRemaining S1 0)
          lastRow n (k + 1 - 1)
          ((EncodedCNF.clauseFields
            (suffixClauses rows hq 0 k (by omega))).reverse ++ saved)
          output
          (List.replicate
            (suffixClauses rows hq 0 k (by omega)).length true ++ count)⟩ := by
    rw [show tc + 1 + tl = tl + (1 + tc) by omega,
      Function.iterate_add_apply,
      show 1 + tc = 1 + tc by rfl,
      Function.iterate_add_apply, hcopy]
    change ((advance (program hq))^[tl])
      (advance (program hq)
        (⟨some .firstPop, .copy none, copiedCount B (k + 1)⟩)) = _
    rw [hpop]
    exact hloop
  rw [show withRemaining S1 0 = withRemaining S 0 from
    withRemaining_zero_idempotent S] at hrun
  simpa only [B] using hrun

noncomputable def loopCoefficient (q : Nat) : Nat :=
  pairCoefficient q * (envelopeCoefficient q + 1) ^ 4 + 10

theorem copy_loop_clock_le_polynomial (q H m tc tl : Nat)
    (hm : m ≤ H)
    (htc : tc ≤ 2 * m + 2)
    (htl : tl ≤ (m - 1) *
      loopPairBudget q (loopEnvelope q H m) + 3) :
    tc + 1 + tl ≤ loopCoefficient q * (H + 1) ^ 9 := by
  let M := H + 1
  let E := envelopeCoefficient q
  let A := pairCoefficient q
  let G := loopEnvelope q H m
  have hM : 1 ≤ M := by dsimp [M]; omega
  have hmM : m ≤ M := by dsimp [M]; omega
  have hkM : m - 1 ≤ M := by omega
  have hG : G ≤ E * M ^ 2 :=
    loopEnvelope_le_quadratic q H m hm
  have hM2 : 1 ≤ M ^ 2 := by nlinarith
  have hG1 : G + 1 ≤ (E + 1) * M ^ 2 := by
    nlinarith
  have hpow := Nat.pow_le_pow_left hG1 4
  have hpair : loopPairBudget q G ≤
      (A * (E + 1) ^ 4 + 2) * M ^ 8 := by
    have hp := Nat.mul_le_mul_left A hpow
    have hM8 : 1 ≤ M ^ 8 := by
      have hp8 := pow_pos (by omega : 0 < M) 8
      omega
    dsimp [loopPairBudget]
    nlinarith
  have htotal : (m - 1) * loopPairBudget q G ≤
      (A * (E + 1) ^ 4 + 2) * M ^ 9 := by
    have hp := Nat.mul_le_mul hkM hpair
    nlinarith
  have hM9 : M ≤ M ^ 9 := by
    have hM8 : 1 ≤ M ^ 8 := by
      have hp8 := pow_pos (by omega : 0 < M) 8
      omega
    nlinarith
  have hbound : tc + 1 + tl ≤
      (A * (E + 1) ^ 4 + 2) * M ^ 9 + 2 * M + 6 := by
    dsimp [G] at htotal htl
    omega
  change tc + 1 + tl ≤
    (A * (E + 1) ^ 4 + 10) * M ^ 9
  nlinarith

/-- Fixed-degree bound, independent of the variable row count as an exponent,
for the actual post-first-row controller. No per-step bank envelope is
assumed: the envelope is derived from typed source rows and initial words. -/
theorem all_remaining_after_first_polynomial {n m q H : Nat}
    (rows : Fin m → SourceCSPCodec.Row n 2 q) (hq : 0 < q)
    (L : Nat) (hn : 0 < n) (hm : 0 < m)
    (hword : ∀ i : Fin m, ∀ j : Fin q,
      ((rows i).1 j).val.bits.length ≤ L)
    (hcapL : n - 1 ≤ L)
    (hnH : n ≤ H) (hmH : m ≤ H)
    (ht : 1 + 2 ^ q ≤ H) (hL : L ≤ H)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (saved output count : List Bool)
    (hS : ∀ x, (S x).length ≤ H)
    (hrow : ∀ x, (row x).length ≤ H)
    (hsaved : saved.length ≤ H)
    (houtput : output.length ≤ H)
    (hcountWords : count.length ≤ H)
    (hheader : S SourceCSPHeaderRowBridge.count =
      List.replicate m true)
    (hvalidatorDone : S SourceCSPHeaderRowBridge.loopCount = [])
    (hcap : S SourceCSPHeaderRowBridge.capSource =
      List.replicate (n - 1) true)
    (hsource : row (.inr 0) = SourceCSPCodec.fnFields
      SourceCSPCodec.rowFields
        (remainingRows rows 0 (m - 1) (by omega)))
    (hsourceLen : (row (.inr 0)).length ≤ H) :
    let clauses := suffixClauses rows hq 0 (m - 1) (by omega)
    ∃ (t : Nat) (lastRow : SourceCSPRowQueryFrame.Stack q → List Bool),
      t ≤ loopCoefficient q * (H + 1) ^ 9 ∧
      ((advance (program hq))^[t])
        (⟨some (.copy .scan), .copy none,
          SourceCSPNextRowBridge.callbackBank S row n 0
            saved output count⟩ :
          TM2.Cfg (fun _ : Stack q => Bool) (Label hq) (Control hq)) =
        ⟨none, .done true,
          SourceCSPNextRowBridge.callbackBank (withRemaining S 0)
            lastRow n (m - 1)
            ((EncodedCNF.clauseFields clauses).reverse ++ saved)
            output (List.replicate clauses.length true ++ count)⟩ ∧
      lastRow (.inr 0) = [] := by
  obtain ⟨tc, tl, t, lastRow, htc, htl, htime, hrun, hfinalSource⟩ :=
    all_remaining_after_first_clock rows hq L hn hm hword hcapL
      hnH hmH ht hL S row saved output count hS hrow hsaved
      houtput hcountWords hheader hvalidatorDone hcap hsource hsourceLen
  refine ⟨t, lastRow, ?_, hrun, hfinalSource⟩
  rw [htime]
  exact copy_loop_clock_le_polynomial q H m tc tl hmH htc htl

end EthInapproximability.CurrentPaper.SourceCSPAllRowLoopClock
