import EthInapproximability.CurrentPaper.SourceGenericFinalizePhase

/-!
# Header and finalizer phase: the actual run (unit 1, segment 4)
-/

namespace EthInapproximability.CurrentPaper.SourceGenericComposite.Converter

open Turing BitMachineEncoding BitMachineStackEmbedding
open scoped Classical

theorem not_hdr_main {q : Nat} (x : SourceGenericComposite.Stack q) :
    ¬ ∃ k, hdrEmb q k = (.inl x : CStack q) := by
  rintro ⟨k, hk⟩
  fin_cases k <;> simp [hdrEmb, h0, h1, fin0] at hk

theorem not_hdr_fin {q : Nat} (k : SourceClauseCountFinalize.Stack)
    (hk : k ≠ .inl 0) :
    ¬ ∃ i, hdrEmb q i = (.inr (.inl k) : CStack q) := by
  rintro ⟨i, hi⟩
  fin_cases i <;> simp [hdrEmb, h0, h1, fin0] at hi
  exact hk hi.symm

theorem not_hdr_scr {q : Nat} : ¬ ∃ i, hdrEmb q i = scr q := by
  rintro ⟨i, hi⟩
  fin_cases i <;> simp [hdrEmb, h0, h1, fin0, scr] at hi

/-- Segment 4: from ANY bank holding unary `n` (writer vertex), unary `m`
(validator row count), the generic reverse payload (writer saved) and the
unary clause count (writer count), with every fresh cell empty, the fixed
phase reaches the exact bank `phaseFinal …`, whose validator output slot is
the literal encoded three-CNF. -/
theorem phase_run {n m a q : Nat} (ha : 0 < a) (hq : 0 < q)
    (P : SourceBooleanEncoding.CSP n m a q)
    (W : CStack q → List Bool)
    (hV : W (vertexCell q) = List.replicate n true)
    (hM : W (countGCell q) = List.replicate m true)
    (hP : W (savedCellC q) = SourceGenericOrder.sourceReversePayload P hq)
    (hC : W (countCellC q) =
      List.replicate (SourceGenericOrder.sourceEmittedCount P hq) true)
    (hE : ∀ e : Extra, W (.inr e) = []) :
    ∃ t ≤ phaseClock a q n m (SourceGenericOrder.sourceVariables P)
        (SourceGenericOrder.sourceEmittedCount P hq)
        (SourceGenericOrder.sourceReversePayload P hq).length
        (W (outCell q)).length,
      ((advance (phase a q))^[t])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          phaseControl a q, W⟩ : TM2.Cfg (fun _ : CStack q => Bool) _ _) =
        ⟨none, phaseControl a q,
          phaseFinal W n m (SourceGenericOrder.sourceVariables P)
            (SourceGenericOrder.sourceReversePayload P hq)
            (SourceGenericOrder.sourceEmittedCount P hq)⟩ ∧
      phaseFinal W n m (SourceGenericOrder.sourceVariables P)
          (SourceGenericOrder.sourceReversePayload P hq)
          (SourceGenericOrder.sourceEmittedCount P hq) (outCell q) =
        EncodedCNF.encode (SourceBooleanEncoding.threeCNF P hq) := by
  -- names
  set vars := SourceGenericOrder.sourceVariables P with hvars
  set cnt := SourceGenericOrder.sourceEmittedCount P hq with hcnt
  set payload := SourceGenericOrder.sourceReversePayload P hq with hpayload
  -- disequalities between the cells used
  have d_h0_h1 : h0 q ≠ h1 q := by simp [h0, h1]
  have d_cG_h0 : countGCell q ≠ h0 q := by intro h; cases h
  have d_sv_h0 : savedCellC q ≠ h0 q := by intro h; cases h
  have d_sv_h1 : savedCellC q ≠ h1 q := by intro h; cases h
  have d_cC_h0 : countCellC q ≠ h0 q := by intro h; cases h
  have d_cC_h1 : countCellC q ≠ h1 q := by intro h; cases h
  have d_cC_f1 : countCellC q ≠ fin1 q := by intro h; cases h
  have d_scr_h0 : scr q ≠ h0 q := by simp [scr, h0]
  have d_scr_h1 : scr q ≠ h1 q := by simp [scr, h1]
  have d_scr_f1 : scr q ≠ fin1 q := by simp [scr, fin1]
  have d_f0_h0 : fin0 q ≠ h0 q := by simp [fin0, h0]
  have d_f0_h1 : fin0 q ≠ h1 q := by simp [fin0, h1]
  have d_f0_f1 : fin0 q ≠ fin1 q := by simp [fin0, fin1]
  have d_f0_fu : fin0 q ≠ fuel q := by simp [fin0, fuel]
  have d_f0_out : fin0 q ≠ outCell q := by intro h; cases h
  have d_f1_h0 : fin1 q ≠ h0 q := by simp [fin1, h0]
  have d_f1_h1 : fin1 q ≠ h1 q := by simp [fin1, h1]
  have d_f1_fu : fin1 q ≠ fuel q := by simp [fin1, fuel]
  have d_f1_out : fin1 q ≠ outCell q := by intro h; cases h
  have d_fu_h0 : fuel q ≠ h0 q := by simp [fuel, h0]
  have d_fu_h1 : fuel q ≠ h1 q := by simp [fuel, h1]
  have d_fu_f1 : fuel q ≠ fin1 q := by simp [fuel, fin1]
  have d_fu_out : fuel q ≠ outCell q := by intro h; cases h
  have d_out_h0 : outCell q ≠ h0 q := by intro h; cases h
  have d_out_h1 : outCell q ≠ h1 q := by intro h; cases h
  have d_out_f1 : outCell q ≠ fin1 q := by intro h; cases h
  have d_out_fu : outCell q ≠ fuel q := by intro h; cases h
  have d_scr_fu : scr q ≠ fuel q := by simp [scr, fuel]
  have hscr : W (scr q) = [] := hE _
  -- 1. copy n
  have hr1 := copy_run (vertexCell q) (h0 q) (scr q)
    (vertex_ne_h0 q) (vertex_ne_scr q) (h0_ne_scr q)
    W (List.replicate n true) hV (hE _) hscr
  simp only [List.length_replicate] at hr1
  -- 2. copy m
  have hr2 := copy_run (countGCell q) (h1 q) (scr q)
    (countG_ne_h1 q) (countG_ne_scr q) (h1_ne_scr q)
    (bank1 W n) (List.replicate m true)
    (by rw [bank1, Function.update_of_ne d_cG_h0]; exact hM)
    (by rw [bank1, Function.update_of_ne (Ne.symm d_h0_h1)]; exact hE _)
    (by rw [bank1, Function.update_of_ne d_scr_h0]; exact hscr)
  simp only [List.length_replicate] at hr2
  -- 3. header scanner
  have hb2 : bank (hdrEmb q) (bank2 W n m)
      (SourceAffineUnary.contents (List.replicate n true)
        (List.replicate m true) []) = bank2 W n m := by
    apply bank_eq_self
    intro k
    fin_cases k
    · show List.replicate n true = bank2 W n m (h0 q)
      rw [bank2, Function.update_of_ne d_h0_h1, bank1, Function.update_self]
    · show List.replicate m true = bank2 W n m (h1 q)
      rw [bank2, Function.update_self]
    · show [] = bank2 W n m (fin0 q)
      rw [bank2, Function.update_of_ne d_f0_h1, bank1,
        Function.update_of_ne d_f0_h0]
      exact (hE _).symm
  have hs := SourceGenericVariableUnary.source_header_run ha P
  have hr3 := BitMachineStackRun.run (hdrEmb q) (bank2 W n m)
    (SourceGenericVariableUnary.program a q)
    (SourceAffineUnary.cfg (some .vertexScan) none
      (List.replicate n true) (List.replicate m true) [])
    (SourceGenericVariableUnary.time a q n m)
  rw [hs] at hr3
  simp only [stackCfg, SourceAffineUnary.cfg, hb2] at hr3
  -- facts about bank3 away from the scanner cells
  have hb3main : ∀ x : SourceGenericComposite.Stack q,
      bank3 W n m vars (.inl x) = bank2 W n m (.inl x) := by
    intro x
    exact bank_outside _ _ _ _ (not_hdr_main x)
  have hb3scr : bank3 W n m vars (scr q) = [] := by
    rw [bank3, bank_outside _ _ _ _ not_hdr_scr, bank2,
      Function.update_of_ne d_scr_h1, bank1, Function.update_of_ne d_scr_h0]
    exact hscr
  have hb3fin : ∀ k : SourceClauseCountFinalize.Stack, k ≠ .inl 0 →
      bank3 W n m vars (.inr (.inl k)) = [] := by
    intro k hk
    rw [bank3, bank_outside _ _ _ _ (not_hdr_fin k hk), bank2,
      Function.update_of_ne (by simp [h1]), bank1,
      Function.update_of_ne (by simp [h0])]
    exact hE _
  have hb3f0 : bank3 W n m vars (fin0 q) = List.replicate vars true := by
    rw [bank3, show fin0 q = hdrEmb q 2 by simp [hdrEmb], bank_at]
    rfl
  -- 4. copy payload
  have hr4 := copy_run (savedCellC q) (fin1 q) (scr q)
    (saved_ne_fin1 q) (saved_ne_scr q) (fin1_ne_scr q)
    (bank3 W n m vars) payload
    (by
      change bank3 W n m vars (.inl _) = payload
      rw [hb3main]
      change bank2 W n m (savedCellC q) = payload
      rw [bank2, Function.update_of_ne d_sv_h1, bank1,
        Function.update_of_ne d_sv_h0]
      exact hP)
    (hb3fin (.inl 1) (by simp)) hb3scr
  -- 5. copy count
  have hr5 := copy_run (countCellC q) (fuel q) (scr q)
    (countC_ne_fuel q) (countC_ne_scr q) (fuel_ne_scr q)
    (bank4 W n m vars payload) (List.replicate cnt true)
    (by
      rw [bank4, Function.update_of_ne d_cC_f1]
      change bank3 W n m vars (.inl _) = _
      rw [hb3main]
      change bank2 W n m (countCellC q) = _
      rw [bank2, Function.update_of_ne d_cC_h1, bank1,
        Function.update_of_ne d_cC_h0]
      exact hC)
    (by
      rw [bank4, Function.update_of_ne d_fu_f1]
      exact hb3fin (.inr (.inr 0)) (by simp))
    (by rw [bank4, Function.update_of_ne d_scr_f1]; exact hb3scr)
  simp only [List.length_replicate] at hr5
  -- 6. clear the output slot
  have hr6 := clear_run (outCell q) (bank5 W n m vars payload cnt)
  have hout5 : bank5 W n m vars payload cnt (outCell q) = W (outCell q) := by
    rw [bank5, Function.update_of_ne d_out_fu, bank4,
      Function.update_of_ne d_out_f1]
    change bank3 W n m vars (.inl _) = _
    rw [hb3main]
    change bank2 W n m (outCell q) = _
    rw [bank2, Function.update_of_ne d_out_h1, bank1,
      Function.update_of_ne d_out_h0]
  rw [hout5] at hr6
  -- 7. the admitted finalizer
  have hb6 : bank (finEmb q) (bank6 W n m vars payload cnt)
      (SourceClauseCountFinalize.inputBank vars cnt payload []) =
      bank6 W n m vars payload cnt := by
    apply bank_eq_self
    intro k
    rcases k with k | c
    · fin_cases k
      · show List.replicate vars true = _
        rw [finEmb_other q _ (by simp)]
        change List.replicate vars true = bank6 W n m vars payload cnt (fin0 q)
        rw [bank6, Function.update_of_ne d_f0_out, bank5,
          Function.update_of_ne d_f0_fu, bank4, Function.update_of_ne d_f0_f1,
          hb3f0]
      · show payload = _
        rw [finEmb_other q _ (by simp)]
        change payload = bank6 W n m vars payload cnt (fin1 q)
        rw [bank6, Function.update_of_ne d_f1_out, bank5,
          Function.update_of_ne d_f1_fu, bank4, Function.update_self]
      · show [] = _
        rw [finEmb_other q _ (by simp)]
        rw [bank6, Function.update_of_ne (by intro h; cases h), bank5,
          Function.update_of_ne (by simp [fuel]), bank4,
          Function.update_of_ne (by simp [fin1])]
        exact (hb3fin (.inl 2) (by simp)).symm
      · show [] = bank6 W n m vars payload cnt (finEmb q (.inl 3))
        rw [finEmb_out, bank6, Function.update_self]
    · change (BitMachineIteration.ready SourceClauseCountFinalize.counter []
          (List.replicate cnt true)).stk c = _
      rw [SourceUnaryBinaryCall.initial_bank,
        finEmb_other q _ (by simp)]
      by_cases hc : c = .inr 0
      · subst c
        simp only [if_true]
        change List.replicate cnt true = bank6 W n m vars payload cnt (fuel q)
        rw [bank6, Function.update_of_ne d_fu_out, bank5, Function.update_self]
      · simp only [hc, if_false]
        rw [bank6, Function.update_of_ne (by intro h; cases h), bank5,
          Function.update_of_ne (by simpa [fuel] using hc), bank4,
          Function.update_of_ne (by simp [fin1])]
        exact (hb3fin (.inr c) (by simp)).symm
  obtain ⟨tf, htf, hf⟩ :=
    SourceClauseCountFinalize.count_and_finalize vars cnt payload []
  have hr7 := BitMachineStackRun.run (finEmb q) (bank6 W n m vars payload cnt)
    SourceClauseCountFinalize.program
    (⟨some (BitMachineRawSequence.leftLabel (.inr .testFuel)),
      ((SourceClauseCountFinalize.counter.initial, none), none),
      SourceClauseCountFinalize.inputBank vars cnt payload []⟩ :
      SourceClauseCountFinalize.Config) tf
  rw [hf] at hr7
  simp only [stackCfg, hb6] at hr7
  -- sequencing
  obtain ⟨t6, ht6, h6⟩ := BitMachineRawSequence.runs
    (clearOut q) (finProgram q) 0
    (BitMachineRawSequence.leftLabel (.inr .testFuel))
    ((), none) ((), none)
    ((SourceClauseCountFinalize.counter.initial, none), none)
    ((SourceClauseCountFinalize.counter.initial, none), none)
    (bank5 W n m vars payload cnt) (bank6 W n m vars payload cnt)
    (phaseFinal W n m vars payload cnt)
    ((W (outCell q)).length + 2) tf hr6 hr7
  obtain ⟨t5, ht5, h5⟩ := BitMachineRawSequence.runs
    (copyC q) (p6 q) BitMachineCopy.Label.scan (BitMachineRawSequence.leftLabel 0)
    none none
    (((), none), ((SourceClauseCountFinalize.counter.initial, none), none))
    (((), none), ((SourceClauseCountFinalize.counter.initial, none), none))
    (bank4 W n m vars payload) (bank5 W n m vars payload cnt)
    (phaseFinal W n m vars payload cnt) (2*cnt+2) t6 hr5 h6
  obtain ⟨t4, ht4, h4⟩ := BitMachineRawSequence.runs
    (copyP q) (p5 q) BitMachineCopy.Label.scan
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    none none
    (none, (((), none), ((SourceClauseCountFinalize.counter.initial, none), none)))
    (none, (((), none), ((SourceClauseCountFinalize.counter.initial, none), none)))
    (bank3 W n m vars) (bank4 W n m vars payload)
    (phaseFinal W n m vars payload cnt) (2*payload.length+2) t5 hr4 h5
  obtain ⟨t3, ht3, h3⟩ := BitMachineRawSequence.runs
    (scanProgram a q) (p4 q) .vertexScan
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    none none
    (none, (none,
      (((), none), ((SourceClauseCountFinalize.counter.initial, none), none))))
    (none, (none,
      (((), none), ((SourceClauseCountFinalize.counter.initial, none), none))))
    (bank2 W n m) (bank3 W n m vars)
    (phaseFinal W n m vars payload cnt)
    (SourceGenericVariableUnary.time a q n m) t4 hr3 h4
  obtain ⟨t2, ht2, h2⟩ := BitMachineRawSequence.runs
    (copyM q) (p3 a q) BitMachineCopy.Label.scan
    (BitMachineRawSequence.leftLabel .vertexScan)
    none none
    (none, (none, (none,
      (((), none), ((SourceClauseCountFinalize.counter.initial, none), none)))))
    (none, (none, (none,
      (((), none), ((SourceClauseCountFinalize.counter.initial, none), none)))))
    (bank1 W n) (bank2 W n m)
    (phaseFinal W n m vars payload cnt) (2*m+2) t3 hr2 h3
  obtain ⟨t1, ht1, h1r⟩ := BitMachineRawSequence.runs
    (copyN q) (p2 a q) BitMachineCopy.Label.scan
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    none none
    (none, (none, (none, (none,
      (((), none), ((SourceClauseCountFinalize.counter.initial, none), none))))))
    (none, (none, (none, (none,
      (((), none), ((SourceClauseCountFinalize.counter.initial, none), none))))))
    W (bank1 W n) (phaseFinal W n m vars payload cnt) (2*n+2) t2 hr1 h2
  refine ⟨t1, ?_, h1r, ?_⟩
  · unfold phaseClock
    try simp only [← hvars, ← hcnt, ← hpayload]
    omega
  · rw [phaseFinal, ← finEmb_out, bank_at, finExit_out]
    exact encode_identity P hq

#print axioms not_hdr_main
#print axioms not_hdr_fin
#print axioms phase_run

end EthInapproximability.CurrentPaper.SourceGenericComposite.Converter
