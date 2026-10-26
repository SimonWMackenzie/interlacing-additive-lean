import EthInapproximability.CurrentPaper.SourceOriginalListPacketizerList

/-! Zero-count exit, empty-tail check, and physically reversed output. -/

namespace EthInapproximability.CurrentPaper.SourceOriginalListPacketizer

open Turing TM2.Stmt BitMachineEncoding EncodedCommunication
open SourceOriginalListPacketizerCleanupRun

noncomputable section

theorem subOne_none_of_zero (q : List Bool) (hzero : bitsValue q = 0) :
    ProtocolBinaryCounter.subOne q = none := by
  have h := ProtocolBinaryCounter.subOne_spec q
  cases hs : ProtocolBinaryCounter.subOne q with
  | none => rfl
  | some q' =>
      simp only [hs] at h
      omega

theorem counter_zero_bank (n : ℕ) (source q acc : List Bool) :
    BitMachineStackEmbedding.bank counterStack (readyBank n source q acc)
      (SourceListMachineCounter.cfg none
        (SourceListMachineCounter.doneControl false) q []).stk =
    readyBank n source q acc := by
  exact counter_success_bank n source q q acc

theorem afterCounter_zero (S : Stack → List Bool) :
    advance program
      ⟨some (adminLabel .afterCounter),
        counterControl (SourceListMachineCounter.doneControl false),S⟩ =
      ⟨some (adminLabel .checkTail),
        counterControl (SourceListMachineCounter.doneControl false),S⟩ := by
  simp only [advance, adminLabel, program, TM2.step, TM2.stepAux,
    Option.getD_some]
  simp [counterControl, SourceListMachineCounter.doneControl]

theorem checkTail_empty (v : PreControl) (S : Stack → List Bool)
    (hsource : S (.inr 0) = []) :
    advance program ⟨some (adminLabel .checkTail),(v,none),S⟩ =
      ⟨some (adminLabel .finalize),(v,none),S⟩ := by
  simp [advance, adminLabel, program, TM2.step, TM2.stepAux, hsource]

theorem finalize_program : program (adminLabel .finalize) =
    BitMachineBroadcast.scanStep (.inr 4) (.inr 9)
      (adminLabel .finalize) (adminLabel .done) := rfl

theorem finalize_source_ne_output : (.inr 4 : Stack) ≠ .inr 9 := by decide

theorem finalize_run (v : PreControl) (S : Stack → List Bool) :
    run ((S (.inr 4)).length+1)
      ⟨some (adminLabel .finalize),(v,none),S⟩ =
    ⟨some (adminLabel .done),(v,none),
      BitMachineBroadcast.contents (.inr 4) (.inr 9) S []
        ((S (.inr 4)).reverse ++ S (.inr 9))⟩ := by
  have h := BitMachineBroadcast.scan_run program (.inr 4) (.inr 9)
    finalize_source_ne_output (adminLabel .finalize) (adminLabel .done)
    finalize_program v none (S (.inr 4)) (S (.inr 9)) S
  rw [contents_eq_self S (.inr 4) (.inr 9) finalize_source_ne_output] at h
  exact h

theorem done_step (v : PreControl) (S : Stack → List Bool) :
    advance program ⟨some (adminLabel .done),(v,none),S⟩ =
      ⟨none,(v,none),S⟩ := by
  simp [advance, adminLabel, program, TM2.step, TM2.stepAux]

theorem zero_finalize (n : ℕ) (q acc : List Bool)
    (hzero : bitsValue q = 0) :
    ∃ t ≤ (4*q.length+5) + 1 + 1 + (acc.length+1) + 1,
      (run t (loopCfg (readyBank n [] q acc))).l = none ∧
      (run t (loopCfg (readyBank n [] q acc))).stk (.inr 9) = acc.reverse := by
  let S := readyBank n [] q acc
  have hstart : counterFrame S
      (SourceListMachineCounter.cfg (some (.inr .scan))
        SourceListMachineCounter.initialControl q []) = loopCfg S := by
    apply counterFrame_initial
    · exact readyBank_count n [] q acc
    · simp [S, readyBank]
  obtain ⟨a, ha, hcounter⟩ := counter_embedded S q
  rw [subOne_none_of_zero q hzero, hstart] at hcounter
  rw [counterFrame_halted, counter_zero_bank] at hcounter
  have h1 : run (a+1) (loopCfg S) =
      ⟨some (adminLabel .checkTail),
        counterControl (SourceListMachineCounter.doneControl false),S⟩ :=
    (run_add hcounter 1).trans (by
      rw [run_succ (afterCounter_zero S) 0]
      rfl)
  have hsource : S (.inr 0) = [] := readyBank_source n [] q acc
  have h2 : run (a+1+1) (loopCfg S) =
      ⟨some (adminLabel .finalize),
        counterControl (SourceListMachineCounter.doneControl false),S⟩ :=
    (run_add h1 1).trans (by
      simpa only [run, Function.iterate_one] using
        (checkTail_empty
          (counterControl (SourceListMachineCounter.doneControl false)).1
          S hsource))
  have hacc : S (.inr 4) = acc := readyBank_accumulator n [] q acc
  have hout : S (.inr 9) = [] := by simp [S, readyBank]
  have h3' := finalize_run
    (counterControl (SourceListMachineCounter.doneControl false)).1 S
  rw [hacc, hout] at h3'
  simp only [List.append_nil] at h3'
  have h3 : run (a+1+1+(acc.length+1)) (loopCfg S) =
      ⟨some (adminLabel .done),
        counterControl (SourceListMachineCounter.doneControl false),
        BitMachineBroadcast.contents (.inr 4) (.inr 9) S [] acc.reverse⟩ :=
    (run_add h2 _).trans h3'
  have h4 : run (a+1+1+(acc.length+1)+1) (loopCfg S) =
      ⟨none,counterControl (SourceListMachineCounter.doneControl false),
        BitMachineBroadcast.contents (.inr 4) (.inr 9) S [] acc.reverse⟩ :=
    (run_add h3 1).trans (by
      simpa only [run, Function.iterate_one] using
        (done_step
          (counterControl (SourceListMachineCounter.doneControl false)).1
          (BitMachineBroadcast.contents (.inr 4) (.inr 9) S [] acc.reverse)))
  refine ⟨a+1+1+(acc.length+1)+1, by omega, ?_, ?_⟩
  · rw [h4]
  · rw [h4]
    simp [BitMachineBroadcast.contents]

def canonicalTime (n : ℕ) (words : List (List Bool)) : ℕ :=
  (5*words.length.bits.length+7) +
    listWork n words.length.bits.length words +
    ((4*words.length.bits.length+5) + 1 + 1 +
      ((natField words.length ++ joined n words).length+1) + 1)

theorem canonical_run (n : ℕ) (words : List (List Bool)) :
    ∃ t ≤ canonicalTime n words,
      (run t (startCfg n (SourceListEncoding.encode words))).l = none ∧
      (run t (startCfg n (SourceListEncoding.encode words))).stk (.inr 9) =
        natField words.length ++ joined n words := by
  obtain ⟨a, ha, hinit⟩ := init_to_counter n words
  rw [initialized_eq_ready] at hinit
  let q := words.length.bits
  let acc := (natField words.length).reverse
  have hvalue : bitsValue q = words.length := bitsValue_bits words.length
  obtain ⟨b, hb, q', hlist, hzero, hlen⟩ :=
    canonical_list_run n words [] q acc hvalue
  simp only [List.append_nil] at hlist
  let acc' := (joined n words).reverse ++ acc
  obtain ⟨d, hd, hhalt, hout⟩ := zero_finalize n q' acc' hzero
  have h1 : run (a+b) (startCfg n (SourceListEncoding.encode words)) =
      loopCfg (readyBank n [] q' acc') :=
    (run_add hinit b).trans hlist
  have hrun : run (a+b+d) (startCfg n (SourceListEncoding.encode words)) =
      run d (loopCfg (readyBank n [] q' acc')) := run_add h1 d
  have hacc : acc'.reverse = natField words.length ++ joined n words := by
    simp [acc', acc, List.reverse_append]
  refine ⟨a+b+d, ?_, ?_, ?_⟩
  · have hlen' : acc'.length =
        (natField words.length ++ joined n words).length := by
      rw [← hacc, List.length_reverse]
    have hqLen : q'.length = words.length.bits.length := by
      simpa only [q] using hlen
    change b ≤ listWork n words.length.bits.length words at hb
    rw [hqLen] at hd
    rw [hlen'] at hd
    dsimp [canonicalTime]
    omega
  · rw [hrun]
    exact hhalt
  · rw [hrun, hout, hacc]

theorem source_canonical_run {η : ℚ}
    (S : EncodedETHSource.Sparsification η)
    (f : EncodedETHSource.ValidFormula) :
    ∃ t ≤ canonicalTime f.val.variables
        ((S.branches f).map fun g => EncodedCNF.encode g.val),
      (run t (startCfg f.val.variables
        (EncodedETHSource.formulaListBits (S.branches f)))).l = none ∧
      (run t (startCfg f.val.variables
        (EncodedETHSource.formulaListBits (S.branches f)))).stk (.inr 9) =
        SourceOriginalBranchPackets.packetList S f := by
  let words := (S.branches f).map fun g => EncodedCNF.encode g.val
  obtain ⟨t, ht, hh, ho⟩ := canonical_run f.val.variables words
  refine ⟨t, ht, ?_, ?_⟩
  · simpa only [words, EncodedETHSource.formulaListBits] using hh
  · have he := output_eq_packetList S f
    rw [← he]
    simpa only [words, EncodedETHSource.formulaListBits,
      List.length_map] using ho

end

end EthInapproximability.CurrentPaper.SourceOriginalListPacketizer
