import CurrentAdditive.GaussCoefficientProgram
import CurrentAdditive.GaussCoefficientTyped

namespace CurrentAdditive.GaussCoefficientProgram

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

noncomputable def parserStart (word : List Bool) :
    CurrentAdditive.GaussPackedParse64.Config :=
  ⟨some (.inl (.scan 0)), none,
    (CurrentAdditive.GaussPackedParse64.frame (fun _ => [])
      (BitMachineBankCodec.parserCfg (K := 3) (some (.scan 0)) none
        (fun _ => []) word [] [])).stk⟩

noncomputable def parserEnd (bank : BitMachineBankCodec.Bank 3) :
    CurrentAdditive.GaussPackedParse64.Config :=
  ⟨none, some true,
    (CurrentAdditive.GaussPackedParse64.frame (fun _ => [])
      (BitMachineBankCodec.parserCfg none (some true) bank [] [] [])).stk⟩

theorem initial_eq_parser_frame (word : List Bool) :
    initial word =
      BitMachineStackEmbedding.cfg parseSlots (initialStack word)
        Label.parse parseEmbed (some .bridgeParse)
        (parserStart word) := by
  have hb : BitMachineStackEmbedding.bank parseSlots
      (initialStack word) (parserStart word).stk = initialStack word := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro k
    rfl
  simp only [BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg]
  rw [hb]
  rfl

theorem parser_phase (bank : BitMachineBankCodec.Bank 3) :
    ∃ t ≤ 7 * ((BitMachineBankCodec.encode bank).length + 1),
      run t (initial (BitMachineBankCodec.encode bank)) =
        BitMachineStackEmbedding.cfg parseSlots
          (initialStack (BitMachineBankCodec.encode bank))
          Label.parse parseEmbed (some .bridgeParse)
          (parserEnd bank) := by
  obtain ⟨tp, htp, hp0⟩ :=
    CurrentAdditive.GaussPackedParse64.parse_encoded bank (fun _ => [])
  have hp : CurrentAdditive.GaussPackedParse64.run tp
      (parserStart (BitMachineBankCodec.encode bank)) = parserEnd bank := by
    simpa only [parserStart, parserEnd,
      CurrentAdditive.GaussPackedParse64.frame,
      BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg] using hp0
  have hh : (((advance Parse.program)^[tp])
      (parserStart (BitMachineBankCodec.encode bank))).l = none := by
    simpa only [parserStart, CurrentAdditive.GaussPackedParse64.run]
      using congrArg TM2.Cfg.l hp
  obtain ⟨t, ht, hr⟩ :=
    BitMachineStackEmbedding.outputs parseSlots
      (initialStack (BitMachineBankCodec.encode bank))
      Label.parse parseEmbed (fun s => s.1.1)
      (by intro s; rfl) (some .bridgeParse)
      Parse.program program (by intro l; rfl)
      (parserStart (BitMachineBankCodec.encode bank)) tp hh
  refine ⟨t, ht.trans htp, ?_⟩
  rw [initial_eq_parser_frame]
  exact hr.trans (congrArg
    (BitMachineStackEmbedding.cfg parseSlots
      (initialStack (BitMachineBankCodec.encode bank))
      Label.parse parseEmbed (some .bridgeParse))
    (by simpa only [parserStart, parserEnd,
        CurrentAdditive.GaussPackedParse64.run] using hp))

theorem bridge_parse (S : Stack → List Bool) (v : Parse.Control) :
    run 1 ⟨some .bridgeParse, parseEmbed v, S⟩ =
      ⟨some (.copyJ .scan), copyEmbed none, S⟩ := by
  simp [run, advance, TM2.step, TM2.stepAux, program]

theorem copyJ_phase (S : Stack → List Bool) (j : Nat)
    (hsource : S (copyJSlots 0) = List.replicate j true)
    (hfirst : S (copyJSlots 1) = [])
    (hsecond : S (copyJSlots 2) = [])
    (htemp : S (copyJSlots 3) = []) :
    ∃ t ≤ 2*j+2,
      run t ⟨some (.copyJ .scan), copyEmbed none, S⟩ =
        BitMachineStackEmbedding.cfg copyJSlots S
          Label.copyJ copyEmbed (some (.copyF .scan))
          (Copy.cfg none none (List.replicate j true)
            (List.replicate j true) (List.replicate j true) []) := by
  let c := Copy.cfg (some .scan) none (List.replicate j true) [] [] []
  have hhalt : (((advance Copy.program)^[2*j+2]) c).l = none := by
    simpa only [c, Copy.run] using congrArg TM2.Cfg.l (Copy.run_unary j)
  obtain ⟨t, ht, hr⟩ :=
    BitMachineStackEmbedding.outputs copyJSlots S Label.copyJ
      copyEmbed (fun s => s.1.2.1) (by intro s; rfl)
      (some (.copyF .scan)) Copy.program program
      (by intro l; rfl) c (2*j+2) hhalt
  have hstart : BitMachineStackEmbedding.cfg copyJSlots S
      Label.copyJ copyEmbed (some (.copyF .scan)) c =
      (⟨some (.copyJ .scan), copyEmbed none, S⟩ : Config) := by
    have hb : BitMachineStackEmbedding.bank copyJSlots S c.stk = S := by
      apply BitMachineStackEmbedding.bank_eq_self
      intro i
      fin_cases i <;> simp [c, Copy.cfg,
        CurrentAdditive.GaussUnaryDoubleCopy.bank,
        hsource, hfirst, hsecond, htemp]
    simp only [BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg]
    rw [hb]
    rfl
  refine ⟨t, ht, ?_⟩
  rw [← hstart]
  exact hr.trans (congrArg
    (BitMachineStackEmbedding.cfg copyJSlots S Label.copyJ copyEmbed
      (some (.copyF .scan)))
    (by simpa only [c, Copy.run] using Copy.run_unary j))

theorem copyF_phase (S : Stack → List Bool) (f : Nat)
    (hsource : S (copyFSlots 0) = List.replicate f true)
    (hfirst : S (copyFSlots 1) = [])
    (hsecond : S (copyFSlots 2) = [])
    (htemp : S (copyFSlots 3) = []) :
    ∃ t ≤ 2*f+2,
      run t ⟨some (.copyF .scan), copyEmbed none, S⟩ =
        BitMachineStackEmbedding.cfg copyFSlots S
          Label.copyF copyEmbed (some .bridgeF)
          (Copy.cfg none none (List.replicate f true)
            (List.replicate f true) (List.replicate f true) []) := by
  let c := Copy.cfg (some .scan) none (List.replicate f true) [] [] []
  have hhalt : (((advance Copy.program)^[2*f+2]) c).l = none := by
    simpa only [c, Copy.run] using congrArg TM2.Cfg.l (Copy.run_unary f)
  obtain ⟨t, ht, hr⟩ :=
    BitMachineStackEmbedding.outputs copyFSlots S Label.copyF
      copyEmbed (fun s => s.1.2.1) (by intro s; rfl)
      (some .bridgeF) Copy.program program
      (by intro l; rfl) c (2*f+2) hhalt
  have hstart : BitMachineStackEmbedding.cfg copyFSlots S
      Label.copyF copyEmbed (some .bridgeF) c =
      (⟨some (.copyF .scan), copyEmbed none, S⟩ : Config) := by
    have hb : BitMachineStackEmbedding.bank copyFSlots S c.stk = S := by
      apply BitMachineStackEmbedding.bank_eq_self
      intro i
      fin_cases i <;> simp [c, Copy.cfg,
        CurrentAdditive.GaussUnaryDoubleCopy.bank,
        hsource, hfirst, hsecond, htemp]
    simp only [BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg]
    rw [hb]
    rfl
  refine ⟨t, ht, ?_⟩
  rw [← hstart]
  exact hr.trans (congrArg
    (BitMachineStackEmbedding.cfg copyFSlots S Label.copyF copyEmbed
      (some .bridgeF))
    (by simpa only [c, Copy.run] using Copy.run_unary f))

theorem bridge_F (S : Stack → List Bool) (v : Copy.Control) :
    run 1 ⟨some .bridgeF, copyEmbed v, S⟩ =
      ⟨some (.compare
        (EthInapproximability.CurrentPaper.BitMachineRawSequence.leftLabel
          EthInapproximability.CurrentPaper.EntryUnaryCompare.CL.loop)),
       compareEmbed compareInitial, S⟩ := by
  simp [run, advance, TM2.step, TM2.stepAux, program]

def compareFinal (j f : Nat) : Compare.Bank :=
  Function.update
    (Function.update
      (Function.update
        (Function.update
          (Function.update
            (Function.update (Compare.initial j f) 0 []) 1 [])
              2 [decide (j < f)]) 3 []) 4 [])
      5 [decide (j = f)]

theorem compare_phase (S : Stack → List Bool) (j f : Nat)
    (hbank : ∀ i : Fin 6, S (compareSlots i) = (Compare.initial j f) i) :
    ∃ t ≤ 2 * (max j f + 2) + 1, ∃ v,
      run t
        ⟨some (.compare
          (EthInapproximability.CurrentPaper.BitMachineRawSequence.leftLabel
            EthInapproximability.CurrentPaper.EntryUnaryCompare.CL.loop)),
          compareEmbed compareInitial, S⟩ =
        BitMachineStackEmbedding.cfg compareSlots S
          Label.compare compareEmbed (some .decide)
          (⟨none, v, compareFinal j f⟩ :
            TM2.Cfg (fun _ : Fin 6 => Bool) Compare.Label Compare.Control) := by
  obtain ⟨tc, htc, v, hc⟩ := Compare.local_run j f
  let c : TM2.Cfg (fun _ : Fin 6 => Bool) Compare.Label Compare.Control :=
    ⟨some (EthInapproximability.CurrentPaper.BitMachineRawSequence.leftLabel
      EthInapproximability.CurrentPaper.EntryUnaryCompare.CL.loop),
      compareInitial, Compare.initial j f⟩
  have hh : (((advance Compare.program)^[tc]) c).l = none := by
    simpa only [c, compareInitial] using congrArg TM2.Cfg.l hc
  obtain ⟨t, ht, hr⟩ :=
    BitMachineStackEmbedding.outputs compareSlots S Label.compare
      compareEmbed (fun s => s.1.2.2.1) (by intro s; rfl)
      (some .decide) Compare.program program
      (by intro l; rfl) c tc hh
  have hstart : BitMachineStackEmbedding.cfg compareSlots S
      Label.compare compareEmbed (some .decide) c =
      (⟨some (.compare
        (EthInapproximability.CurrentPaper.BitMachineRawSequence.leftLabel
          EthInapproximability.CurrentPaper.EntryUnaryCompare.CL.loop)),
        compareEmbed compareInitial, S⟩ : Config) := by
    have hb : BitMachineStackEmbedding.bank compareSlots S c.stk = S := by
      apply BitMachineStackEmbedding.bank_eq_self
      intro i
      exact (hbank i).symm
    simp only [BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg]
    rw [hb]
  refine ⟨t, ht.trans htc, v, ?_⟩
  rw [← hstart]
  exact hr.trans (congrArg
    (BitMachineStackEmbedding.cfg compareSlots S Label.compare compareEmbed
      (some .decide))
    (by simpa only [c, compareInitial, compareFinal,
        CurrentAdditive.GaussPreparedColumnDecision.A₀,
        CurrentAdditive.GaussPreparedColumnDecision.B₀,
        CurrentAdditive.GaussPreparedColumnDecision.O₀,
        CurrentAdditive.GaussPreparedColumnDecision.A₁,
        CurrentAdditive.GaussPreparedColumnDecision.B₁,
        CurrentAdditive.GaussPreparedColumnDecision.O₁] using hc))

theorem decide_true (S : Stack → List Bool) (v : Compare.Control)
    (h : S (.inr (.inl 2)) = [true]) :
    run 1 ⟨some .decide, compareEmbed v, S⟩ =
      ⟨some .bridgeGetter, ((compareEmbed v).1, some true), S⟩ := by
  simp [run, advance, TM2.step, TM2.stepAux, program, h]

theorem decide_false (S : Stack → List Bool) (v : Compare.Control)
    (h : S (.inr (.inl 2)) = [false]) :
    run 1 ⟨some .decide, compareEmbed v, S⟩ =
      ⟨some .nonless, ((compareEmbed v).1, some false), S⟩ := by
  simp [run, advance, TM2.step, TM2.stepAux, program, h]

theorem writeWord_step (word : List Bool) (S : Stack → List Bool)
    (v : Control) :
    TM2.stepAux (writeWord word) v S =
      ⟨none, v,
        Function.update S (.inl 38) (word.reverse ++ S (.inl 38))⟩ := by
  induction word generalizing S with
  | nil => simp [writeWord]
  | cons b bs ih =>
      simp only [writeWord, TM2.stepAux.eq_1]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc,
        Function.update_idem]

theorem write_negOne (S : Stack → List Bool) (v : Control) :
    run 1 ⟨some .writeNegOne, v, S⟩ =
      ⟨none, v,
        Function.update S (.inl 38) (negOneWord ++ S (.inl 38))⟩ := by
  simp [run, advance, TM2.step, program, writeWord_step]

theorem write_zero (S : Stack → List Bool) (v : Control) :
    run 1 ⟨some .writeZero, v, S⟩ =
      ⟨none, v,
        Function.update S (.inl 38) (zeroWord ++ S (.inl 38))⟩ := by
  simp [run, advance, TM2.step, program, writeWord_step]

theorem bridge_getter (S : Stack → List Bool) (v : Control) :
    run 1 ⟨some .bridgeGetter, v, S⟩ =
      ⟨some (.getter
        (EthInapproximability.CurrentPaper.BitMachineRawSequence.leftLabel
          (EthInapproximability.CurrentPaper.BitMachineRawSequence.leftLabel
            (EthInapproximability.CurrentPaper.BitMachineRawSequence.leftLabel
              (.clear 0))))), getterEmbed getterInitial, S⟩ := by
  simp [run, advance, TM2.step, TM2.stepAux, program]

theorem nonless_true (S : Stack → List Bool) (v : Control)
    (h : S (.inr (.inl 5)) = [true]) :
    run 1 ⟨some .nonless, v, S⟩ =
      ⟨some .writeNegOne, (v.1, some true), S⟩ := by
  simp [run, advance, TM2.step, TM2.stepAux, program, h]

theorem nonless_false (S : Stack → List Bool) (v : Control)
    (h : S (.inr (.inl 5)) = [false]) :
    run 1 ⟨some .nonless, v, S⟩ =
      ⟨some .writeZero, (v.1, some false), S⟩ := by
  simp [run, advance, TM2.step, TM2.stepAux, program, h]

noncomputable def parsedStack (bank : BitMachineBankCodec.Bank 3) :
    Stack → List Bool :=
  (BitMachineStackEmbedding.cfg parseSlots
    (initialStack (BitMachineBankCodec.encode bank))
    Label.parse parseEmbed (some .bridgeParse) (parserEnd bank)).stk

theorem parsed_bank (bank : BitMachineBankCodec.Bank 3) (p : Fin 3) :
    parsedStack bank (.inl (![8, 15, 16] p)) = bank p := by
  have ho := BitMachineStackEmbedding.bank_at parseSlots
    (initialStack (BitMachineBankCodec.encode bank))
    (parserEnd bank).stk (![8, 15, 16] p)
  have hi := CurrentAdditive.GaussPackedParse64.parsed_field bank
    (fun _ => []) p
  simpa only [parsedStack, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    parserEnd, CurrentAdditive.GaussPackedParse64.frame,
    BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg, CurrentAdditive.GaussPackedParse64.locate,
    parseSlots] using ho.trans hi

theorem parsed_external (bank : BitMachineBankCodec.Bank 3)
    (i : Fin 6 ⊕ Fin 1) : parsedStack bank (.inr i) = [] := by
  have ho : ¬ ∃ k : Parse.Stack, parseSlots k = (.inr i : Stack) := by
    intro ⟨k, h⟩
    cases h
  have h := BitMachineStackEmbedding.bank_outside parseSlots
    (initialStack (BitMachineBankCodec.encode bank))
    (parserEnd bank).stk (.inr i) ho
  simpa only [parsedStack, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    initialStack] using h

theorem parsed_internal_empty (bank : BitMachineBankCodec.Bank 3)
    (i : Fin 64)
    (hi : ¬ ∃ k : BitMachineBankCodec.Stack 3,
      CurrentAdditive.GaussPackedParse64.locate k = i) :
    parsedStack bank (.inl i) = [] := by
  have h₁ := BitMachineStackEmbedding.bank_at parseSlots
    (initialStack (BitMachineBankCodec.encode bank))
    (parserEnd bank).stk i
  have h₂ := BitMachineStackEmbedding.bank_outside
    CurrentAdditive.GaussPackedParse64.locate (fun _ => [])
    (BitMachineBankCodec.parserCfg none (some true) bank [] [] []).stk i hi
  simpa only [parsedStack, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    parserEnd, CurrentAdditive.GaussPackedParse64.frame,
    BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg, initialStack] using h₁.trans h₂

theorem parsed38_empty (bank : BitMachineBankCodec.Bank 3) :
    parsedStack bank (.inl 38) = [] := by
  apply parsed_internal_empty bank 38
  · intro ⟨k, h⟩
    cases k with
    | inl p => fin_cases p <;> simp_all [CurrentAdditive.GaussPackedParse64.locate]
    | inr p => fin_cases p <;> simp_all [CurrentAdditive.GaussPackedParse64.locate]

theorem parsed63_empty (bank : BitMachineBankCodec.Bank 3) :
    parsedStack bank (.inl 63) = [] := by
  apply parsed_internal_empty bank 63
  · intro ⟨k, h⟩
    cases k with
    | inl p => fin_cases p <;> simp_all [CurrentAdditive.GaussPackedParse64.locate]
    | inr p => fin_cases p <;> simp_all [CurrentAdditive.GaussPackedParse64.locate]

noncomputable def afterJ (bank : BitMachineBankCodec.Bank 3) (j : Nat) :
    Stack → List Bool :=
  BitMachineStackEmbedding.bank copyJSlots (parsedStack bank)
    (Copy.cfg none none (List.replicate j true)
      (List.replicate j true) (List.replicate j true) []).stk

theorem afterJ_at (bank : BitMachineBankCodec.Bank 3) (j : Nat)
    (i : Copy.Stack) :
    afterJ bank j (copyJSlots i) =
      (Copy.cfg none none (List.replicate j true)
        (List.replicate j true) (List.replicate j true) []).stk i := by
  exact BitMachineStackEmbedding.bank_at copyJSlots (parsedStack bank) _ i

theorem afterJ_outside (bank : BitMachineBankCodec.Bank 3) (j : Nat)
    (i : Stack) (hi : ¬ ∃ k : Copy.Stack, copyJSlots k = i) :
    afterJ bank j i = parsedStack bank i := by
  exact BitMachineStackEmbedding.bank_outside copyJSlots (parsedStack bank) _ i hi

theorem afterJ_copyF_source (bank : BitMachineBankCodec.Bank 3)
    (j : Nat) : afterJ bank j (.inl 16) = bank 2 := by
  rw [afterJ_outside]
  · simpa using parsed_bank bank 2
  · intro ⟨k, h⟩
    fin_cases k <;> simp_all [copyJSlots, copyJSlot]

theorem afterJ_copyF_empty (bank : BitMachineBankCodec.Bank 3)
    (j : Nat) :
    afterJ bank j (.inr (.inl 1)) = [] ∧
    afterJ bank j (.inr (.inl 4)) = [] ∧
    afterJ bank j (.inr (.inr 0)) = [] := by
  constructor
  · rw [afterJ_outside]
    · exact parsed_external bank (.inl 1)
    · intro ⟨k, h⟩
      fin_cases k <;> simp_all [copyJSlots, copyJSlot]
  constructor
  · rw [afterJ_outside]
    · exact parsed_external bank (.inl 4)
    · intro ⟨k, h⟩
      fin_cases k <;> simp_all [copyJSlots, copyJSlot]
  · simpa [copyJSlots, copyJSlot, Copy.cfg,
      CurrentAdditive.GaussUnaryDoubleCopy.bank] using afterJ_at bank j 3

noncomputable def afterF (bank : BitMachineBankCodec.Bank 3)
    (j f : Nat) : Stack → List Bool :=
  BitMachineStackEmbedding.bank copyFSlots (afterJ bank j)
    (Copy.cfg none none (List.replicate f true)
      (List.replicate f true) (List.replicate f true) []).stk

theorem afterF_at (bank : BitMachineBankCodec.Bank 3) (j f : Nat)
    (i : Copy.Stack) :
    afterF bank j f (copyFSlots i) =
      (Copy.cfg none none (List.replicate f true)
        (List.replicate f true) (List.replicate f true) []).stk i := by
  exact BitMachineStackEmbedding.bank_at copyFSlots (afterJ bank j) _ i

theorem afterF_outside (bank : BitMachineBankCodec.Bank 3) (j f : Nat)
    (i : Stack) (hi : ¬ ∃ k : Copy.Stack, copyFSlots k = i) :
    afterF bank j f i = afterJ bank j i := by
  exact BitMachineStackEmbedding.bank_outside copyFSlots (afterJ bank j) _ i hi

theorem afterF_compare_bank (bank : BitMachineBankCodec.Bank 3)
    (j f : Nat) :
    ∀ i : Fin 6, afterF bank j f (compareSlots i) =
      (Compare.initial j f) i := by
  intro i
  fin_cases i
  · rw [afterF_outside]
    · simpa [compareSlots, copyJSlots, copyJSlot, Copy.cfg,
        CurrentAdditive.GaussUnaryDoubleCopy.bank,
        Compare.initial] using afterJ_at bank j 1
    · intro ⟨k, h⟩
      fin_cases k <;> simp_all [copyFSlots, copyFSlot, compareSlots]

  · simpa [compareSlots, copyFSlots, copyFSlot, Copy.cfg,
      CurrentAdditive.GaussUnaryDoubleCopy.bank,
      Compare.initial] using afterF_at bank j f 1
  · rw [afterF_outside]
    · rw [afterJ_outside]
      · simpa [compareSlots, Compare.initial] using
          parsed_external bank (.inl 2)
      · intro ⟨k, h⟩
        fin_cases k <;> simp_all [copyJSlots, copyJSlot, compareSlots]
    · intro ⟨k, h⟩
      fin_cases k <;> simp_all [copyFSlots, copyFSlot, compareSlots]
  · rw [afterF_outside]
    · simpa [compareSlots, copyJSlots, copyJSlot, Copy.cfg,
        CurrentAdditive.GaussUnaryDoubleCopy.bank,
        Compare.initial] using afterJ_at bank j 2
    · intro ⟨k, h⟩
      fin_cases k <;> simp_all [copyFSlots, copyFSlot, compareSlots]
  · simpa [compareSlots, copyFSlots, copyFSlot, Copy.cfg,
      CurrentAdditive.GaussUnaryDoubleCopy.bank,
      Compare.initial] using afterF_at bank j f 2
  · rw [afterF_outside]
    · rw [afterJ_outside]
      · simpa [compareSlots, Compare.initial] using
          parsed_external bank (.inl 5)
      · intro ⟨k, h⟩
        fin_cases k <;> simp_all [copyJSlots, copyJSlot, compareSlots]
    · intro ⟨k, h⟩
      fin_cases k <;> simp_all [copyFSlots, copyFSlot, compareSlots]

theorem prepared_phase (bank : BitMachineBankCodec.Bank 3) (j f : Nat)
    (hj : bank 1 = List.replicate j true)
    (hf : bank 2 = List.replicate f true) :
    ∃ t ≤ 7 * ((BitMachineBankCodec.encode bank).length + 1) +
        1 + (2*j+2) + (2*f+2) + 1,
      run t (initial (BitMachineBankCodec.encode bank)) =
        ⟨some (.compare
          (EthInapproximability.CurrentPaper.BitMachineRawSequence.leftLabel
            EthInapproximability.CurrentPaper.EntryUnaryCompare.CL.loop)),
          compareEmbed compareInitial, afterF bank j f⟩ := by
  obtain ⟨tp, htp, hp⟩ := parser_phase bank
  have hp' : run tp (initial (BitMachineBankCodec.encode bank)) =
      ⟨some .bridgeParse, parseEmbed (some true), parsedStack bank⟩ := by
    rw [hp]
    rfl
  have hjsource : (parsedStack bank) (copyJSlots 0) =
      List.replicate j true := by
    simpa [copyJSlots, copyJSlot, hj] using parsed_bank bank 1
  have hjfirst : (parsedStack bank) (copyJSlots 1) = [] := by
    simpa [copyJSlots, copyJSlot] using parsed_external bank (.inl 0)
  have hjsecond : (parsedStack bank) (copyJSlots 2) = [] := by
    simpa [copyJSlots, copyJSlot] using parsed_external bank (.inl 3)
  have hjtemp : (parsedStack bank) (copyJSlots 3) = [] := by
    simpa [copyJSlots, copyJSlot] using parsed_external bank (.inr 0)
  obtain ⟨tj, htj, hrunj⟩ :=
    copyJ_phase (parsedStack bank) j hjsource hjfirst hjsecond hjtemp
  have hrunj' : run tj
      ⟨some (.copyJ .scan), copyEmbed none, parsedStack bank⟩ =
      ⟨some (.copyF .scan), copyEmbed none, afterJ bank j⟩ := by
    rw [hrunj]
    rfl
  have hfsource : (afterJ bank j) (copyFSlots 0) =
      List.replicate f true := by
    simpa [copyFSlots, copyFSlot, hf] using afterJ_copyF_source bank j
  have hfempty := afterJ_copyF_empty bank j
  obtain ⟨tf, htf, hrunf⟩ :=
    copyF_phase (afterJ bank j) f hfsource
      (by simpa [copyFSlots, copyFSlot] using hfempty.1)
      (by simpa [copyFSlots, copyFSlot] using hfempty.2.1)
      (by simpa [copyFSlots, copyFSlot] using hfempty.2.2)
  have hrunf' : run tf
      ⟨some (.copyF .scan), copyEmbed none, afterJ bank j⟩ =
      ⟨some .bridgeF, copyEmbed none, afterF bank j f⟩ := by
    rw [hrunf]
    rfl
  refine ⟨tp + 1 + tj + tf + 1, by omega, ?_⟩
  rw [run_add, run_add, run_add, run_add, hp', bridge_parse,
    hrunj', hrunf', bridge_F]

noncomputable def comparedStack (bank : BitMachineBankCodec.Bank 3)
    (j f : Nat) : Stack → List Bool :=
  BitMachineStackEmbedding.bank compareSlots (afterF bank j f)
    (compareFinal j f)

theorem compared_lt (bank : BitMachineBankCodec.Bank 3)
    (j f : Nat) :
    comparedStack bank j f (.inr (.inl 2)) = [decide (j < f)] := by
  have h := BitMachineStackEmbedding.bank_at compareSlots
    (afterF bank j f) (compareFinal j f) 2
  simpa [comparedStack, compareSlots, compareFinal] using h

theorem compared_eq (bank : BitMachineBankCodec.Bank 3)
    (j f : Nat) :
    comparedStack bank j f (.inr (.inl 5)) = [decide (j = f)] := by
  have h := BitMachineStackEmbedding.bank_at compareSlots
    (afterF bank j f) (compareFinal j f) 5
  simpa [comparedStack, compareSlots, compareFinal] using h

theorem compared_phase (bank : BitMachineBankCodec.Bank 3) (j f : Nat)
    (hj : bank 1 = List.replicate j true)
    (hf : bank 2 = List.replicate f true) :
    ∃ t ≤ 7 * ((BitMachineBankCodec.encode bank).length + 1) +
        1 + (2*j+2) + (2*f+2) + 1 +
        (2 * (max j f + 2) + 1), ∃ v,
      run t (initial (BitMachineBankCodec.encode bank)) =
        ⟨some .decide, compareEmbed v, comparedStack bank j f⟩ := by
  obtain ⟨tp, htp, hp⟩ := prepared_phase bank j f hj hf
  obtain ⟨tc, htc, v, hc⟩ :=
    compare_phase (afterF bank j f) j f
      (afterF_compare_bank bank j f)
  refine ⟨tp+tc, by omega, v, ?_⟩
  rw [run_add, hp, hc]
  rfl

theorem compared_internal_unselected (bank : BitMachineBankCodec.Bank 3)
    (j f : Nat) (i : Fin 64) (h15 : i ≠ 15) (h16 : i ≠ 16) :
    comparedStack bank j f (.inl i) = parsedStack bank (.inl i) := by
  unfold comparedStack
  rw [BitMachineStackEmbedding.bank_outside compareSlots]
  · rw [afterF_outside]
    · apply afterJ_outside
      intro ⟨k, h⟩
      fin_cases k <;> simp_all [copyJSlots, copyJSlot]
    · intro ⟨k, h⟩
      fin_cases k <;> simp_all [copyFSlots, copyFSlot]
  · intro ⟨k, h⟩
    cases h

theorem compared38_empty (bank : BitMachineBankCodec.Bank 3)
    (j f : Nat) : comparedStack bank j f (.inl 38) = [] := by
  rw [compared_internal_unselected bank j f 38 (by decide) (by decide)]
  exact parsed38_empty bank

theorem compared63_empty (bank : BitMachineBankCodec.Bank 3)
    (j f : Nat) : comparedStack bank j f (.inl 63) = [] := by
  rw [compared_internal_unselected bank j f 63 (by decide) (by decide)]
  exact parsed63_empty bank

theorem compared_matrix (bank : BitMachineBankCodec.Bank 3)
    (j f : Nat) : comparedStack bank j f (.inl 8) = bank 0 := by
  rw [compared_internal_unselected bank j f 8 (by decide) (by decide)]
  simpa using parsed_bank bank 0

theorem compared_row (bank : BitMachineBankCodec.Bank 3)
    (j f : Nat) : comparedStack bank j f (.inl 15) =
      List.replicate j true := by
  unfold comparedStack
  rw [BitMachineStackEmbedding.bank_outside compareSlots]
  · rw [afterF_outside]
    · simpa [copyJSlots, copyJSlot, Copy.cfg,
        CurrentAdditive.GaussUnaryDoubleCopy.bank] using afterJ_at bank j 0
    · intro ⟨k, h⟩
      fin_cases k <;> simp_all [copyFSlots, copyFSlot]
  · intro ⟨k, h⟩
    cases h

theorem compared_column (bank : BitMachineBankCodec.Bank 3)
    (j f : Nat) : comparedStack bank j f (.inl 16) =
      List.replicate f true := by
  unfold comparedStack
  rw [BitMachineStackEmbedding.bank_outside compareSlots]
  · simpa [copyFSlots, copyFSlot, Copy.cfg,
      CurrentAdditive.GaussUnaryDoubleCopy.bank] using afterF_at bank j f 0
  · intro ⟨k, h⟩
    cases h

theorem compared_reset_empty (bank : BitMachineBankCodec.Bank 3)
    (j f : Nat) (r : Fin 21) :
    comparedStack bank j f
      (.inl (CurrentAdditive.GaussGetterReset64.resetBank r)) = [] := by
  have hr : 32 ≤ (CurrentAdditive.GaussGetterReset64.resetBank r).val ∧
      (CurrentAdditive.GaussGetterReset64.resetBank r).val < 53 := by
    fin_cases r <;> decide
  have h15 : CurrentAdditive.GaussGetterReset64.resetBank r ≠
      (15 : Fin 64) := by
    intro h
    have := congrArg Fin.val h
    omega
  have h16 : CurrentAdditive.GaussGetterReset64.resetBank r ≠
      (16 : Fin 64) := by
    intro h
    have := congrArg Fin.val h
    omega
  rw [compared_internal_unselected bank j f _ h15 h16]
  apply parsed_internal_empty
  rintro ⟨q, hq⟩
  cases q with
  | inl q =>
      fin_cases q <;> have hv := congrArg Fin.val hq <;>
        simp [CurrentAdditive.GaussPackedParse64.locate] at hv <;> omega
  | inr q =>
      fin_cases q <;> have hv := congrArg Fin.val hq <;>
        simp [CurrentAdditive.GaussPackedParse64.locate] at hv <;> omega

theorem compared_preparation_clock (bank : BitMachineBankCodec.Bank 3)
    (j f : Nat) :
    Getter.preparationClock
      (fun i => comparedStack bank j f (.inl i)) j f =
      2*j + 2*f + 31 := by
  simp [CurrentAdditive.GaussOneFetchProgram64.preparationClock,
    CurrentAdditive.GaussOneFetchProgram64.resetClock,
    CurrentAdditive.GaussOneFetchProgram64.copyClock,
    compared_reset_empty]
  omega

theorem nonless_output (bank : BitMachineBankCodec.Bank 3)
    (j f : Nat)
    (hj : bank 1 = List.replicate j true)
    (hf : bank 2 = List.replicate f true)
    (hlt : ¬ j < f) :
    ∃ t ≤ 7 * ((BitMachineBankCodec.encode bank).length + 1) +
        1 + (2*j+2) + (2*f+2) + 1 +
        (2 * (max j f + 2) + 1) + 3,
      (run t (initial (BitMachineBankCodec.encode bank))).l = none ∧
      (run t (initial (BitMachineBankCodec.encode bank))).stk (.inl 38) =
        if j = f then negOneWord else zeroWord := by
  obtain ⟨tc, htc, v, hc⟩ := compared_phase bank j f hj hf
  have hflag : comparedStack bank j f (.inr (.inl 2)) = [false] := by
    simpa [hlt] using compared_lt bank j f
  by_cases heq : j = f
  · have heqflag : comparedStack bank j f (.inr (.inl 5)) = [true] := by
      simpa [heq] using compared_eq bank j f
    refine ⟨tc+3, by omega, ?_, ?_⟩
    · rw [run_add, hc]
      simp only [show (3:Nat) = 1+1+1 by omega, run_add]
      rw [decide_false _ _ hflag, nonless_true _ _ heqflag,
        write_negOne]
    · rw [run_add, hc]
      simp only [show (3:Nat) = 1+1+1 by omega, run_add]
      rw [decide_false _ _ hflag, nonless_true _ _ heqflag,
        write_negOne]
      simp [compared38_empty, heq]
  · have heqflag : comparedStack bank j f (.inr (.inl 5)) = [false] := by
      simpa [heq] using compared_eq bank j f
    refine ⟨tc+3, by omega, ?_, ?_⟩
    · rw [run_add, hc]
      simp only [show (3:Nat) = 1+1+1 by omega, run_add]
      rw [decide_false _ _ hflag, nonless_false _ _ heqflag,
        write_zero]
    · rw [run_add, hc]
      simp only [show (3:Nat) = 1+1+1 by omega, run_add]
      rw [decide_false _ _ hflag, nonless_false _ _ heqflag,
        write_zero]
      simp [compared38_empty, heq]

theorem getter_phase
    (rowPre rowSuffix cellPre cellSuffix : List (List Bool))
    (cell : List Bool) (S : Stack → List Bool)
    (hmat : S (.inl 8) = SourceListEncoding.encode
      (rowPre ++ SourceListEncoding.encode
        (cellPre ++ cell :: cellSuffix) :: rowSuffix))
    (hrow : S (.inl 15) = List.replicate rowPre.length true)
    (hcolumn : S (.inl 16) = List.replicate cellPre.length true)
    (htemp : S (.inl 63) = []) :
    let SG : Getter.Stack → List Bool := fun i => S (.inl i)
    let matrix := SourceListEncoding.encode
      (rowPre ++ SourceListEncoding.encode
        (cellPre ++ cell :: cellSuffix) :: rowSuffix)
    ∃ t ≤ Getter.preparationClock SG rowPre.length cellPre.length +
        140 * (matrix.length + 1)^3 + 1,
      (run t ⟨some (.getter
        (EthInapproximability.CurrentPaper.BitMachineRawSequence.leftLabel
          (EthInapproximability.CurrentPaper.BitMachineRawSequence.leftLabel
            (EthInapproximability.CurrentPaper.BitMachineRawSequence.leftLabel
              (.clear 0))))), getterEmbed getterInitial, S⟩).l = none ∧
      (run t ⟨some (.getter
        (EthInapproximability.CurrentPaper.BitMachineRawSequence.leftLabel
          (EthInapproximability.CurrentPaper.BitMachineRawSequence.leftLabel
            (EthInapproximability.CurrentPaper.BitMachineRawSequence.leftLabel
              (.clear 0))))), getterEmbed getterInitial, S⟩).stk (.inl 38) = cell := by
  dsimp only
  let SG : Getter.Stack → List Bool := fun i => S (.inl i)
  obtain ⟨tg, htg, hgh, hcell, _⟩ :=
    Getter.canonical_one_fetch rowPre rowSuffix cellPre cellSuffix cell SG
      hmat hrow hcolumn htemp
  have hhalt : (((advance Getter.program)^[tg]) (Getter.initial SG)).l =
      none := by simpa only [CurrentAdditive.GaussOneFetchProgram64.run] using hgh
  obtain ⟨t, ht, hr⟩ :=
    BitMachineStackEmbedding.outputs getterSlots S Label.getter
      getterEmbed (fun s => s.1.2.2.2) (by intro s; rfl)
      none Getter.program program (by intro l; rfl)
      (Getter.initial SG) tg hhalt
  have hstart : BitMachineStackEmbedding.cfg getterSlots S
      Label.getter getterEmbed none (Getter.initial SG) =
      (⟨some (.getter
        (EthInapproximability.CurrentPaper.BitMachineRawSequence.leftLabel
          (EthInapproximability.CurrentPaper.BitMachineRawSequence.leftLabel
            (EthInapproximability.CurrentPaper.BitMachineRawSequence.leftLabel
              (.clear 0))))), getterEmbed getterInitial, S⟩ : Config) := by
    have hb : BitMachineStackEmbedding.bank getterSlots S SG = S := by
      apply BitMachineStackEmbedding.bank_eq_self
      intro i
      rfl
    simp only [BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg]
    simp only [CurrentAdditive.GaussOneFetchProgram64.initial]
    rw [hb]
    rfl
  refine ⟨t, ht.trans htg, ?_, ?_⟩
  · rw [← hstart]
    change (((advance program)^[t]) _).l = none
    rw [hr]
    simp [BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg, hhalt]
  · rw [← hstart]
    change (((advance program)^[t]) _).stk (.inl 38) = cell
    rw [hr]
    simpa only [BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
      CurrentAdditive.GaussOneFetchProgram64.run] using
      (BitMachineStackEmbedding.bank_at getterSlots S
        (((advance Getter.program)^[tg]) (Getter.initial SG)).stk 38).trans hcell

theorem typed_getter_output {m k : Nat} (B : Fin m → Fin k → ℚ)
    (j f : Fin k) (hf : f.val ≤ m) (hlt : j.val < f.val) :
    let bank : BitMachineBankCodec.Bank 3 :=
      ![CurrentAdditive.GaussPhysical.encodeTypedMatrix B,
        List.replicate j.val true, List.replicate f.val true]
    let SG : Getter.Stack → List Bool :=
      fun i => comparedStack bank j.val f.val (.inl i)
    ∃ t ≤ 7 * ((BitMachineBankCodec.encode bank).length + 1) +
        1 + (2*j.val+2) + (2*f.val+2) + 1 +
        (2 * (max j.val f.val + 2) + 1) + 2 +
        Getter.preparationClock SG j.val f.val +
        140 * ((CurrentAdditive.GaussPhysical.encodeTypedMatrix B).length + 1)^3 + 1,
      (run t (initial (BitMachineBankCodec.encode bank))).l = none ∧
      (run t (initial (BitMachineBankCodec.encode bank))).stk (.inl 38) =
        CodeDCodec.encodeRawRat
          (CurrentAdditive.GaussPhysical.rawOfRat
            (B ⟨j.val, by omega⟩ f)) := by
  dsimp only
  let bank : BitMachineBankCodec.Bank 3 :=
    ![CurrentAdditive.GaussPhysical.encodeTypedMatrix B,
      List.replicate j.val true, List.replicate f.val true]
  let rowIndex : Fin m := ⟨j.val, by omega⟩
  let rowPre := (CurrentAdditive.GaussCoefficientTyped.rowWords B).take j.val
  let rowSuffix := (CurrentAdditive.GaussCoefficientTyped.rowWords B).drop (j.val+1)
  let cellPre := (CurrentAdditive.GaussCoefficientTyped.cellWords B rowIndex).take f.val
  let cellSuffix := (CurrentAdditive.GaussCoefficientTyped.cellWords B rowIndex).drop (f.val+1)
  let cell := CodeDCodec.encodeRawRat
    (CurrentAdditive.GaussPhysical.rawOfRat (B rowIndex f))
  obtain ⟨hm, hri, hcf⟩ :=
    CurrentAdditive.GaussCoefficientTyped.typed_decomposition B rowIndex f
  obtain ⟨tc, htc, v, hc⟩ := compared_phase bank j.val f.val
    (by rfl) (by rfl)
  have hflag : comparedStack bank j.val f.val (.inr (.inl 2)) = [true] := by
    simpa [hlt] using compared_lt bank j.val f.val
  have hmat : comparedStack bank j.val f.val (.inl 8) =
      SourceListEncoding.encode
        (rowPre ++ SourceListEncoding.encode
          (cellPre ++ cell :: cellSuffix) :: rowSuffix) := by
    rw [compared_matrix]
    exact hm
  have hrow : comparedStack bank j.val f.val (.inl 15) =
      List.replicate rowPre.length true := by
    rw [compared_row]
    rw [hri]
  have hcol : comparedStack bank j.val f.val (.inl 16) =
      List.replicate cellPre.length true := by
    rw [compared_column]
    rw [hcf]
  obtain ⟨tg, htg, hgh, hcell⟩ := getter_phase
    rowPre rowSuffix cellPre cellSuffix cell
    (comparedStack bank j.val f.val) hmat hrow hcol
    (compared63_empty bank j.val f.val)
  refine ⟨tc+1+1+tg, ?_, ?_, ?_⟩
  · have hmatrix : SourceListEncoding.encode
        (rowPre ++ SourceListEncoding.encode
          (cellPre ++ cell :: cellSuffix) :: rowSuffix) =
        CurrentAdditive.GaussPhysical.encodeTypedMatrix B := hm.symm
    rw [hmatrix] at htg
    rw [hri, hcf] at htg
    simp only [rowIndex, bank] at htg htc ⊢
    omega
  · rw [run_add, run_add, run_add, hc,
      decide_true _ _ hflag, bridge_getter]
    exact hgh
  · rw [run_add, run_add, run_add, hc,
      decide_true _ _ hflag, bridge_getter]
    exact hcell

end CurrentAdditive.GaussCoefficientProgram
