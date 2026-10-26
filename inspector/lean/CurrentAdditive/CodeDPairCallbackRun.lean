import CurrentAdditive.CodeDPairCallbackProgram
import CurrentAdditive.CodeDPairRecordABI

set_option maxHeartbeats 1000000

/-! Literal per-pair callback run, preserving the outer source context and
appending one correctly framed multiplication request. -/

namespace CurrentAdditive.CodeDPairCallbackRun

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open EthInapproximability.CurrentPaper.BitMachineBankCodec
open CurrentAdditive.CodeDPairCallbackProgram
open CurrentAdditive.CodeDPairRecordABI
open CurrentAdditive.CodeDSourceCodecV2
open CurrentAdditive.CodeDCodec
open CurrentAdditive.CodeDCanonicalSourceV2
open Turing BitMachineEncoding

def initialBank (x : Entry) (y : Nat × ℚ) (output : List Bool) :
    Stack → List Bool :=
  fun k => if k = 12 then encodeEntry x
    else if k = 6 then CurrentAdditive.CodeDTargetV2.alphabetEntry y
    else if k = 9 then output else []

def initial (x : Entry) (y : Nat × ℚ) (output : List Bool) : Config :=
  ⟨some (.copy (.inl .scan)), none, initialBank x y output⟩

noncomputable def afterCopy (x : Entry) (y : Nat × ℚ)
    (output : List Bool) : Stack → List Bool :=
  (CodeDSourceCopy15.frame (initialBank x y output)
    (BitMachineCopy.cfg none none (encodeEntry x) (encodeEntry x) [])).stk

private theorem copy_start (x : Entry) (y : Nat × ℚ) (output : List Bool) :
    (CodeDSourceCopy15.frame (initialBank x y output)
      (BitMachineCopy.cfg (some .scan) none (encodeEntry x) [] [])).stk =
      initialBank x y output := by
  unfold CodeDSourceCopy15.frame
  apply bank_eq_self CodeDSourceCopy15.locate
  intro k
  fin_cases k <;> simp [BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg, CodeDSourceCopy15.locate, BitMachineCopy.cfg,
    BitMachineCopy.stackContents, initialBank]

theorem copy_run (x : Entry) (y : Nat × ℚ) (output : List Bool) :
    ∃ t ≤ 2*(encodeEntry x).length+2,
      CodeDPairCallbackProgram.run t (initial x y output) =
        ⟨some (.copy (.inr ())), none, afterCopy x y output⟩ := by
  obtain ⟨t, ht, hr⟩ :=
    CodeDPairCallbackProgram.copy_phase (encodeEntry x) (initialBank x y output)
  refine ⟨t, ht, ?_⟩
  change CodeDPairCallbackProgram.run t
      ⟨some (.copy (.inl .scan)), none,
        (CodeDSourceCopy15.frame (initialBank x y output)
          (BitMachineCopy.cfg (some .scan) none (encodeEntry x) [] [])).stk⟩ =
      ⟨some (.copy (.inr ())), none,
        (CodeDSourceCopy15.frame (initialBank x y output)
          (BitMachineCopy.cfg none none (encodeEntry x) (encodeEntry x) [])).stk⟩ at hr
  rw [copy_start] at hr
  exact hr

noncomputable def afterSource (x : Entry) (y : Nat × ℚ)
    (output : List Bool) : Stack → List Bool :=
  (CodeDSourceBank2Field15.frame (afterCopy x y output)
    (parserCfg none (some true) (sourceBank x) [] [] [])).stk

private theorem afterCopy_at3 (x : Entry) (y : Nat × ℚ)
    (output : List Bool) : afterCopy x y output 3 = encodeEntry x := by
  exact (CodeDSourceCopy15.copied_banks (encodeEntry x)
    (initialBank x y output)).2.1

private theorem afterCopy_at14 (x : Entry) (y : Nat × ℚ)
    (output : List Bool) : afterCopy x y output 14 = [] := by
  change bank CodeDSourceCopy15.locate (initialBank x y output)
    (BitMachineCopy.cfg none none (encodeEntry x) (encodeEntry x) []).stk 14 = []
  rw [show (14 : Stack) = CodeDSourceCopy15.locate 2 by rfl,
    bank_at]
  rfl

private theorem afterCopy_other (x : Entry) (y : Nat × ℚ)
    (output : List Bool) (j : Stack)
    (hj : j ≠ 12 ∧ j ≠ 3 ∧ j ≠ 14) :
    afterCopy x y output j = initialBank x y output j := by
  change bank CodeDSourceCopy15.locate (initialBank x y output)
    (BitMachineCopy.cfg none none (encodeEntry x) (encodeEntry x) []).stk j = _
  apply bank_outside
  rintro ⟨k, hk⟩
  fin_cases k <;> simp_all [CodeDSourceCopy15.locate]

private theorem source_start (x : Entry) (y : Nat × ℚ)
    (output : List Bool) :
    (CodeDSourceBank2Field15.frame (afterCopy x y output)
      (parserCfg (some (.scan 0)) none (fun _ => [])
        (encodeEntry x) [] [])).stk = afterCopy x y output := by
  unfold CodeDSourceBank2Field15.frame
  apply bank_eq_self CodeDSourceBank2Field15.locate
  intro k
  cases k with
  | inl i =>
      fin_cases i
      · simpa [CodeDSourceBank2Field15.locate, parserCfg,
          BitMachineInline.cfg, BitMachineBankCodec.contents,
          initialBank] using
          (afterCopy_other x y output 1 (by decide))
      · simpa [CodeDSourceBank2Field15.locate, parserCfg,
          BitMachineInline.cfg, BitMachineBankCodec.contents,
          initialBank] using
          (afterCopy_other x y output 7 (by decide))
  | inr i =>
      fin_cases i
      · simpa [CodeDSourceBank2Field15.locate, parserCfg,
          BitMachineInline.cfg, BitMachineBankCodec.contents,
          source_record] using (afterCopy_at3 x y output).symm
      · simpa [CodeDSourceBank2Field15.locate, parserCfg,
          BitMachineInline.cfg, BitMachineBankCodec.contents]
          using (afterCopy_at14 x y output)
      · simpa [CodeDSourceBank2Field15.locate, parserCfg,
          BitMachineInline.cfg, BitMachineBankCodec.contents,
          initialBank] using
          (afterCopy_other x y output 11 (by decide))

theorem source_run (x : Entry) (y : Nat × ℚ) (output : List Bool) :
    ∃ t ≤ 5*((encodeEntry x).length+1),
      CodeDPairCallbackProgram.run t
        ⟨some (.source (.inl (.scan 0))), none, afterCopy x y output⟩ =
        ⟨some (.source (.inr ())), some true, afterSource x y output⟩ := by
  obtain ⟨t, ht, hr⟩ := CodeDPairCallbackProgram.source_phase
    (sourceBank x) (afterCopy x y output) []
  refine ⟨t, ?_, ?_⟩
  · simpa [source_record] using ht
  · change CodeDPairCallbackProgram.run t
        ⟨some (.source (.inl (.scan 0))), none,
          (CodeDSourceBank2Field15.frame (afterCopy x y output)
            (parserCfg (some (.scan 0)) none (fun _ => [])
              (encode (sourceBank x)) [] [])).stk⟩ =
        ⟨some (.source (.inr ())), some true, afterSource x y output⟩ at hr
    rw [source_record, source_start] at hr
    exact hr

noncomputable def afterAlphabet (x : Entry) (y : Nat × ℚ)
    (output : List Bool) : Stack → List Bool :=
  (CodeDAlphabetBank2Field15.frame (afterSource x y output)
    (parserCfg none (some true) (alphabetBank y) [] [] [])).stk

private theorem afterSource_other (x : Entry) (y : Nat × ℚ)
    (output : List Bool) (j : Stack)
    (hj : j ≠ 1 ∧ j ≠ 7 ∧ j ≠ 3 ∧ j ≠ 14 ∧ j ≠ 11) :
    afterSource x y output j = afterCopy x y output j := by
  change bank CodeDSourceBank2Field15.locate (afterCopy x y output)
    (parserCfg none (some true) (sourceBank x) [] [] []).stk j = _
  apply bank_outside
  rintro ⟨k, hk⟩
  cases k with
  | inl k => fin_cases k <;> simp_all [CodeDSourceBank2Field15.locate]
  | inr k => fin_cases k <;> simp_all [CodeDSourceBank2Field15.locate]

private theorem afterSource_at14 (x : Entry) (y : Nat × ℚ)
    (output : List Bool) : afterSource x y output 14 = [] := by
  change bank CodeDSourceBank2Field15.locate (afterCopy x y output)
    (parserCfg none (some true) (sourceBank x) [] [] []).stk 14 = []
  rw [show (14 : Stack) = CodeDSourceBank2Field15.locate (.inr 1) by rfl,
    bank_at]
  rfl

private theorem afterSource_at11 (x : Entry) (y : Nat × ℚ)
    (output : List Bool) : afterSource x y output 11 = [] := by
  change bank CodeDSourceBank2Field15.locate (afterCopy x y output)
    (parserCfg none (some true) (sourceBank x) [] [] []).stk 11 = []
  rw [show (11 : Stack) = CodeDSourceBank2Field15.locate (.inr 2) by rfl,
    bank_at]
  rfl

private theorem alphabet_start (x : Entry) (y : Nat × ℚ)
    (output : List Bool) :
    (CodeDAlphabetBank2Field15.frame (afterSource x y output)
      (parserCfg (some (.scan 0)) none (fun _ => [])
        (CurrentAdditive.CodeDTargetV2.alphabetEntry y) [] [])).stk =
      afterSource x y output := by
  unfold CodeDAlphabetBank2Field15.frame
  apply bank_eq_self CodeDAlphabetBank2Field15.locate
  intro k
  cases k with
  | inl i =>
      fin_cases i
      · have h0 := afterSource_other x y output 0 (by decide)
        have h00 := afterCopy_other x y output 0 (by decide)
        simpa [CodeDAlphabetBank2Field15.locate, parserCfg,
          BitMachineInline.cfg, BitMachineBankCodec.contents,
          initialBank] using h0.trans h00
      · have h5 := afterSource_other x y output 5 (by decide)
        have h50 := afterCopy_other x y output 5 (by decide)
        simpa [CodeDAlphabetBank2Field15.locate, parserCfg,
          BitMachineInline.cfg, BitMachineBankCodec.contents,
          initialBank] using h5.trans h50
  | inr i =>
      fin_cases i
      · have h6 := afterSource_other x y output 6 (by decide)
        have h60 := afterCopy_other x y output 6 (by decide)
        simpa [CodeDAlphabetBank2Field15.locate, parserCfg,
          BitMachineInline.cfg, BitMachineBankCodec.contents,
          initialBank] using (h6.trans h60).symm
      · simpa [CodeDAlphabetBank2Field15.locate, parserCfg,
          BitMachineInline.cfg, BitMachineBankCodec.contents]
          using afterSource_at14 x y output
      · simpa [CodeDAlphabetBank2Field15.locate, parserCfg,
          BitMachineInline.cfg, BitMachineBankCodec.contents]
          using afterSource_at11 x y output

theorem alphabet_run (x : Entry) (y : Nat × ℚ) (output : List Bool) :
    ∃ t ≤ 5*((CurrentAdditive.CodeDTargetV2.alphabetEntry y).length+1),
      CodeDPairCallbackProgram.run t
        ⟨some (.alphabet (.inl (.scan 0))), none, afterSource x y output⟩ =
        ⟨some (.alphabet (.inr ())), some true,
          afterAlphabet x y output⟩ := by
  obtain ⟨t, ht, hr⟩ := CodeDPairCallbackProgram.alphabet_phase
    (alphabetBank y) (afterSource x y output) []
  refine ⟨t, ?_, ?_⟩
  · simpa [alphabet_record] using ht
  · change CodeDPairCallbackProgram.run t
        ⟨some (.alphabet (.inl (.scan 0))), none,
          (CodeDAlphabetBank2Field15.frame (afterSource x y output)
            (parserCfg (some (.scan 0)) none (fun _ => [])
              (encode (alphabetBank y)) [] [])).stk⟩ =
        ⟨some (.alphabet (.inr ())), some true,
          afterAlphabet x y output⟩ at hr
    rw [alphabet_record, alphabet_start] at hr
    exact hr

noncomputable def afterPair (x : Entry) (y : Nat × ℚ)
    (output : List Bool) (S' : BitMachineBankSerialize.Bank 2) :
    Stack → List Bool :=
  (CodeDPairWeights15.frame (afterAlphabet x y output)
    (BitMachineBankSerialize.cfg none none S' [] []
      (CodeDPairProductTargetV2.pairBytes x.weight
        (rawOfRat y.2)))).stk

private theorem afterSource_at7 (x : Entry) (y : Nat × ℚ)
    (output : List Bool) :
    afterSource x y output 7 = encodeRawRat x.weight := by
  change bank CodeDSourceBank2Field15.locate (afterCopy x y output)
    (parserCfg none (some true) (sourceBank x) [] [] []).stk 7 = _
  rw [show (7 : Stack) = CodeDSourceBank2Field15.locate (.inl 1) by rfl,
    bank_at]
  rfl

private theorem afterAlphabet_at5 (x : Entry) (y : Nat × ℚ)
    (output : List Bool) :
    afterAlphabet x y output 5 = encodeRawRat (rawOfRat y.2) := by
  change bank CodeDAlphabetBank2Field15.locate (afterSource x y output)
    (parserCfg none (some true) (alphabetBank y) [] [] []).stk 5 = _
  rw [show (5 : Stack) = CodeDAlphabetBank2Field15.locate (.inl 1) by rfl,
    bank_at]
  rfl

private theorem afterAlphabet_at14 (x : Entry) (y : Nat × ℚ)
    (output : List Bool) : afterAlphabet x y output 14 = [] := by
  change bank CodeDAlphabetBank2Field15.locate (afterSource x y output)
    (parserCfg none (some true) (alphabetBank y) [] [] []).stk 14 = []
  rw [show (14 : Stack) = CodeDAlphabetBank2Field15.locate (.inr 1) by rfl,
    bank_at]
  rfl

private theorem afterAlphabet_at11 (x : Entry) (y : Nat × ℚ)
    (output : List Bool) : afterAlphabet x y output 11 = [] := by
  change bank CodeDAlphabetBank2Field15.locate (afterSource x y output)
    (parserCfg none (some true) (alphabetBank y) [] [] []).stk 11 = []
  rw [show (11 : Stack) = CodeDAlphabetBank2Field15.locate (.inr 2) by rfl,
    bank_at]
  rfl

private theorem afterAlphabet_other (x : Entry) (y : Nat × ℚ)
    (output : List Bool) (j : Stack)
    (hj : j ≠ 0 ∧ j ≠ 5 ∧ j ≠ 6 ∧ j ≠ 14 ∧ j ≠ 11) :
    afterAlphabet x y output j = afterSource x y output j := by
  change bank CodeDAlphabetBank2Field15.locate (afterSource x y output)
    (parserCfg none (some true) (alphabetBank y) [] [] []).stk j = _
  apply bank_outside
  rintro ⟨k, hk⟩
  cases k with
  | inl k => fin_cases k <;> simp_all [CodeDAlphabetBank2Field15.locate]
  | inr k => fin_cases k <;> simp_all [CodeDAlphabetBank2Field15.locate]

private theorem pair_start (x : Entry) (y : Nat × ℚ)
    (output : List Bool) :
    (CodeDPairWeights15.frame (afterAlphabet x y output)
      (BitMachineBankSerialize.cfg (some (.emit 0)) none
        (CodeDPairWeights15.pairBank x.weight (rawOfRat y.2)) [] [] [])).stk =
      afterAlphabet x y output := by
  unfold CodeDPairWeights15.frame
  apply bank_eq_self CodeDPairWeights15.locate
  intro k
  cases k with
  | inl i =>
      fin_cases i
      · have h7 := afterAlphabet_other x y output 7 (by decide)
        simpa [CodeDPairWeights15.locate,
          BitMachineBankSerialize.cfg, BitMachineInline.cfg,
          BitMachineBankSerialize.contents, CodeDPairWeights15.pairBank]
          using (h7.trans (afterSource_at7 x y output)).symm
      · simpa [CodeDPairWeights15.locate,
          BitMachineBankSerialize.cfg, BitMachineInline.cfg,
          BitMachineBankSerialize.contents, CodeDPairWeights15.pairBank]
          using (afterAlphabet_at5 x y output).symm
  | inr i =>
      fin_cases i
      · simpa [CodeDPairWeights15.locate,
          BitMachineBankSerialize.cfg, BitMachineInline.cfg,
          BitMachineBankSerialize.contents]
          using afterAlphabet_at14 x y output
      · simpa [CodeDPairWeights15.locate,
          BitMachineBankSerialize.cfg, BitMachineInline.cfg,
          BitMachineBankSerialize.contents]
          using afterAlphabet_at11 x y output
      · have h4 := afterAlphabet_other x y output 4 (by decide)
        have h4' := afterSource_other x y output 4 (by decide)
        have h4'' := afterCopy_other x y output 4 (by decide)
        simpa [CodeDPairWeights15.locate,
          BitMachineBankSerialize.cfg, BitMachineInline.cfg,
          BitMachineBankSerialize.contents, initialBank]
          using (h4.trans (h4'.trans h4''))

theorem pair_run (x : Entry) (y : Nat × ℚ) (output : List Bool) :
    ∃ t ≤ 2*(CodeDPairProductTargetV2.pairBytes x.weight
        (rawOfRat y.2)).length+2,
      ∃ S' : BitMachineBankSerialize.Bank 2,
        CodeDPairCallbackProgram.run t
          ⟨some (.pair (.inl (.emit 0))), none,
            afterAlphabet x y output⟩ =
          ⟨some (.pair (.inr ())), none, afterPair x y output S'⟩ := by
  obtain ⟨t, ht, S', hr⟩ :=
    CodeDPairCallbackProgram.pair_phase x.weight (rawOfRat y.2)
      (afterAlphabet x y output) []
  refine ⟨t, ht, S', ?_⟩
  simp only [List.append_nil] at hr
  change CodeDPairCallbackProgram.run t
      ⟨some (.pair (.inl (.emit 0))), none,
        (CodeDPairWeights15.frame (afterAlphabet x y output)
          (BitMachineBankSerialize.cfg (some (.emit 0)) none
            (CodeDPairWeights15.pairBank x.weight (rawOfRat y.2))
            [] [] [])).stk⟩ =
      ⟨some (.pair (.inr ())), none, afterPair x y output S'⟩ at hr
  rw [pair_start] at hr
  exact hr

def clearedPairBank (x : Entry) (y : Nat × ℚ) :
    BitMachineBankSerialize.Bank 2 :=
  CodeDPairSerializerClear.cleared
    (CodeDPairWeights15.pairBank x.weight (rawOfRat y.2))

theorem pair_run_cleared (x : Entry) (y : Nat × ℚ)
    (output : List Bool) :
    ∃ t ≤ 2*(CodeDPairProductTargetV2.pairBytes x.weight
        (rawOfRat y.2)).length+2,
      CodeDPairCallbackProgram.run t
        ⟨some (.pair (.inl (.emit 0))), none,
          afterAlphabet x y output⟩ =
        ⟨some (.pair (.inr ())), none,
          afterPair x y output (clearedPairBank x y)⟩ := by
  obtain ⟨t, ht, hr⟩ :=
    CodeDPairCallbackProgram.pair_phase_cleared x.weight
      (rawOfRat y.2) (afterAlphabet x y output)
  refine ⟨t, ht, ?_⟩
  change CodeDPairCallbackProgram.run t
      ⟨some (.pair (.inl (.emit 0))), none,
        (CodeDPairWeights15.frame (afterAlphabet x y output)
          (BitMachineBankSerialize.cfg (some (.emit 0)) none
            (CodeDPairWeights15.pairBank x.weight (rawOfRat y.2))
            [] [] [])).stk⟩ =
      ⟨some (.pair (.inr ())), none,
        afterPair x y output (clearedPairBank x y)⟩ at hr
  rw [pair_start] at hr
  exact hr

private theorem afterPair_cleared_at5 (x : Entry) (y : Nat × ℚ)
    (output : List Bool) :
    afterPair x y output (clearedPairBank x y) 5 = [] := by
  change bank CodeDPairWeights15.locate (afterAlphabet x y output)
    (BitMachineBankSerialize.cfg none none (clearedPairBank x y) [] []
      (CodeDPairProductTargetV2.pairBytes x.weight (rawOfRat y.2))).stk 5 = []
  rw [show (5 : Stack) = CodeDPairWeights15.locate (.inl 1) by rfl,
    bank_at]
  exact CodeDPairSerializerClear.cleared_one
    (CodeDPairWeights15.pairBank x.weight (rawOfRat y.2))

noncomputable def afterClear (x : Entry) (y : Nat × ℚ)
    (output : List Bool) (S' : BitMachineBankSerialize.Bank 2) :
    Stack → List Bool :=
  Function.update (afterPair x y output S') 5 []

theorem clear_run (x : Entry) (y : Nat × ℚ) (output : List Bool)
    (S' : BitMachineBankSerialize.Bank 2) :
    CodeDPairCallbackProgram.run ((afterPair x y output S' 5).length + 1)
      ⟨some .clearPayload, none, afterPair x y output S'⟩ =
      ⟨some (.frame (.inl (.emit 0))), none,
        afterClear x y output S'⟩ := by
  exact CodeDPairCallbackProgram.clear_payload_run _

private theorem afterPair_at4 (x : Entry) (y : Nat × ℚ)
    (output : List Bool) (S' : BitMachineBankSerialize.Bank 2) :
    afterPair x y output S' 4 =
      CodeDPairProductTargetV2.pairBytes x.weight (rawOfRat y.2) := by
  change bank CodeDPairWeights15.locate (afterAlphabet x y output)
    (BitMachineBankSerialize.cfg none none S' [] []
      (CodeDPairProductTargetV2.pairBytes x.weight (rawOfRat y.2))).stk 4 = _
  rw [show (4 : Stack) = CodeDPairWeights15.locate (.inr 2) by rfl,
    bank_at]
  rfl

private theorem afterPair_at14 (x : Entry) (y : Nat × ℚ)
    (output : List Bool) (S' : BitMachineBankSerialize.Bank 2) :
    afterPair x y output S' 14 = [] := by
  change bank CodeDPairWeights15.locate (afterAlphabet x y output)
    (BitMachineBankSerialize.cfg none none S' [] []
      (CodeDPairProductTargetV2.pairBytes x.weight (rawOfRat y.2))).stk 14 = []
  rw [show (14 : Stack) = CodeDPairWeights15.locate (.inr 0) by rfl,
    bank_at]
  rfl

private theorem afterPair_at11 (x : Entry) (y : Nat × ℚ)
    (output : List Bool) (S' : BitMachineBankSerialize.Bank 2) :
    afterPair x y output S' 11 = [] := by
  change bank CodeDPairWeights15.locate (afterAlphabet x y output)
    (BitMachineBankSerialize.cfg none none S' [] []
      (CodeDPairProductTargetV2.pairBytes x.weight (rawOfRat y.2))).stk 11 = []
  rw [show (11 : Stack) = CodeDPairWeights15.locate (.inr 1) by rfl,
    bank_at]
  rfl

private theorem frame_start (x : Entry) (y : Nat × ℚ)
    (output : List Bool) (S' : BitMachineBankSerialize.Bank 2) :
    (CodeDFramePair15.frame (afterClear x y output S')
      (BitMachineBankSerialize.cfg (some (.emit 0)) none
        (CodeDFramePair15.oneBank
          (CodeDPairProductTargetV2.pairBytes x.weight (rawOfRat y.2)))
        [] [] [])).stk = afterClear x y output S' := by
  unfold CodeDFramePair15.frame
  apply bank_eq_self CodeDFramePair15.locate
  intro k
  cases k with
  | inl i =>
      fin_cases i
      simpa [CodeDFramePair15.locate, BitMachineBankSerialize.cfg,
        BitMachineInline.cfg, BitMachineBankSerialize.contents,
        CodeDFramePair15.oneBank, afterClear] using
        (afterPair_at4 x y output S').symm
  | inr i =>
      fin_cases i
      · simpa [CodeDFramePair15.locate, BitMachineBankSerialize.cfg,
          BitMachineInline.cfg, BitMachineBankSerialize.contents,
          afterClear] using afterPair_at14 x y output S'
      · simpa [CodeDFramePair15.locate, BitMachineBankSerialize.cfg,
          BitMachineInline.cfg, BitMachineBankSerialize.contents,
          afterClear] using afterPair_at11 x y output S'
      · simp [CodeDFramePair15.locate, BitMachineBankSerialize.cfg,
          BitMachineInline.cfg, BitMachineBankSerialize.contents,
          afterClear]

noncomputable def afterFrame (x : Entry) (y : Nat × ℚ)
    (output : List Bool) (S' : BitMachineBankSerialize.Bank 2)
    (T' : BitMachineBankSerialize.Bank 1) : Stack → List Bool :=
  (CodeDFramePair15.frame (afterClear x y output S')
    (BitMachineBankSerialize.cfg none none T' [] []
      (EncodedCommunication.field
        (CodeDPairProductTargetV2.pairBytes x.weight (rawOfRat y.2))))).stk

theorem frame_run (x : Entry) (y : Nat × ℚ) (output : List Bool)
    (S' : BitMachineBankSerialize.Bank 2) :
    ∃ t ≤ 2*(EncodedCommunication.field
        (CodeDPairProductTargetV2.pairBytes x.weight (rawOfRat y.2))).length+2,
      ∃ T' : BitMachineBankSerialize.Bank 1,
        CodeDPairCallbackProgram.run t
          ⟨some (.frame (.inl (.emit 0))), none,
            afterClear x y output S'⟩ =
          ⟨some (.frame (.inr ())), none,
            afterFrame x y output S' T'⟩ := by
  obtain ⟨t, ht, T', hr⟩ :=
    CodeDPairCallbackProgram.frame_phase
      (CodeDPairProductTargetV2.pairBytes x.weight (rawOfRat y.2))
      (afterClear x y output S') []
  refine ⟨t, ht, T', ?_⟩
  simp only [List.append_nil] at hr
  change CodeDPairCallbackProgram.run t
      ⟨some (.frame (.inl (.emit 0))), none,
        (CodeDFramePair15.frame (afterClear x y output S')
          (BitMachineBankSerialize.cfg (some (.emit 0)) none
            (CodeDFramePair15.oneBank
              (CodeDPairProductTargetV2.pairBytes x.weight (rawOfRat y.2)))
            [] [] [])).stk⟩ =
      ⟨some (.frame (.inr ())), none,
        afterFrame x y output S' T'⟩ at hr
  rw [frame_start] at hr
  exact hr

private theorem afterPair_other (x : Entry) (y : Nat × ℚ)
    (output : List Bool) (S' : BitMachineBankSerialize.Bank 2)
    (j : Stack) (hj : j ≠ 7 ∧ j ≠ 5 ∧ j ≠ 14 ∧ j ≠ 11 ∧ j ≠ 4) :
    afterPair x y output S' j = afterAlphabet x y output j := by
  change bank CodeDPairWeights15.locate (afterAlphabet x y output)
    (BitMachineBankSerialize.cfg none none S' [] []
      (CodeDPairProductTargetV2.pairBytes x.weight (rawOfRat y.2))).stk j = _
  apply bank_outside
  rintro ⟨k, hk⟩
  cases k with
  | inl k => fin_cases k <;> simp_all [CodeDPairWeights15.locate]
  | inr k => fin_cases k <;> simp_all [CodeDPairWeights15.locate]

private theorem afterFrame_other (x : Entry) (y : Nat × ℚ)
    (output : List Bool) (S' : BitMachineBankSerialize.Bank 2)
    (T' : BitMachineBankSerialize.Bank 1)
    (j : Stack) (hj : j ≠ 4 ∧ j ≠ 14 ∧ j ≠ 11 ∧ j ≠ 5) :
    afterFrame x y output S' T' j = afterClear x y output S' j := by
  change bank CodeDFramePair15.locate (afterClear x y output S')
    (BitMachineBankSerialize.cfg none none T' [] []
      (EncodedCommunication.field
        (CodeDPairProductTargetV2.pairBytes x.weight (rawOfRat y.2)))).stk j = _
  apply bank_outside
  rintro ⟨k, hk⟩
  cases k with
  | inl k => fin_cases k <;> simp_all [CodeDFramePair15.locate]
  | inr k => fin_cases k <;> simp_all [CodeDFramePair15.locate]

private theorem afterFrame_at5 (x : Entry) (y : Nat × ℚ)
    (output : List Bool) (S' : BitMachineBankSerialize.Bank 2)
    (T' : BitMachineBankSerialize.Bank 1) :
    afterFrame x y output S' T' 5 =
      EncodedCommunication.field
        (CodeDPairProductTargetV2.pairBytes x.weight (rawOfRat y.2)) := by
  change bank CodeDFramePair15.locate (afterClear x y output S')
    (BitMachineBankSerialize.cfg none none T' [] []
      (EncodedCommunication.field
        (CodeDPairProductTargetV2.pairBytes x.weight (rawOfRat y.2)))).stk 5 = _
  rw [show (5 : Stack) = CodeDFramePair15.locate (.inr 2) by rfl,
    bank_at]
  rfl

private theorem afterFrame_at11 (x : Entry) (y : Nat × ℚ)
    (output : List Bool) (S' : BitMachineBankSerialize.Bank 2)
    (T' : BitMachineBankSerialize.Bank 1) :
    afterFrame x y output S' T' 11 = [] := by
  change bank CodeDFramePair15.locate (afterClear x y output S')
    (BitMachineBankSerialize.cfg none none T' [] []
      (EncodedCommunication.field
        (CodeDPairProductTargetV2.pairBytes x.weight (rawOfRat y.2)))).stk 11 = []
  rw [show (11 : Stack) = CodeDFramePair15.locate (.inr 1) by rfl,
    bank_at]
  rfl

private theorem afterFrame_at14 (x : Entry) (y : Nat × ℚ)
    (output : List Bool) (S' : BitMachineBankSerialize.Bank 2)
    (T' : BitMachineBankSerialize.Bank 1) :
    afterFrame x y output S' T' 14 = [] := by
  change bank CodeDFramePair15.locate (afterClear x y output S')
    (BitMachineBankSerialize.cfg none none T' [] []
      (EncodedCommunication.field
        (CodeDPairProductTargetV2.pairBytes x.weight (rawOfRat y.2)))).stk 14 = []
  rw [show (14 : Stack) = CodeDFramePair15.locate (.inr 0) by rfl,
    bank_at]
  rfl

private theorem afterFrame_at9 (x : Entry) (y : Nat × ℚ)
    (output : List Bool) (S' : BitMachineBankSerialize.Bank 2)
    (T' : BitMachineBankSerialize.Bank 1) :
    afterFrame x y output S' T' 9 = output := by
  rw [afterFrame_other x y output S' T' 9 (by decide)]
  simp only [afterClear, Function.update_of_ne (by decide : (9 : Stack) ≠ 5)]
  rw [afterPair_other x y output S' 9 (by decide),
    afterAlphabet_other x y output 9 (by decide),
    afterSource_other x y output 9 (by decide)]
  exact (CodeDSourceCopy15.copied_banks (encodeEntry x)
    (initialBank x y output)).2.2.trans (by simp [initialBank])

private theorem append_start (x : Entry) (y : Nat × ℚ)
    (output : List Bool) (S' : BitMachineBankSerialize.Bank 2)
    (T' : BitMachineBankSerialize.Bank 1) :
    CodeDAppendAtEnd15.initialBank (afterFrame x y output S' T') output
      (EncodedCommunication.field
        (CodeDPairProductTargetV2.pairBytes x.weight (rawOfRat y.2))) =
      afterFrame x y output S' T' := by
  let S := afterFrame x y output S' T'
  have h9 : Function.update S 9 output = S := by
    calc
      Function.update S 9 output = Function.update S 9 (S 9) := by
        congr 1
        exact (afterFrame_at9 x y output S' T').symm
      _ = S := Function.update_eq_self 9 S
  have h5 : Function.update S 5
      (EncodedCommunication.field
        (CodeDPairProductTargetV2.pairBytes x.weight (rawOfRat y.2))) = S := by
    calc
      Function.update S 5 _ = Function.update S 5 (S 5) := by
        congr 1
        exact (afterFrame_at5 x y output S' T').symm
      _ = S := Function.update_eq_self 5 S
  unfold CodeDAppendAtEnd15.initialBank
  change Function.update (Function.update S 9 output) 5 _ = S
  rw [h9, h5]

noncomputable def afterAppend (x : Entry) (y : Nat × ℚ)
    (output : List Bool) (S' : BitMachineBankSerialize.Bank 2)
    (T' : BitMachineBankSerialize.Bank 1) : Stack → List Bool :=
  Function.update
    (Function.update
      (Function.update (afterFrame x y output S' T') 9 []) 5 [])
    9 (output ++ EncodedCommunication.field
      (CodeDPairProductTargetV2.pairBytes x.weight (rawOfRat y.2)))

theorem append_run (x : Entry) (y : Nat × ℚ) (output : List Bool)
    (S' : BitMachineBankSerialize.Bank 2)
    (T' : BitMachineBankSerialize.Bank 1) :
    CodeDPairCallbackProgram.run
        (4 * output.length +
          2 * (EncodedCommunication.field
            (CodeDPairProductTargetV2.pairBytes x.weight (rawOfRat y.2))).length + 6)
      ⟨some (.append .saveScan), none, afterFrame x y output S' T'⟩ =
      ⟨some (.append .done), none, afterAppend x y output S' T'⟩ := by
  have hr := CodeDPairCallbackProgram.append_phase
    (afterFrame x y output S' T') output
    (EncodedCommunication.field
      (CodeDPairProductTargetV2.pairBytes x.weight (rawOfRat y.2)))
    (afterFrame_at11 x y output S' T')
    (afterFrame_at14 x y output S' T')
  change CodeDPairCallbackProgram.run _
      ⟨some (.append .saveScan), none,
        CodeDAppendAtEnd15.initialBank (afterFrame x y output S' T') output
          (EncodedCommunication.field
            (CodeDPairProductTargetV2.pairBytes x.weight (rawOfRat y.2)))⟩ =
      ⟨some (.append .done), none,
        Function.update
          (Function.update
            (Function.update
              (CodeDAppendAtEnd15.initialBank
                (afterFrame x y output S' T') output
                (EncodedCommunication.field
                  (CodeDPairProductTargetV2.pairBytes x.weight
                    (rawOfRat y.2)))) 9 []) 5 [])
          9 (output ++ EncodedCommunication.field
            (CodeDPairProductTargetV2.pairBytes x.weight (rawOfRat y.2)))⟩ at hr
  rw [append_start] at hr
  exact hr

private theorem chain {c d e : Config} {a b : Nat}
    (h₁ : CodeDPairCallbackProgram.run a c = d)
    (h₂ : CodeDPairCallbackProgram.run b d = e) :
    CodeDPairCallbackProgram.run (a+b) c = e :=
  (CodeDPairCallbackProgram.run_add h₁ b).trans h₂

private theorem one {c d : Config}
    (h : advance CodeDPairCallbackProgram.program c = d) :
    CodeDPairCallbackProgram.run 1 c = d := by
  simpa [CodeDPairCallbackProgram.run, Function.iterate_one] using h

noncomputable def budget (x : Entry) (y : Nat × ℚ) (output : List Bool)
    (S' : BitMachineBankSerialize.Bank 2) : Nat :=
  (2*(encodeEntry x).length+2) + 1 +
  5*((encodeEntry x).length+1) + 1 +
  5*((CurrentAdditive.CodeDTargetV2.alphabetEntry y).length+1) + 1 +
  (2*(CodeDPairProductTargetV2.pairBytes x.weight
    (rawOfRat y.2)).length+2) + 1 +
  ((afterPair x y output S' 5).length+1) +
  (2*(EncodedCommunication.field
    (CodeDPairProductTargetV2.pairBytes x.weight
      (rawOfRat y.2))).length+2) + 1 +
  (4*output.length + 2*(EncodedCommunication.field
    (CodeDPairProductTargetV2.pairBytes x.weight
      (rawOfRat y.2))).length+6) + 1

theorem one_pair_run (x : Entry) (y : Nat × ℚ)
    (output : List Bool) :
    ∃ S' : BitMachineBankSerialize.Bank 2,
      S' = clearedPairBank x y ∧
        ∃ T' : BitMachineBankSerialize.Bank 1,
          ∃ t ≤ budget x y output S',
            CodeDPairCallbackProgram.run t (initial x y output) =
              ⟨none, none, afterAppend x y output S' T'⟩ := by
  obtain ⟨a, ha, hcopy⟩ := copy_run x y output
  obtain ⟨b, hb, hsource⟩ := source_run x y output
  obtain ⟨c, hc, halpha⟩ := alphabet_run x y output
  let S' := clearedPairBank x y
  obtain ⟨d, hd, hpair⟩ := pair_run_cleared x y output
  obtain ⟨e, he, T', hframe⟩ := frame_run x y output S'
  have h₁ := chain hcopy
    (one (CodeDPairCallbackProgram.step_copy_done
      (afterCopy x y output)))
  have h₂ := chain h₁ hsource
  have h₃ := chain h₂
    (one (CodeDPairCallbackProgram.step_source_done
      (afterSource x y output)))
  have h₄ := chain h₃ halpha
  have h₅ := chain h₄
    (one (CodeDPairCallbackProgram.step_alphabet_done
      (afterAlphabet x y output)))
  have h₆ := chain h₅ hpair
  have h₇ := chain h₆
    (one (CodeDPairCallbackProgram.step_pair_done
      (afterPair x y output S')))
  have h₈ := chain h₇ (clear_run x y output S')
  have h₉ := chain h₈ hframe
  have h₁₀ := chain h₉
    (one (CodeDPairCallbackProgram.step_frame_done
      (afterFrame x y output S' T')))
  have h₁₁ := chain h₁₀ (append_run x y output S' T')
  have h₁₂ := chain h₁₁
    (one (CodeDPairCallbackProgram.step_append_done
      (afterAppend x y output S' T')))
  let t := a + 1 + b + 1 + c + 1 + d + 1 +
    ((afterPair x y output S' 5).length + 1) + e + 1 +
    (4 * output.length +
      2 * (EncodedCommunication.field
        (CodeDPairProductTargetV2.pairBytes x.weight
          (rawOfRat y.2))).length + 6) + 1
  refine ⟨S', rfl, T', t, ?_, ?_⟩
  · unfold budget
    dsimp [t]
    omega
  · exact h₁₂

def fixedBudget (x : Entry) (y : Nat × ℚ)
    (output : List Bool) : Nat :=
  (2*(encodeEntry x).length+2) + 1 +
  5*((encodeEntry x).length+1) + 1 +
  5*((CurrentAdditive.CodeDTargetV2.alphabetEntry y).length+1) + 1 +
  (2*(CodeDPairProductTargetV2.pairBytes x.weight
    (rawOfRat y.2)).length+2) + 1 +
  1 +
  (2*(EncodedCommunication.field
    (CodeDPairProductTargetV2.pairBytes x.weight
      (rawOfRat y.2))).length+2) + 1 +
  (4*output.length + 2*(EncodedCommunication.field
    (CodeDPairProductTargetV2.pairBytes x.weight
      (rawOfRat y.2))).length+6) + 1

theorem budget_cleared (x : Entry) (y : Nat × ℚ)
    (output : List Bool) :
    budget x y output (clearedPairBank x y) =
      fixedBudget x y output := by
  simp only [budget, fixedBudget, afterPair_cleared_at5, List.length_nil,
    Nat.zero_add]

theorem one_pair_run_fixed (x : Entry) (y : Nat × ℚ)
    (output : List Bool) :
    ∃ T' : BitMachineBankSerialize.Bank 1,
      ∃ t ≤ fixedBudget x y output,
        CodeDPairCallbackProgram.run t (initial x y output) =
          ⟨none, none,
            afterAppend x y output (clearedPairBank x y) T'⟩ := by
  obtain ⟨S', rfl, T', t, ht, hr⟩ := one_pair_run x y output
  exact ⟨T', t, (budget_cleared x y output) ▸ ht, hr⟩

theorem afterAppend_at9 (x : Entry) (y : Nat × ℚ)
    (output : List Bool) (S' : BitMachineBankSerialize.Bank 2)
    (T' : BitMachineBankSerialize.Bank 1) :
    afterAppend x y output S' T' 9 =
      output ++ EncodedCommunication.field
        (CodeDPairProductTargetV2.pairBytes x.weight (rawOfRat y.2)) := by
  simp [afterAppend]

theorem afterAppend_at12 (x : Entry) (y : Nat × ℚ)
    (output : List Bool) (S' : BitMachineBankSerialize.Bank 2)
    (T' : BitMachineBankSerialize.Bank 1) :
    afterAppend x y output S' T' 12 = encodeEntry x := by
  simp only [afterAppend, Function.update_of_ne (by decide : (12 : Stack) ≠ 9),
    Function.update_of_ne (by decide : (12 : Stack) ≠ 5)]
  rw [afterFrame_other x y output S' T' 12 (by decide)]
  simp only [afterClear, Function.update_of_ne (by decide : (12 : Stack) ≠ 5)]
  rw [afterPair_other x y output S' 12 (by decide),
    afterAlphabet_other x y output 12 (by decide),
    afterSource_other x y output 12 (by decide)]
  exact (CodeDSourceCopy15.copied_banks (encodeEntry x)
    (initialBank x y output)).1

theorem one_pair_output (x : Entry) (y : Nat × ℚ)
    (output : List Bool) :
    ∃ t ≤ fixedBudget x y output,
      ∃ S : Stack → List Bool,
        CodeDPairCallbackProgram.run t (initial x y output) =
          ⟨none, none, S⟩ ∧
        S 9 = output ++ EncodedCommunication.field
          (CodeDPairProductTargetV2.pairBytes x.weight (rawOfRat y.2)) ∧
        S 12 = encodeEntry x := by
  obtain ⟨T', t, ht, hr⟩ := one_pair_run_fixed x y output
  refine ⟨t, ht, _, hr, ?_, ?_⟩
  · exact afterAppend_at9 x y output (clearedPairBank x y) T'
  · exact afterAppend_at12 x y output (clearedPairBank x y) T'

#print axioms one_pair_run

#print axioms one_pair_run_fixed

#print axioms one_pair_output

#print axioms copy_run

end CurrentAdditive.CodeDPairCallbackRun
