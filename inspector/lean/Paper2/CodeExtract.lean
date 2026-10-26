import Paper2.CodeScanner
import EthInapproximability.CurrentPaper.BitMachineCopy
import EthInapproximability.CurrentPaper.BitMachineRawSequence
import EthInapproximability.CurrentPaper.BitMachineStackRun

/-! A physical, source-preserving one-code boundary phase. The extracted
prefix is not yet separated from the preserved source; see TASK.md. -/

namespace Paper2.CodeExtract

open Turing
open EthInapproximability.CurrentPaper
open BitMachineEncoding BitMachineStackEmbedding
open Paper2.GeneratorCode Paper2.GeneratorSerialization

abbrev Stack := CodeScanner.Stack ⊕ Fin 2

def copyEmbedding : Fin 3 ↪ Stack where
  toFun
    | 0 => .inr 0
    | 1 => .inl (.inl 0)
    | 2 => .inr 1
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

def scanEmbedding : CodeScanner.Stack ↪ Stack := ⟨Sum.inl, by intro i j h; exact Sum.inl.inj h⟩

def contents (source scanned scratch pending : List Bool) : Stack → List Bool
  | .inl (.inl 0) => scanned
  | .inl (.inl _) => []
  | .inl (.inr _) => pending
  | .inr 0 => source
  | .inr 1 => scratch

def copyProgram (l : BitMachineCopy.Label) :=
  stackStmt copyEmbedding (BitMachineCopy.program l)

def scanProgram (l : CodeScanner.Label) :=
  stackStmt scanEmbedding (CodeScanner.program l)

def boundaryProgram := BitMachineRawSequence.program copyProgram scanProgram
  (.inr .check) (none : Option Bool) (((none, none), none) : CodeScanner.Control)

abbrev Config := TM2.Cfg (fun _ : Stack => Bool)
  (BitMachineRawSequence.Label BitMachineCopy.Label CodeScanner.Label)
  (Option Bool × CodeScanner.Control)

def initial (input : List Bool) : Config :=
  ⟨some (BitMachineRawSequence.leftLabel .scan),
    (none, ((none, none), none)), contents input [] [] [true]⟩

def boundary (input rest : List Bool) : Config :=
  ⟨none, (none, ((none, none), none)), contents input rest [] []⟩

def fbank (source scanned work rev : List Bool) : Stack → List Bool
  | .inl (.inl 0) => scanned
  | .inl (.inl 1) => work
  | .inl (.inl _) => []
  | .inl (.inr _) => []
  | .inr 0 => source
  | .inr 1 => rev

private theorem fbank_start (source scanned rev : List Bool) :
    fbank source scanned [] rev = contents source scanned rev [] := by
  funext k; rcases k with k | k
  · rcases k with k | k <;> fin_cases k <;> rfl
  · fin_cases k <;> rfl

inductive FinishLabel where
  | reverseFull | cancelSuffix | reverseCode | restoreSuffix
  deriving DecidableEq, Fintype

def finishProgram : FinishLabel →
    TM2.Stmt (fun _ : Stack => Bool) FinishLabel (Option Bool)
  | .reverseFull =>
      .pop (.inr 0) (fun _ b => b)
        (.branch Option.isSome
          (.push (.inr 1) (fun b => b.getD false) (.goto (fun _ => .reverseFull)))
          (.goto (fun _ => .cancelSuffix)))
  | .cancelSuffix =>
      .pop (.inl (.inl 0)) (fun _ b => b)
        (.branch Option.isSome
          (.push (.inl (.inl 1)) (fun b => b.getD false)
            (.pop (.inr 1) (fun _ b => b) (.goto (fun _ => .cancelSuffix))))
          (.goto (fun _ => .reverseCode)))
  | .reverseCode =>
      .pop (.inr 1) (fun _ b => b)
        (.branch Option.isSome
          (.push (.inr 0) (fun b => b.getD false) (.goto (fun _ => .reverseCode)))
          (.goto (fun _ => .restoreSuffix)))
  | .restoreSuffix =>
      .pop (.inl (.inl 1)) (fun _ b => b)
        (.branch Option.isSome
          (.push (.inl (.inl 0)) (fun b => b.getD false) (.goto (fun _ => .restoreSuffix)))
          (.load (fun _ => none) .halt))

def finishCfg (l : Option FinishLabel) (v : Option Bool)
    (source scanned work rev : List Bool) :
    TM2.Cfg (fun _ : Stack => Bool) FinishLabel (Option Bool) :=
  ⟨l, v, fbank source scanned work rev⟩

theorem reverseFull_cons (v : Option Bool) (b : Bool)
    (source scanned work rev : List Bool) :
    advance finishProgram (finishCfg (some .reverseFull) v (b :: source) scanned work rev) =
      finishCfg (some .reverseFull) (some b) source scanned work (b :: rev) := by
  simp [advance, TM2.step, TM2.stepAux, finishProgram, finishCfg, fbank]
  funext k; rcases k with k | k
  · rcases k with k | k <;> fin_cases k <;> rfl
  · fin_cases k <;> rfl

theorem reverseFull_nil (v : Option Bool) (scanned work rev : List Bool) :
    advance finishProgram (finishCfg (some .reverseFull) v [] scanned work rev) =
      finishCfg (some .cancelSuffix) none [] scanned work rev := by
  simp [advance, TM2.step, TM2.stepAux, finishProgram, finishCfg, fbank]

theorem cancelSuffix_cons (v : Option Bool) (b : Bool)
    (x : Bool) (source scanned work rev : List Bool) :
    advance finishProgram
        (finishCfg (some .cancelSuffix) v source (b :: scanned) work (x :: rev)) =
      finishCfg (some .cancelSuffix) (some x) source scanned (b :: work) rev := by
  simp [advance, TM2.step, TM2.stepAux, finishProgram, finishCfg, fbank]
  funext k; rcases k with k | k
  · rcases k with k | k <;> fin_cases k <;> rfl
  · fin_cases k <;> rfl

theorem cancelSuffix_nil (v : Option Bool) (source work rev : List Bool) :
    advance finishProgram (finishCfg (some .cancelSuffix) v source [] work rev) =
      finishCfg (some .reverseCode) none source [] work rev := by
  simp [advance, TM2.step, TM2.stepAux, finishProgram, finishCfg, fbank]

theorem reverseCode_cons (v : Option Bool) (b : Bool)
    (source scanned work rev : List Bool) :
    advance finishProgram (finishCfg (some .reverseCode) v source scanned work (b :: rev)) =
      finishCfg (some .reverseCode) (some b) (b :: source) scanned work rev := by
  simp [advance, TM2.step, TM2.stepAux, finishProgram, finishCfg, fbank]
  funext k; rcases k with k | k
  · rcases k with k | k <;> fin_cases k <;> rfl
  · fin_cases k <;> rfl

theorem reverseCode_nil (v : Option Bool) (source scanned work : List Bool) :
    advance finishProgram (finishCfg (some .reverseCode) v source scanned work []) =
      finishCfg (some .restoreSuffix) none source scanned work [] := by
  simp [advance, TM2.step, TM2.stepAux, finishProgram, finishCfg, fbank]

theorem restoreSuffix_cons (v : Option Bool) (b : Bool)
    (source scanned work rev : List Bool) :
    advance finishProgram
        (finishCfg (some .restoreSuffix) v source scanned (b :: work) rev) =
      finishCfg (some .restoreSuffix) (some b) source (b :: scanned) work rev := by
  simp [advance, TM2.step, TM2.stepAux, finishProgram, finishCfg, fbank]
  funext k; rcases k with k | k
  · rcases k with k | k <;> fin_cases k <;> rfl
  · fin_cases k <;> rfl

theorem restoreSuffix_nil (v : Option Bool) (source scanned rev : List Bool) :
    advance finishProgram (finishCfg (some .restoreSuffix) v source scanned [] rev) =
      finishCfg none none source scanned [] rev := by
  simp [advance, TM2.step, TM2.stepAux, finishProgram, finishCfg, fbank]

theorem reverseFull_run (v : Option Bool)
    (source scanned work rev : List Bool) :
    ((advance finishProgram)^[source.length + 1])
      (finishCfg (some .reverseFull) v source scanned work rev) =
      finishCfg (some .cancelSuffix) none [] scanned work (source.reverse ++ rev) := by
  induction source generalizing v rev with
  | nil => simpa using reverseFull_nil v scanned work rev
  | cons b source ih =>
      rw [List.length_cons, Function.iterate_succ_apply, reverseFull_cons, ih]
      simp [List.reverse_cons, List.append_assoc]

theorem reverseCode_run (v : Option Bool)
    (source scanned work rev : List Bool) :
    ((advance finishProgram)^[rev.length + 1])
      (finishCfg (some .reverseCode) v source scanned work rev) =
      finishCfg (some .restoreSuffix) none (rev.reverse ++ source) scanned work [] := by
  induction rev generalizing v source with
  | nil => simpa using reverseCode_nil v source scanned work
  | cons b rev ih =>
      rw [List.length_cons, Function.iterate_succ_apply, reverseCode_cons, ih]
      simp [List.reverse_cons, List.append_assoc]

theorem restoreSuffix_run (v : Option Bool)
    (source scanned work rev : List Bool) :
    ((advance finishProgram)^[work.length + 1])
      (finishCfg (some .restoreSuffix) v source scanned work rev) =
      finishCfg none none source (work.reverse ++ scanned) [] rev := by
  induction work generalizing v scanned with
  | nil => simpa using restoreSuffix_nil v source scanned rev
  | cons b work ih =>
      rw [List.length_cons, Function.iterate_succ_apply, restoreSuffix_cons, ih]
      simp [List.reverse_cons, List.append_assoc]

theorem cancelSuffix_run (v : Option Bool)
    (suffix revPrefix codeRev work source : List Bool)
    (hlen : revPrefix.length = suffix.length) :
    ((advance finishProgram)^[suffix.length + 1])
      (finishCfg (some .cancelSuffix) v source suffix work
        (revPrefix ++ codeRev)) =
      finishCfg (some .reverseCode) none source [] (suffix.reverse ++ work) codeRev := by
  induction suffix generalizing v work revPrefix with
  | nil =>
      have : revPrefix = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst revPrefix
      simpa using cancelSuffix_nil v source work codeRev
  | cons b suffix ih =>
      cases revPrefix with
      | nil => simp at hlen
      | cons x revPrefix =>
          have htail : revPrefix.length = suffix.length := by simpa using hlen
          rw [List.length_cons, Function.iterate_succ_apply]
          simp only [List.cons_append]
          rw [cancelSuffix_cons v b x source suffix work (revPrefix ++ codeRev)]
          rw [ih (some x) revPrefix (b :: work) htail]
          simp [List.reverse_cons, List.append_assoc]

/-- Physical extraction after a completed boundary scan. All four loops
operate on fixed Boolean stacks, not on a decoded Code object. -/
theorem finish_exact (c : Code) (rest : List Bool) :
    ((advance finishProgram)^[(rest.length + 1) +
      ((encodeCode c).length + 1) + (rest.length + 1) +
      ((encodeCode c ++ rest).length + 1)])
      (finishCfg (some .reverseFull) none (encodeCode c ++ rest) rest [] []) =
      finishCfg none none (encodeCode c) rest [] [] := by
  let code := encodeCode c
  have hrev : (code ++ rest).reverse = rest.reverse ++ code.reverse := by
    simp [List.reverse_append]
  have hcancel := cancelSuffix_run none rest rest.reverse code.reverse [] []
    (by simp)
  have hrCode := reverseCode_run none ([] : List Bool) [] rest.reverse code.reverse
  have hrRest := restoreSuffix_run none code [] rest.reverse []
  simp only [List.append_nil] at hcancel
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at hrCode hrRest
  change ((advance finishProgram)^[(rest.length + 1) + (code.length + 1) +
    (rest.length + 1) + ((code ++ rest).length + 1)]) _ = _
  rw [Function.iterate_add_apply, reverseFull_run, hrev, List.append_nil,
    Function.iterate_add_apply, hcancel,
    Function.iterate_add_apply, hrCode, hrRest]

private theorem copy_bank (word source target scratch : List Bool) :
    bank copyEmbedding (contents word word [] [true])
      (BitMachineCopy.stackContents source target scratch) =
      contents source target scratch [true] := by
  funext k
  rcases k with k | k
  · rcases k with k | k
    · fin_cases k
      · change bank copyEmbedding _ _ (copyEmbedding 1) = _
        rw [bank_at]; rfl
      all_goals
        rw [bank_outside]
        · rfl
        · intro ⟨j, hj⟩; fin_cases j <;> simp [copyEmbedding] at hj
    · fin_cases k
      rw [bank_outside]
      · rfl
      · intro ⟨j, hj⟩; fin_cases j <;> simp [copyEmbedding] at hj
  · fin_cases k
    · change bank copyEmbedding _ _ (copyEmbedding 0) = _
      rw [bank_at]; rfl
    · change bank copyEmbedding _ _ (copyEmbedding 2) = _
      rw [bank_at]; rfl

private theorem scan_bank (source foreignInput input pending : List Bool) :
    bank scanEmbedding (contents source foreignInput [] [true])
      (CodeScanner.blank input pending) =
      contents source input [] pending := by
  funext k
  rcases k with k | k
  · change bank scanEmbedding _ _ (scanEmbedding k) = _
    rw [bank_at]
    rcases k with k | k
    · fin_cases k <;> rfl
    · fin_cases k; rfl
  · rw [bank_outside]
    · fin_cases k <;> rfl
    · intro ⟨j, hj⟩; cases hj

/-- A fixed finite-control preparatory phase copies the entire physical input,
then runs the frozen code scanner on that copy. The original input and the
arbitrary suffix are both physical output stacks. This does not yet split the
code prefix from the original input. -/
theorem source_and_boundary (c : Code) (rest : List Bool) :
    ∃ t ≤ 2 * (encodeCode c ++ rest).length + 2 +
        (5 * codeSize c + 1) + 1,
      ((advance boundaryProgram)^[t]) (initial (encodeCode c ++ rest)) =
        boundary (encodeCode c ++ rest) rest := by
  let input := encodeCode c ++ rest
  have hcopy := BitMachineStackRun.run copyEmbedding
    (contents input input [] [true]) BitMachineCopy.program
    (BitMachineCopy.cfg (some .scan) none input [] []) (2 * input.length + 2)
  have hc := BitMachineCopy.run_correct none input []
  simp only [BitMachineCopy.run] at hc
  rw [hc] at hcopy
  simp only [stackCfg, BitMachineCopy.cfg, List.append_nil, copy_bank] at hcopy
  obtain ⟨ts, hts, hs⟩ := CodeScanner.skip_code c rest
  have hscan := BitMachineStackRun.run scanEmbedding
    (contents input input [] [true]) CodeScanner.program
    (CodeScanner.ready input [true]) ts
  rw [hs] at hscan
  simp only [stackCfg, CodeScanner.ready, scan_bank] at hscan
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    copyProgram scanProgram .scan (.inr .check)
    (none : Option Bool) none
    (((none, none), none) : CodeScanner.Control) (((none, none), none) : CodeScanner.Control)
    (contents input [] [] [true]) (contents input input [] [true])
    (contents input rest [] [])
    (2 * input.length + 2) ts hcopy hscan
  exact ⟨t, by simpa only [input] using (show t ≤ 2 * input.length + 2 +
    (5 * codeSize c + 1) + 1 by omega), hr⟩

#print axioms source_and_boundary

def fullProgram := BitMachineRawSequence.program boundaryProgram finishProgram
  .reverseFull (none, (((none, none), none) : CodeScanner.Control))
  (none : Option Bool)

abbrev FullConfig := TM2.Cfg (fun _ : Stack => Bool)
  (BitMachineRawSequence.Label
    (BitMachineRawSequence.Label BitMachineCopy.Label CodeScanner.Label) FinishLabel)
  ((Option Bool × CodeScanner.Control) × Option Bool)

def fullInitial (input : List Bool) : FullConfig :=
  ⟨some (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
    ((none, ((none, none), none)), none), contents input [] [] [true]⟩

def fullOutput (code rest : List Bool) : FullConfig :=
  ⟨none, ((none, ((none, none), none)), none), fbank code rest [] []⟩

/-- A single finite-control TM2 program physically separates exactly the
first serialized code from an arbitrary following suffix. It never receives
the `Code`, either output list, or their lengths as machine input. -/
theorem extract_one_code (c : Code) (rest : List Bool) :
    ∃ t ≤ 12 * (encodeCode c ++ rest).length + 12,
      ((advance fullProgram)^[t]) (fullInitial (encodeCode c ++ rest)) =
        fullOutput (encodeCode c) rest := by
  let input := encodeCode c ++ rest
  obtain ⟨tb, htb, hb⟩ := source_and_boundary c rest
  let tf := (rest.length + 1) + ((encodeCode c).length + 1) +
    (rest.length + 1) + (input.length + 1)
  have hf := finish_exact c rest
  have hf' : ((advance finishProgram)^[tf])
      (⟨some FinishLabel.reverseFull, none, contents input rest [] []⟩ :
        TM2.Cfg (fun _ : Stack => Bool) FinishLabel (Option Bool)) =
      finishCfg none none (encodeCode c) rest [] [] := by
    simpa only [tf, input, finishCfg, fbank_start] using hf
  have hb' : ((advance boundaryProgram)^[tb])
      (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
        (none, ((none, none), none)), contents input [] [] [true]⟩ : Config) =
      ⟨none, (none, ((none, none), none)), contents input rest [] []⟩ := by
    simpa only [initial, boundary, input] using hb
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    boundaryProgram finishProgram
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) .reverseFull
    (none, (((none, none), none) : CodeScanner.Control))
    (none, (((none, none), none) : CodeScanner.Control))
    (none : Option Bool) none
    (contents input [] [] [true]) (contents input rest [] [])
    (fbank (encodeCode c) rest [] []) tb tf hb' hf'
  refine ⟨t, ?_, ?_⟩
  · have hcode : codeSize c = (encodeCode c).length :=
      (encodeCode_length c).symm
    have hin : input.length = (encodeCode c).length + rest.length := by
      simp [input]
    dsimp [tf] at ht
    change tb ≤ 2 * input.length + 2 + (5 * codeSize c + 1) + 1 at htb
    change t ≤ 12 * input.length + 12
    omega
  · exact hr

#print axioms finish_exact
#print axioms extract_one_code

end Paper2.CodeExtract
