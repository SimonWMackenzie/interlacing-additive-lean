import Paper2.CodeExtract
import Paper2.UnaryChoice
import EthInapproximability.CurrentPaper.BitMachineInline
import EthInapproximability.CurrentPaper.BitMachineStackRun

/-! Fixed-control serialized-child transport after a physical unary choice. -/

namespace Paper2.ChildSelect

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open BitMachineEncoding BitMachineStackEmbedding
open Paper2.GeneratorCode Paper2.GeneratorSerialization

abbrev Stack := CodeExtract.Stack
abbrev ExtractLabel := BitMachineRawSequence.Label
  (BitMachineRawSequence.Label BitMachineCopy.Label CodeScanner.Label)
  CodeExtract.FinishLabel
abbrev ExtractControl := (Option Bool × CodeScanner.Control) × Option Bool
abbrev Control := (CodeScanner.Control × ExtractControl) × UnaryChoice.Choice

def scanZero : CodeScanner.Control := ((none, none), none)
def extractZero : ExtractControl := ((none, scanZero), none)

inductive Label where
  | dispatch
  | startBefore1 (c : UnaryChoice.Choice)
  | before1 (c : UnaryChoice.Choice) (l : CodeScanner.Label)
  | afterBefore1 (c : UnaryChoice.Choice)
  | startBefore2 (c : UnaryChoice.Choice)
  | before2 (c : UnaryChoice.Choice) (l : CodeScanner.Label)
  | startExtract (c : UnaryChoice.Choice)
  | extract (c : UnaryChoice.Choice) (l : ExtractLabel)
  | afterExtract (c : UnaryChoice.Choice)
  | startAfter1 (c : UnaryChoice.Choice)
  | after1 (c : UnaryChoice.Choice) (l : CodeScanner.Label)
  | afterAfter1 (c : UnaryChoice.Choice)
  | startAfter2 (c : UnaryChoice.Choice)
  | after2 (c : UnaryChoice.Choice) (l : CodeScanner.Label)
  | done
  deriving DecidableEq, Fintype

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def pending : Stack := .inl CodeScanner.pending
def source : Stack := .inr 0

def beforeEmbedding : CodeScanner.Stack ↪ Stack where
  toFun
    | .inl 0 => source
    | .inl k => .inl (.inl k)
    | .inr k => .inl (.inr k)
  inj' := by
    intro i j h
    rcases i with i | i <;> rcases j with j | j
    · fin_cases i <;> fin_cases j <;> simp_all [source]
    · fin_cases i <;> fin_cases j <;> simp_all [source]
    · fin_cases i <;> fin_cases j <;> simp_all [source]
    · fin_cases i <;> fin_cases j <;> simp_all [source]

def scanBeforeProgram (l : CodeScanner.Label) :=
  stackStmt beforeEmbedding (CodeScanner.program l)

def scanAfterProgram := CodeExtract.scanProgram

def scanEmbed (c : UnaryChoice.Choice) (v : CodeScanner.Control) : Control :=
  ((v, extractZero), c)
def scanRead (v : Control) : CodeScanner.Control := v.1.1
def extractEmbed (c : UnaryChoice.Choice) (v : ExtractControl) : Control :=
  ((scanZero, v), c)
def extractRead (v : Control) : ExtractControl := v.1.2

def startScan (c : UnaryChoice.Choice) (next : Label) :
    TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  .load (fun _ => scanEmbed c scanZero)
    (.push pending (fun _ => true) (.goto (fun _ => next)))

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .dispatch =>
      .branch (fun v => decide (v.2 = .first))
        (.goto (fun v => .startExtract v.2))
        (.goto (fun v => .startBefore1 v.2))
  | .startBefore1 c => startScan c (.before1 c (.inr .check))
  | .before1 c l =>
      BitMachineInline.stmt (.before1 c) (scanEmbed c) scanRead
        (some (.afterBefore1 c)) (scanBeforeProgram l)
  | .afterBefore1 c =>
      if c = .third then .goto (fun _ => .startBefore2 c)
      else .goto (fun _ => .startExtract c)
  | .startBefore2 c => startScan c (.before2 c (.inr .check))
  | .before2 c l =>
      BitMachineInline.stmt (.before2 c) (scanEmbed c) scanRead
        (some (.startExtract c)) (scanBeforeProgram l)
  | .startExtract c =>
      .load (fun _ => extractEmbed c extractZero)
        (.push pending (fun _ => true)
          (.goto (fun _ => .extract c
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))))
  | .extract c l =>
      BitMachineInline.stmt (.extract c) (extractEmbed c) extractRead
        (some (.afterExtract c)) (CodeExtract.fullProgram l)
  | .afterExtract c =>
      if c = .third then .goto (fun _ => .done)
      else .goto (fun _ => .startAfter1 c)
  | .startAfter1 c => startScan c (.after1 c (.inr .check))
  | .after1 c l =>
      BitMachineInline.stmt (.after1 c) (scanEmbed c) scanRead
        (some (.afterAfter1 c)) (scanAfterProgram l)
  | .afterAfter1 c =>
      if c = .first then .goto (fun _ => .startAfter2 c)
      else .goto (fun _ => .done)
  | .startAfter2 c => startScan c (.after2 c (.inr .check))
  | .after2 c l =>
      BitMachineInline.stmt (.after2 c) (scanEmbed c) scanRead
        (some .done) (scanAfterProgram l)
  | .done => .halt

private theorem before_bank (foreignInput input pending : List Bool) :
    bank beforeEmbedding (CodeExtract.contents foreignInput [] [] [true])
      (CodeScanner.blank input pending) =
      CodeExtract.contents input [] [] pending := by
  funext k
  rcases k with k | k
  · rcases k with k | k
    · refine Fin.cases ?_ (fun j => ?_) k
      · rw [bank_outside]
        · rfl
        · intro ⟨j, hj⟩
          rcases j with j | j
          · fin_cases j <;> simp [beforeEmbedding, source] at hj
          · fin_cases j <;> simp [beforeEmbedding, source] at hj
      · change bank beforeEmbedding _ _ (beforeEmbedding (.inl j.succ)) = _
        rw [bank_at]
        fin_cases j <;> rfl
    · fin_cases k
      change bank beforeEmbedding _ _ (beforeEmbedding (.inr 0)) = _
      rw [bank_at]; rfl
  · fin_cases k
    · change bank beforeEmbedding _ _ (beforeEmbedding (.inl 0)) = _
      rw [bank_at]; rfl
    · rw [bank_outside]
      · rfl
      · intro ⟨j, hj⟩
        rcases j with j | j
        · fin_cases j <;> simp [beforeEmbedding, source] at hj
        · fin_cases j <;> simp [beforeEmbedding, source] at hj

/-- Scanner run on the source stack, leaving every non-scanner stack intact. -/
theorem skip_source (c : Code) (rest : List Bool) :
    ∃ t ≤ 5 * codeSize c + 1,
      ((advance scanBeforeProgram)^[t])
        (⟨some (.inr .check), scanZero,
          CodeExtract.contents (encodeCode c ++ rest) [] [] [true]⟩ :
          TM2.Cfg (fun _ : Stack => Bool) CodeScanner.Label CodeScanner.Control) =
        ⟨none, scanZero, CodeExtract.contents rest [] [] []⟩ := by
  obtain ⟨t, ht, hr⟩ := CodeScanner.skip_code c rest
  have hs := BitMachineStackRun.run beforeEmbedding
    (CodeExtract.contents (encodeCode c ++ rest) [] [] [true])
    CodeScanner.program (CodeScanner.ready (encodeCode c ++ rest) [true]) t
  rw [hr] at hs
  simp only [stackCfg, CodeScanner.ready, before_bank] at hs
  exact ⟨t, ht, hs⟩

private theorem after_bank (code foreignInput input pending : List Bool) :
    bank CodeExtract.scanEmbedding
      (CodeExtract.contents code foreignInput [] [true])
      (CodeScanner.blank input pending) =
      CodeExtract.contents code input [] pending := by
  funext k
  rcases k with k | k
  · change bank CodeExtract.scanEmbedding _ _ (CodeExtract.scanEmbedding k) = _
    rw [bank_at]
    rcases k with k | k
    · fin_cases k <;> rfl
    · fin_cases k; rfl
  · rw [bank_outside]
    · fin_cases k <;> rfl
    · intro ⟨j, hj⟩; cases hj

/-- Scanner run on the suffix stack, retaining the selected source/output. -/
theorem skip_suffix (selected : List Bool) (c : Code) (rest : List Bool) :
    ∃ t ≤ 5 * codeSize c + 1,
      ((advance scanAfterProgram)^[t])
        (⟨some (.inr .check), scanZero,
          CodeExtract.contents selected (encodeCode c ++ rest) [] [true]⟩ :
          TM2.Cfg (fun _ : Stack => Bool) CodeScanner.Label CodeScanner.Control) =
        ⟨none, scanZero, CodeExtract.contents selected rest [] []⟩ := by
  obtain ⟨t, ht, hr⟩ := CodeScanner.skip_code c rest
  have hs := BitMachineStackRun.run CodeExtract.scanEmbedding
    (CodeExtract.contents selected (encodeCode c ++ rest) [] [true])
    CodeScanner.program (CodeScanner.ready (encodeCode c ++ rest) [true]) t
  rw [hr] at hs
  simp only [stackCfg, CodeScanner.ready, after_bank] at hs
  exact ⟨t, ht, hs⟩

private theorem inline_scanner (choice : UnaryChoice.Choice)
    (P : CodeScanner.Label → TM2.Stmt (fun _ : Stack => Bool)
      CodeScanner.Label CodeScanner.Control)
    (entry : CodeScanner.Label → Label) (exit : Label)
    (S T : Stack → List Bool) (bound : Nat)
    (hP : ((advance P)^[bound])
      (⟨some (.inr .check), scanZero, S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) CodeScanner.Label CodeScanner.Control) =
      ⟨none, scanZero, T⟩)
    (hQ : ∀ l, program (entry l) =
      BitMachineInline.stmt entry (scanEmbed choice) scanRead (some exit) (P l)) :
    ∃ t ≤ bound,
      ((advance program)^[t])
        (⟨some (entry (.inr .check)), scanEmbed choice scanZero, S⟩ : Config) =
        ⟨some exit, scanEmbed choice scanZero, T⟩ := by
  have hhalt : (((advance P)^[bound])
      (⟨some (.inr .check), scanZero, S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) CodeScanner.Label CodeScanner.Control)).l = none := by
    rw [hP]
  obtain ⟨t, ht, hr⟩ := BitMachineInline.outputs entry
    (scanEmbed choice) scanRead (by intro v; rfl) (some exit)
    P program hQ
    (⟨some (.inr .check), scanZero, S⟩ :
      TM2.Cfg (fun _ : Stack => Bool) CodeScanner.Label CodeScanner.Control)
    bound hhalt
  rw [hP] at hr
  exact ⟨t, ht, hr⟩

/-- Inlined physical extractor, with the chosen branch kept in finite control. -/
theorem extract_stage (choice : UnaryChoice.Choice) (c : Code) (rest : List Bool) :
    ∃ t ≤ 12 * (encodeCode c ++ rest).length + 12,
      ((advance program)^[t])
        (⟨some (.extract choice
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))),
          extractEmbed choice extractZero,
          CodeExtract.contents (encodeCode c ++ rest) [] [] [true]⟩ : Config) =
        ⟨some (.afterExtract choice), extractEmbed choice extractZero,
          CodeExtract.fbank (encodeCode c) rest [] []⟩ := by
  obtain ⟨t, ht, hr⟩ := CodeExtract.extract_one_code c rest
  have hhalt : (((advance CodeExtract.fullProgram)^[t])
      (CodeExtract.fullInitial (encodeCode c ++ rest))).l = none := by
    rw [hr]
    rfl
  obtain ⟨u, hu, he⟩ := BitMachineInline.outputs (.extract choice)
    (extractEmbed choice) extractRead (by intro v; rfl)
    (some (.afterExtract choice)) CodeExtract.fullProgram program
    (by intro l; rfl) (CodeExtract.fullInitial (encodeCode c ++ rest)) t hhalt
  rw [hr] at he
  exact ⟨u, by omega, he⟩

theorem before1_stage (choice : UnaryChoice.Choice) (c : Code) (rest : List Bool) :
    ∃ t ≤ 5 * codeSize c + 1,
      ((advance program)^[t])
        (⟨some (.before1 choice (.inr .check)), scanEmbed choice scanZero,
          CodeExtract.contents (encodeCode c ++ rest) [] [] [true]⟩ : Config) =
        ⟨some (.afterBefore1 choice), scanEmbed choice scanZero,
          CodeExtract.contents rest [] [] []⟩ := by
  obtain ⟨t, ht, hr⟩ := skip_source c rest
  obtain ⟨u, hu, he⟩ := inline_scanner choice scanBeforeProgram
    (.before1 choice) (.afterBefore1 choice)
    (CodeExtract.contents (encodeCode c ++ rest) [] [] [true])
    (CodeExtract.contents rest [] [] []) t hr (by intro l; rfl)
  exact ⟨u, by omega, he⟩

theorem before2_stage (choice : UnaryChoice.Choice) (c : Code) (rest : List Bool) :
    ∃ t ≤ 5 * codeSize c + 1,
      ((advance program)^[t])
        (⟨some (.before2 choice (.inr .check)), scanEmbed choice scanZero,
          CodeExtract.contents (encodeCode c ++ rest) [] [] [true]⟩ : Config) =
        ⟨some (.startExtract choice), scanEmbed choice scanZero,
          CodeExtract.contents rest [] [] []⟩ := by
  obtain ⟨t, ht, hr⟩ := skip_source c rest
  obtain ⟨u, hu, he⟩ := inline_scanner choice scanBeforeProgram
    (.before2 choice) (.startExtract choice)
    (CodeExtract.contents (encodeCode c ++ rest) [] [] [true])
    (CodeExtract.contents rest [] [] []) t hr (by intro l; rfl)
  exact ⟨u, by omega, he⟩

theorem after1_stage (choice : UnaryChoice.Choice)
    (selected : List Bool) (c : Code) (rest : List Bool) :
    ∃ t ≤ 5 * codeSize c + 1,
      ((advance program)^[t])
        (⟨some (.after1 choice (.inr .check)), scanEmbed choice scanZero,
          CodeExtract.contents selected (encodeCode c ++ rest) [] [true]⟩ : Config) =
        ⟨some (.afterAfter1 choice), scanEmbed choice scanZero,
          CodeExtract.contents selected rest [] []⟩ := by
  obtain ⟨t, ht, hr⟩ := skip_suffix selected c rest
  obtain ⟨u, hu, he⟩ := inline_scanner choice scanAfterProgram
    (.after1 choice) (.afterAfter1 choice)
    (CodeExtract.contents selected (encodeCode c ++ rest) [] [true])
    (CodeExtract.contents selected rest [] []) t hr (by intro l; rfl)
  exact ⟨u, by omega, he⟩

theorem after2_stage (choice : UnaryChoice.Choice)
    (selected : List Bool) (c : Code) (rest : List Bool) :
    ∃ t ≤ 5 * codeSize c + 1,
      ((advance program)^[t])
        (⟨some (.after2 choice (.inr .check)), scanEmbed choice scanZero,
          CodeExtract.contents selected (encodeCode c ++ rest) [] [true]⟩ : Config) =
        ⟨some .done, scanEmbed choice scanZero,
          CodeExtract.contents selected rest [] []⟩ := by
  obtain ⟨t, ht, hr⟩ := skip_suffix selected c rest
  obtain ⟨u, hu, he⟩ := inline_scanner choice scanAfterProgram
    (.after2 choice) .done
    (CodeExtract.contents selected (encodeCode c ++ rest) [] [true])
    (CodeExtract.contents selected rest [] []) t hr (by intro l; rfl)
  exact ⟨u, by omega, he⟩

def idle (c : UnaryChoice.Choice) : Control := ((scanZero, extractZero), c)

def initial (c : UnaryChoice.Choice) (input : List Bool) : Config :=
  ⟨some .dispatch, idle c, CodeExtract.contents input [] [] []⟩

def output (c : UnaryChoice.Choice) (selected rest : List Bool) : Config :=
  ⟨none, idle c, CodeExtract.contents selected rest [] []⟩

private theorem pending_push (source scanned : List Bool) :
    Function.update (CodeExtract.contents source scanned [] []) pending [true] =
      CodeExtract.contents source scanned [] [true] := by
  funext k
  rcases k with k | k
  · rcases k with k | k
    · fin_cases k <;> simp [pending, CodeScanner.pending, CodeExtract.contents,
        Function.update]
    · fin_cases k <;> simp [pending, CodeScanner.pending, CodeExtract.contents,
        Function.update]
  · fin_cases k <;> simp [pending, CodeScanner.pending, CodeExtract.contents,
      Function.update]

private theorem fbank_output (source scanned : List Bool) :
    CodeExtract.fbank source scanned [] [] =
      CodeExtract.contents source scanned [] [] := by
  funext k
  rcases k with k | k
  · rcases k with k | k <;> fin_cases k <;> rfl
  · fin_cases k <;> rfl

theorem dispatch_step (c : UnaryChoice.Choice) (input : List Bool) :
    advance program (initial c input) =
      ⟨some (if c = .first then .startExtract c else .startBefore1 c),
        idle c, CodeExtract.contents input [] [] []⟩ := by
  cases c <;> rfl

theorem startBefore1_step (c : UnaryChoice.Choice) (input : List Bool) :
    advance program
      (⟨some (.startBefore1 c), idle c, CodeExtract.contents input [] [] []⟩ : Config) =
      ⟨some (.before1 c (.inr .check)), idle c,
        CodeExtract.contents input [] [] [true]⟩ := by
  change (⟨some (.before1 c (.inr .check)), idle c,
    Function.update (CodeExtract.contents input [] [] []) pending [true]⟩ : Config) = _
  rw [pending_push]

theorem startBefore2_step (c : UnaryChoice.Choice) (input : List Bool) :
    advance program
      (⟨some (.startBefore2 c), idle c, CodeExtract.contents input [] [] []⟩ : Config) =
      ⟨some (.before2 c (.inr .check)), idle c,
        CodeExtract.contents input [] [] [true]⟩ := by
  change (⟨some (.before2 c (.inr .check)), idle c,
    Function.update (CodeExtract.contents input [] [] []) pending [true]⟩ : Config) = _
  rw [pending_push]

theorem startExtract_step (c : UnaryChoice.Choice) (input : List Bool) :
    advance program
      (⟨some (.startExtract c), idle c, CodeExtract.contents input [] [] []⟩ : Config) =
      ⟨some (.extract c (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))),
        idle c, CodeExtract.contents input [] [] [true]⟩ := by
  change (⟨some (.extract c (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))), idle c,
    Function.update (CodeExtract.contents input [] [] []) pending [true]⟩ : Config) = _
  rw [pending_push]

theorem startAfter1_step (c : UnaryChoice.Choice)
    (selected suffix : List Bool) :
    advance program
      (⟨some (.startAfter1 c), idle c,
        CodeExtract.contents selected suffix [] []⟩ : Config) =
      ⟨some (.after1 c (.inr .check)), idle c,
        CodeExtract.contents selected suffix [] [true]⟩ := by
  change (⟨some (.after1 c (.inr .check)), idle c,
    Function.update (CodeExtract.contents selected suffix [] []) pending [true]⟩ : Config) = _
  rw [pending_push]

theorem startAfter2_step (c : UnaryChoice.Choice)
    (selected suffix : List Bool) :
    advance program
      (⟨some (.startAfter2 c), idle c,
        CodeExtract.contents selected suffix [] []⟩ : Config) =
      ⟨some (.after2 c (.inr .check)), idle c,
        CodeExtract.contents selected suffix [] [true]⟩ := by
  change (⟨some (.after2 c (.inr .check)), idle c,
    Function.update (CodeExtract.contents selected suffix [] []) pending [true]⟩ : Config) = _
  rw [pending_push]

theorem done_step (c : UnaryChoice.Choice) (selected rest : List Bool) :
    advance program
      (⟨some .done, idle c, CodeExtract.contents selected rest [] []⟩ : Config) =
      output c selected rest := rfl

theorem afterBefore1_step (c : UnaryChoice.Choice) (input : List Bool) :
    advance program
      (⟨some (.afterBefore1 c), idle c,
        CodeExtract.contents input [] [] []⟩ : Config) =
      ⟨some (if c = .third then .startBefore2 c else .startExtract c),
        idle c, CodeExtract.contents input [] [] []⟩ := by
  cases c <;> rfl

theorem afterExtract_step (c : UnaryChoice.Choice)
    (selected suffix : List Bool) :
    advance program
      (⟨some (.afterExtract c), idle c,
        CodeExtract.contents selected suffix [] []⟩ : Config) =
      ⟨some (if c = .third then .done else .startAfter1 c),
        idle c, CodeExtract.contents selected suffix [] []⟩ := by
  cases c <;> rfl

theorem afterAfter1_step (c : UnaryChoice.Choice)
    (selected suffix : List Bool) :
    advance program
      (⟨some (.afterAfter1 c), idle c,
        CodeExtract.contents selected suffix [] []⟩ : Config) =
      ⟨some (if c = .first then .startAfter2 c else .done),
        idle c, CodeExtract.contents selected suffix [] []⟩ := by
  cases c <;> rfl

private theorem chain {x y z : Config} {m n : Nat}
    (hxy : ((advance program)^[m]) x = y)
    (hyz : ((advance program)^[n]) y = z) :
    ((advance program)^[m + n]) x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, hxy, hyz]

theorem select_first (f s t : Code) (rest : List Bool) :
    ∃ n ≤ 25 * (encodeCode f ++ encodeCode s ++ encodeCode t ++ rest).length + 30,
      ((advance program)^[n])
        (initial .first (encodeCode f ++ encodeCode s ++ encodeCode t ++ rest)) =
        output .first (encodeCode f) rest := by
  let word := encodeCode f ++ encodeCode s ++ encodeCode t ++ rest
  let tail1 := encodeCode s ++ encodeCode t ++ rest
  let tail2 := encodeCode t ++ rest
  obtain ⟨te, hte, he⟩ := extract_stage .first f tail1
  obtain ⟨ts, hts, hs⟩ := after1_stage .first (encodeCode f) s tail2
  obtain ⟨tt, htt, ht⟩ := after2_stage .first (encodeCode f) t rest
  have h0 : ((advance program)^[1]) (initial .first word) =
      ⟨some (.startExtract .first), idle .first,
        CodeExtract.contents word [] [] []⟩ := by
    simpa using dispatch_step .first word
  have h1 : ((advance program)^[1])
      (⟨some (.startExtract .first), idle .first,
        CodeExtract.contents word [] [] []⟩ : Config) =
      ⟨some (.extract .first (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))),
        idle .first, CodeExtract.contents word [] [] [true]⟩ := by
    simpa using startExtract_step .first word
  have h2 : ((advance program)^[te])
      (⟨some (.extract .first (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))),
        idle .first, CodeExtract.contents word [] [] [true]⟩ : Config) =
      ⟨some (.afterExtract .first), idle .first,
        CodeExtract.contents (encodeCode f) tail1 [] []⟩ := by
    simpa only [word, tail1, idle, extractEmbed, fbank_output,
      List.append_assoc] using he
  have h3 : ((advance program)^[1])
      (⟨some (.afterExtract .first), idle .first,
        CodeExtract.contents (encodeCode f) tail1 [] []⟩ : Config) =
      ⟨some (.startAfter1 .first), idle .first,
        CodeExtract.contents (encodeCode f) tail1 [] []⟩ := by
    simpa using afterExtract_step .first (encodeCode f) tail1
  have h4 : ((advance program)^[1])
      (⟨some (.startAfter1 .first), idle .first,
        CodeExtract.contents (encodeCode f) tail1 [] []⟩ : Config) =
      ⟨some (.after1 .first (.inr .check)), idle .first,
        CodeExtract.contents (encodeCode f) tail1 [] [true]⟩ := by
    simpa using startAfter1_step .first (encodeCode f) tail1
  have h5 : ((advance program)^[ts])
      (⟨some (.after1 .first (.inr .check)), idle .first,
        CodeExtract.contents (encodeCode f) tail1 [] [true]⟩ : Config) =
      ⟨some (.afterAfter1 .first), idle .first,
        CodeExtract.contents (encodeCode f) tail2 [] []⟩ := by
    simpa only [tail1, tail2, idle, scanEmbed, List.append_assoc] using hs
  have h6 : ((advance program)^[1])
      (⟨some (.afterAfter1 .first), idle .first,
        CodeExtract.contents (encodeCode f) tail2 [] []⟩ : Config) =
      ⟨some (.startAfter2 .first), idle .first,
        CodeExtract.contents (encodeCode f) tail2 [] []⟩ := by
    simpa using afterAfter1_step .first (encodeCode f) tail2
  have h7 : ((advance program)^[1])
      (⟨some (.startAfter2 .first), idle .first,
        CodeExtract.contents (encodeCode f) tail2 [] []⟩ : Config) =
      ⟨some (.after2 .first (.inr .check)), idle .first,
        CodeExtract.contents (encodeCode f) tail2 [] [true]⟩ := by
    simpa using startAfter2_step .first (encodeCode f) tail2
  have h8 : ((advance program)^[tt])
      (⟨some (.after2 .first (.inr .check)), idle .first,
        CodeExtract.contents (encodeCode f) tail2 [] [true]⟩ : Config) =
      ⟨some .done, idle .first,
        CodeExtract.contents (encodeCode f) rest [] []⟩ := by
    simpa only [tail2, idle, scanEmbed] using ht
  have h9 : ((advance program)^[1])
      (⟨some .done, idle .first,
        CodeExtract.contents (encodeCode f) rest [] []⟩ : Config) =
      output .first (encodeCode f) rest := by
    simpa using done_step .first (encodeCode f) rest
  have hrun := chain (chain (chain (chain (chain (chain (chain (chain
    (chain h0 h1) h2) h3) h4) h5) h6) h7) h8) h9
  refine ⟨1 + 1 + te + 1 + 1 + ts + 1 + 1 + tt + 1, ?_, ?_⟩
  · have hlen : word.length = (encodeCode f).length +
        (encodeCode s).length + (encodeCode t).length + rest.length := by
      simp only [word, List.length_append]
    have hsizeS := encodeCode_length s
    have hsizeT := encodeCode_length t
    dsimp [tail1, tail2] at hte hts htt
    simp only [List.length_append] at hte hts htt
    change 1 + 1 + te + 1 + 1 + ts + 1 + 1 + tt + 1 ≤ 25 * word.length + 30
    omega
  · exact hrun

theorem select_second (f s t : Code) (rest : List Bool) :
    ∃ n ≤ 25 * (encodeCode f ++ encodeCode s ++ encodeCode t ++ rest).length + 30,
      ((advance program)^[n])
        (initial .second (encodeCode f ++ encodeCode s ++ encodeCode t ++ rest)) =
        output .second (encodeCode s) rest := by
  let word := encodeCode f ++ encodeCode s ++ encodeCode t ++ rest
  let tail1 := encodeCode s ++ encodeCode t ++ rest
  let tail2 := encodeCode t ++ rest
  obtain ⟨tf, htf, hf⟩ := before1_stage .second f tail1
  obtain ⟨te, hte, he⟩ := extract_stage .second s tail2
  obtain ⟨tt, htt, ht⟩ := after1_stage .second (encodeCode s) t rest
  have h0 : ((advance program)^[1]) (initial .second word) =
      ⟨some (.startBefore1 .second), idle .second,
        CodeExtract.contents word [] [] []⟩ := by
    simpa using dispatch_step .second word
  have h1 : ((advance program)^[1])
      (⟨some (.startBefore1 .second), idle .second,
        CodeExtract.contents word [] [] []⟩ : Config) =
      ⟨some (.before1 .second (.inr .check)), idle .second,
        CodeExtract.contents word [] [] [true]⟩ := by
    simpa using startBefore1_step .second word
  have h2 : ((advance program)^[tf])
      (⟨some (.before1 .second (.inr .check)), idle .second,
        CodeExtract.contents word [] [] [true]⟩ : Config) =
      ⟨some (.afterBefore1 .second), idle .second,
        CodeExtract.contents tail1 [] [] []⟩ := by
    simpa only [word, tail1, idle, scanEmbed, List.append_assoc] using hf
  have h3 : ((advance program)^[1])
      (⟨some (.afterBefore1 .second), idle .second,
        CodeExtract.contents tail1 [] [] []⟩ : Config) =
      ⟨some (.startExtract .second), idle .second,
        CodeExtract.contents tail1 [] [] []⟩ := by
    simpa using afterBefore1_step .second tail1
  have h4 : ((advance program)^[1])
      (⟨some (.startExtract .second), idle .second,
        CodeExtract.contents tail1 [] [] []⟩ : Config) =
      ⟨some (.extract .second (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))),
        idle .second, CodeExtract.contents tail1 [] [] [true]⟩ := by
    simpa using startExtract_step .second tail1
  have h5 : ((advance program)^[te])
      (⟨some (.extract .second (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))),
        idle .second, CodeExtract.contents tail1 [] [] [true]⟩ : Config) =
      ⟨some (.afterExtract .second), idle .second,
        CodeExtract.contents (encodeCode s) tail2 [] []⟩ := by
    simpa only [tail1, tail2, idle, extractEmbed, fbank_output,
      List.append_assoc] using he
  have h6 : ((advance program)^[1])
      (⟨some (.afterExtract .second), idle .second,
        CodeExtract.contents (encodeCode s) tail2 [] []⟩ : Config) =
      ⟨some (.startAfter1 .second), idle .second,
        CodeExtract.contents (encodeCode s) tail2 [] []⟩ := by
    simpa using afterExtract_step .second (encodeCode s) tail2
  have h7 : ((advance program)^[1])
      (⟨some (.startAfter1 .second), idle .second,
        CodeExtract.contents (encodeCode s) tail2 [] []⟩ : Config) =
      ⟨some (.after1 .second (.inr .check)), idle .second,
        CodeExtract.contents (encodeCode s) tail2 [] [true]⟩ := by
    simpa using startAfter1_step .second (encodeCode s) tail2
  have h8 : ((advance program)^[tt])
      (⟨some (.after1 .second (.inr .check)), idle .second,
        CodeExtract.contents (encodeCode s) tail2 [] [true]⟩ : Config) =
      ⟨some (.afterAfter1 .second), idle .second,
        CodeExtract.contents (encodeCode s) rest [] []⟩ := by
    simpa only [tail2, idle, scanEmbed] using ht
  have h9 : ((advance program)^[1])
      (⟨some (.afterAfter1 .second), idle .second,
        CodeExtract.contents (encodeCode s) rest [] []⟩ : Config) =
      ⟨some .done, idle .second,
        CodeExtract.contents (encodeCode s) rest [] []⟩ := by
    simpa using afterAfter1_step .second (encodeCode s) rest
  have h10 : ((advance program)^[1])
      (⟨some .done, idle .second,
        CodeExtract.contents (encodeCode s) rest [] []⟩ : Config) =
      output .second (encodeCode s) rest := by
    simpa using done_step .second (encodeCode s) rest
  have hrun := chain (chain (chain (chain (chain (chain (chain (chain (chain
    (chain h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10
  refine ⟨1 + 1 + tf + 1 + 1 + te + 1 + 1 + tt + 1 + 1, ?_, ?_⟩
  · have hlen : word.length = (encodeCode f).length +
        (encodeCode s).length + (encodeCode t).length + rest.length := by
      simp only [word, List.length_append]
    have hfsize := encodeCode_length f
    have htsize := encodeCode_length t
    dsimp [tail1, tail2] at htf hte htt
    simp only [List.length_append] at htf hte htt
    change 1 + 1 + tf + 1 + 1 + te + 1 + 1 + tt + 1 + 1 ≤ 25 * word.length + 30
    omega
  · exact hrun

theorem select_third (f s t : Code) (rest : List Bool) :
    ∃ n ≤ 25 * (encodeCode f ++ encodeCode s ++ encodeCode t ++ rest).length + 30,
      ((advance program)^[n])
        (initial .third (encodeCode f ++ encodeCode s ++ encodeCode t ++ rest)) =
        output .third (encodeCode t) rest := by
  let word := encodeCode f ++ encodeCode s ++ encodeCode t ++ rest
  let tail1 := encodeCode s ++ encodeCode t ++ rest
  let tail2 := encodeCode t ++ rest
  obtain ⟨tf, htf, hf⟩ := before1_stage .third f tail1
  obtain ⟨ts, hts, hs⟩ := before2_stage .third s tail2
  obtain ⟨te, hte, he⟩ := extract_stage .third t rest
  have h0 : ((advance program)^[1]) (initial .third word) =
      ⟨some (.startBefore1 .third), idle .third,
        CodeExtract.contents word [] [] []⟩ := by
    simpa using dispatch_step .third word
  have h1 : ((advance program)^[1])
      (⟨some (.startBefore1 .third), idle .third,
        CodeExtract.contents word [] [] []⟩ : Config) =
      ⟨some (.before1 .third (.inr .check)), idle .third,
        CodeExtract.contents word [] [] [true]⟩ := by
    simpa using startBefore1_step .third word
  have h2 : ((advance program)^[tf])
      (⟨some (.before1 .third (.inr .check)), idle .third,
        CodeExtract.contents word [] [] [true]⟩ : Config) =
      ⟨some (.afterBefore1 .third), idle .third,
        CodeExtract.contents tail1 [] [] []⟩ := by
    simpa only [word, tail1, idle, scanEmbed, List.append_assoc] using hf
  have h3 : ((advance program)^[1])
      (⟨some (.afterBefore1 .third), idle .third,
        CodeExtract.contents tail1 [] [] []⟩ : Config) =
      ⟨some (.startBefore2 .third), idle .third,
        CodeExtract.contents tail1 [] [] []⟩ := by
    simpa using afterBefore1_step .third tail1
  have h4 : ((advance program)^[1])
      (⟨some (.startBefore2 .third), idle .third,
        CodeExtract.contents tail1 [] [] []⟩ : Config) =
      ⟨some (.before2 .third (.inr .check)), idle .third,
        CodeExtract.contents tail1 [] [] [true]⟩ := by
    simpa using startBefore2_step .third tail1
  have h5 : ((advance program)^[ts])
      (⟨some (.before2 .third (.inr .check)), idle .third,
        CodeExtract.contents tail1 [] [] [true]⟩ : Config) =
      ⟨some (.startExtract .third), idle .third,
        CodeExtract.contents tail2 [] [] []⟩ := by
    simpa only [tail1, tail2, idle, scanEmbed, List.append_assoc] using hs
  have h6 : ((advance program)^[1])
      (⟨some (.startExtract .third), idle .third,
        CodeExtract.contents tail2 [] [] []⟩ : Config) =
      ⟨some (.extract .third (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))),
        idle .third, CodeExtract.contents tail2 [] [] [true]⟩ := by
    simpa using startExtract_step .third tail2
  have h7 : ((advance program)^[te])
      (⟨some (.extract .third (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))),
        idle .third, CodeExtract.contents tail2 [] [] [true]⟩ : Config) =
      ⟨some (.afterExtract .third), idle .third,
        CodeExtract.contents (encodeCode t) rest [] []⟩ := by
    simpa only [tail2, idle, extractEmbed, fbank_output] using he
  have h8 : ((advance program)^[1])
      (⟨some (.afterExtract .third), idle .third,
        CodeExtract.contents (encodeCode t) rest [] []⟩ : Config) =
      ⟨some .done, idle .third,
        CodeExtract.contents (encodeCode t) rest [] []⟩ := by
    simpa using afterExtract_step .third (encodeCode t) rest
  have h9 : ((advance program)^[1])
      (⟨some .done, idle .third,
        CodeExtract.contents (encodeCode t) rest [] []⟩ : Config) =
      output .third (encodeCode t) rest := by
    simpa using done_step .third (encodeCode t) rest
  have hrun := chain (chain (chain (chain (chain (chain (chain (chain
    (chain h0 h1) h2) h3) h4) h5) h6) h7) h8) h9
  refine ⟨1 + 1 + tf + 1 + 1 + ts + 1 + te + 1 + 1, ?_, ?_⟩
  · have hlen : word.length = (encodeCode f).length +
        (encodeCode s).length + (encodeCode t).length + rest.length := by
      simp only [word, List.length_append]
    have hfsize := encodeCode_length f
    have hssize := encodeCode_length s
    simp only [List.length_append] at htf hts hte
    change 1 + 1 + tf + 1 + 1 + ts + 1 + te + 1 + 1 ≤ 25 * word.length + 30
    omega
  · exact hrun

theorem select_choice (c : UnaryChoice.Choice)
    (f s t : Code) (rest : List Bool) :
    ∃ n ≤ 25 * (encodeCode f ++ encodeCode s ++ encodeCode t ++ rest).length + 30,
      ((advance program)^[n])
        (initial c (encodeCode f ++ encodeCode s ++ encodeCode t ++ rest)) =
        output c (encodeCode (match c with
          | .first => f | .second => s | .third => t)) rest := by
  cases c with
  | first => exact select_first f s t rest
  | second => exact select_second f s t rest
  | third => exact select_third f s t rest

#print axioms select_choice

end Paper2.ChildSelect
