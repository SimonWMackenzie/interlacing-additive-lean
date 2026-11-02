import EthInapproximability.CurrentPaper.PrimeSamplerBinaryModularStep
import EthInapproximability.CurrentPaper.PrimeSamplerBinaryDigitFrame
import EthInapproximability.CurrentPaper.PrimeSamplerBinaryDigitStream
import EthInapproximability.CurrentPaper.BitMachineTrimLeadingZeros
import EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming

/-!
# Finite-bank framed-digit Horner controller

The stream is a sequence of self-delimiting binary digit frames. A fixed
fifteen-bank program parses one frame, calls the literal modular Horner step,
reverses and trims the remainder into the next MSB-first accumulator, clears
the quotient, and repeats until the stream is exhausted. The controller and
component run proofs are separated from an end-to-end query certificate.
-/

namespace EthInapproximability.CurrentPaper.PrimeSamplerBinaryHornerStream

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition

abbrev Stack := Fin 15

inductive Admin where
  | choose | move | trim | clear
  deriving DecidableEq, Fintype

abbrev Label := PrimeSamplerBinaryModularStep.Label ⊕
  (PrimeSamplerBinaryDigitFrame.Reader.Label ⊕ Admin)
abbrev Control := PrimeSamplerBinaryModularStep.Control ×
  (PrimeSamplerBinaryDigitFrame.Reader.Control × Option Bool)
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def initial : Control := (PrimeSamplerBinaryModularStep.initial, none, none)

def stepStacks : (Fin 14 ⊕ Fin 1) ≃ Stack := finSumFinEquiv

def readerPermutation : Stack ≃ Stack where
  toFun i := ![14,6,0,1,2,3,4,5,7,8,9,10,11,12,13] i
  invFun i := ![2,3,4,5,6,7,1,8,9,10,11,12,13,14,0] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def readerStacks : (Fin 2 ⊕ Fin 13) ≃ Stack :=
  finSumFinEquiv.trans readerPermutation

def readerLabels :
    (PrimeSamplerBinaryDigitFrame.Reader.Label ⊕
      (PrimeSamplerBinaryModularStep.Label ⊕ Admin)) ≃ Label where
  toFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inl l
    | .inr (.inr l) => .inr (.inr l)
  invFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inl l
    | .inr (.inr l) => .inr (.inr l)
  left_inv l := by rcases l with l | (l | l) <;> rfl
  right_inv l := by rcases l with l | (l | l) <;> rfl

def readerControl :
    (PrimeSamplerBinaryDigitFrame.Reader.Control ×
      (PrimeSamplerBinaryModularStep.Control × Option Bool)) ≃ Control where
  toFun s := (s.2.1, s.1, s.2.2)
  invFun s := (s.2.1, s.1, s.2.2)
  left_inv s := by rcases s with ⟨a,b,c⟩; rfl
  right_inv s := by rcases s with ⟨a,b,c⟩; rfl

def stepStart : PrimeSamplerBinaryModularStep.Label := .inl (.inr (.inr ()))

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => renameStmt stepStacks (Equiv.refl Label) (Equiv.refl Control)
      (liftStmt (some (.inr .move)) (PrimeSamplerBinaryModularStep.program l))
  | .inr (.inl l) => renameStmt readerStacks readerLabels readerControl
      (liftStmt (some (.inl stepStart))
        (PrimeSamplerBinaryDigitFrame.Reader.program l))
  | .inr (.inr .choose) =>
      pop 14 (fun s b => (s.1,s.2.1,b))
        (branch (fun s => s.2.2.isSome)
          (push 14 (fun s => s.2.2.getD false)
            (load (fun s => (s.1,none,none))
              (goto (fun _ => .inr (.inl .scan)))))
          halt)
  | .inr (.inr .move) =>
      pop 9 (fun s b => (s.1,s.2.1,b))
        (branch (fun s => s.2.2.isSome)
          (push 4 (fun s => s.2.2.getD false)
            (goto (fun _ => .inr (.inr .move))))
          (goto (fun _ => .inr (.inr .trim))))
  | .inr (.inr .trim) =>
      pop 4 (fun s b => (s.1,s.2.1,b))
        (branch (fun s => s.2.2.getD false)
          (push 4 (fun _ => true)
            (goto (fun _ => .inr (.inr .clear))))
          (branch (fun s => s.2.2.isSome)
            (goto (fun _ => .inr (.inr .trim)))
            (goto (fun _ => .inr (.inr .clear)))))
  | .inr (.inr .clear) =>
      pop 10 (fun s b => (s.1,s.2.1,b))
        (branch (fun s => s.2.2.isSome)
          (goto (fun _ => .inr (.inr .clear)))
          (goto (fun _ => .inr (.inr .choose))))

def bank (product multOperand multScratch coordinate accumulator copyScratch
    digit divInput prime remainder quotient old saved diff stream : List Bool) :
    Stack → List Bool :=
  ![product,multOperand,multScratch,coordinate,accumulator,copyScratch,
    digit,divInput,prime,remainder,quotient,old,saved,diff,stream]

def cfg (l : Option Label) (s : Control)
    (product multOperand multScratch coordinate accumulator copyScratch
      digit divInput prime remainder quotient old saved diff stream :
      List Bool) : Config :=
  ⟨l,s,bank product multOperand multScratch coordinate accumulator copyScratch
    digit divInput prime remainder quotient old saved diff stream⟩

def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

private theorem run_step {c d : Config} (h : TM2.step program c = some d)
    (t : ℕ) : run (t + 1) c = run t d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : Config} {t : ℕ} (h : run t c = d)
    (u : ℕ) : run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

def readerFrame (coordinate accumulator prime : List Bool)
    (c : TM2.Cfg (fun _ : Fin 2 => Bool)
      PrimeSamplerBinaryDigitFrame.Reader.Label
      PrimeSamplerBinaryDigitFrame.Reader.Control) : Config :=
  renameCfg readerStacks readerLabels readerControl
    (liftCfg (some (.inl stepStart))
      (PrimeSamplerBinaryModularStep.initial, none)
      (fun i : Fin 13 => ![[],[],[],coordinate,accumulator,[],[],prime,
        [],[],[],[],[]] i) c)

theorem readerFrame_start (coordinate accumulator prime digit tail : List Bool) :
    readerFrame coordinate accumulator prime
      (PrimeSamplerBinaryDigitFrame.Reader.cfg (some .scan) none
        (PrimeSamplerBinaryDigitFrame.frame digit tail) []) =
    cfg (some (.inr (.inl .scan))) initial
      [] [] [] coordinate accumulator [] [] [] prime [] [] [] [] []
      (PrimeSamplerBinaryDigitFrame.frame digit tail) := by
  unfold readerFrame cfg bank
  simp only [renameCfg, liftCfg]
  congr 1
  funext k
  fin_cases k <;>
    simp [readerStacks, readerPermutation,
      PrimeSamplerBinaryDigitFrame.Reader.cfg,
      PrimeSamplerBinaryDigitFrame.Reader.bank,
      finSumFinEquiv, Fin.addCases]

theorem readerFrame_end (coordinate accumulator prime digit tail : List Bool) :
    readerFrame coordinate accumulator prime
      (PrimeSamplerBinaryDigitFrame.Reader.cfg none (some false) tail digit) =
    cfg (some (.inl stepStart))
      (PrimeSamplerBinaryModularStep.initial, some false, none)
      [] [] [] coordinate accumulator [] digit [] prime [] [] [] [] [] tail := by
  unfold readerFrame cfg bank
  simp only [renameCfg, liftCfg]
  congr 1
  funext k
  fin_cases k <;>
    simp [readerStacks, readerPermutation,
      PrimeSamplerBinaryDigitFrame.Reader.cfg,
      PrimeSamplerBinaryDigitFrame.Reader.bank,
      finSumFinEquiv, Fin.addCases]

theorem reader_call (coordinate accumulator prime digit tail : List Bool) :
    ∃ n ≤ digit.length + 1,
      run n (cfg (some (.inr (.inl .scan))) initial
        [] [] [] coordinate accumulator [] [] [] prime [] [] [] [] []
        (PrimeSamplerBinaryDigitFrame.frame digit tail)) =
      cfg (some (.inl stepStart))
        (PrimeSamplerBinaryModularStep.initial, some false, none)
        [] [] [] coordinate accumulator [] digit [] prime [] [] [] [] [] tail := by
  have hQ : ∀ l, program (readerLabels (.inl l)) =
      renameStmt readerStacks readerLabels readerControl
        (liftStmt (some (.inl stepStart))
          (PrimeSamplerBinaryDigitFrame.Reader.program l)) := by
    intro l
    rfl
  have hr := PrimeSamplerBinaryDigitFrame.Reader.frame_run digit tail []
  have hhalt : (((advance PrimeSamplerBinaryDigitFrame.Reader.program)^[
      digit.length + 1])
      (PrimeSamplerBinaryDigitFrame.Reader.cfg (some .scan) none
        (PrimeSamplerBinaryDigitFrame.frame digit tail) [])).l = none := by
    change (PrimeSamplerBinaryDigitFrame.Reader.run (digit.length + 1)
      (PrimeSamplerBinaryDigitFrame.Reader.cfg (some .scan) none
        (PrimeSamplerBinaryDigitFrame.frame digit tail) [])).l = none
    rw [hr]
    rfl
  obtain ⟨n, hn, hglobal⟩ := BitMachineSubroutineRenaming.lift_outputs_renamed
    readerStacks readerLabels readerControl
    PrimeSamplerBinaryDigitFrame.Reader.program program
    (some (.inl stepStart)) hQ
    (PrimeSamplerBinaryModularStep.initial, none)
    (fun i : Fin 13 => ![[],[],[],coordinate,accumulator,[],[],prime,
      [],[],[],[],[]] i)
    (PrimeSamplerBinaryDigitFrame.Reader.cfg (some .scan) none
      (PrimeSamplerBinaryDigitFrame.frame digit tail) [])
    (digit.length + 1) hhalt
  refine ⟨n, hn, ?_⟩
  change run n (readerFrame coordinate accumulator prime _) =
    readerFrame coordinate accumulator prime _ at hglobal
  rw [show ((advance PrimeSamplerBinaryDigitFrame.Reader.program)^[
    digit.length + 1]) _ =
    PrimeSamplerBinaryDigitFrame.Reader.run (digit.length + 1) _ from rfl,
    hr] at hglobal
  simpa only [List.append_nil, readerFrame_start, readerFrame_end] using hglobal

def stepFrame (tail : List Bool)
    (c : PrimeSamplerBinaryModularStep.Config) : Config :=
  renameCfg stepStacks (Equiv.refl Label) (Equiv.refl Control)
    (liftCfg (some (.inr .move)) (some false, none)
      (fun _ : Fin 1 => tail) c)

theorem stepFrame_start (coordinate accumulator digit prime tail : List Bool) :
    stepFrame tail
      (PrimeSamplerBinaryModularStep.cfg (some stepStart)
        PrimeSamplerBinaryModularStep.initial
        [] [] [] coordinate accumulator [] digit [] prime [] [] [] [] []) =
    cfg (some (.inl stepStart))
      (PrimeSamplerBinaryModularStep.initial, some false, none)
      [] [] [] coordinate accumulator [] digit [] prime [] [] [] [] [] tail := by
  unfold stepFrame cfg bank
  simp only [renameCfg, liftCfg]
  congr 1
  funext k
  fin_cases k <;>
    simp [stepStacks, PrimeSamplerBinaryModularStep.cfg,
      PrimeSamplerBinaryModularStep.bank, finSumFinEquiv, Fin.addCases]

theorem stepFrame_end (coordinate accumulator digit prime tail : List Bool) :
    stepFrame tail
      (PrimeSamplerBinaryModularStep.cfg none
        PrimeSamplerBinaryModularStep.initial
        [] [] [] coordinate [] [] [] [] prime
        (BitMachineBinaryDivision.divideFrom
          (PrimeSamplerBinaryModularStep.sumWord accumulator coordinate digit).reverse
          prime [] []).1
        (BitMachineBinaryDivision.divideFrom
          (PrimeSamplerBinaryModularStep.sumWord accumulator coordinate digit).reverse
          prime [] []).2 [] [] []) =
    cfg (some (.inr (.inr .move)))
      (PrimeSamplerBinaryModularStep.initial, some false, none)
      [] [] [] coordinate [] [] [] [] prime
      (BitMachineBinaryDivision.divideFrom
        (PrimeSamplerBinaryModularStep.sumWord accumulator coordinate digit).reverse
        prime [] []).1
      (BitMachineBinaryDivision.divideFrom
        (PrimeSamplerBinaryModularStep.sumWord accumulator coordinate digit).reverse
        prime [] []).2 [] [] [] tail := by
  unfold stepFrame cfg bank
  simp only [renameCfg, liftCfg]
  congr 1
  funext k
  fin_cases k <;>
    simp [stepStacks, PrimeSamplerBinaryModularStep.cfg,
      PrimeSamplerBinaryModularStep.bank, finSumFinEquiv, Fin.addCases]

theorem step_call (coordinate accumulator digit prime tail : List Bool) :
    ∃ n ≤ PrimeSamplerBinaryModularStep.stepCost
        accumulator coordinate digit prime,
      run n (cfg (some (.inl stepStart))
        (PrimeSamplerBinaryModularStep.initial, some false, none)
        [] [] [] coordinate accumulator [] digit [] prime [] [] [] [] [] tail) =
      cfg (some (.inr (.inr .move)))
        (PrimeSamplerBinaryModularStep.initial, some false, none)
        [] [] [] coordinate [] [] [] [] prime
        (BitMachineBinaryDivision.divideFrom
          (PrimeSamplerBinaryModularStep.sumWord accumulator coordinate digit).reverse
          prime [] []).1
        (BitMachineBinaryDivision.divideFrom
          (PrimeSamplerBinaryModularStep.sumWord accumulator coordinate digit).reverse
          prime [] []).2 [] [] [] tail := by
  have hQ : ∀ l, program (.inl l) =
      renameStmt stepStacks (Equiv.refl Label) (Equiv.refl Control)
        (liftStmt (some (.inr .move))
          (PrimeSamplerBinaryModularStep.program l)) := by
    intro l
    rfl
  obtain ⟨u, hu, hr⟩ := PrimeSamplerBinaryModularStep.step_run
    accumulator coordinate digit prime
  have hhalt : (((advance PrimeSamplerBinaryModularStep.program)^[u])
      (PrimeSamplerBinaryModularStep.cfg (some stepStart)
        PrimeSamplerBinaryModularStep.initial
        [] [] [] coordinate accumulator [] digit [] prime [] [] [] [] [])).l = none := by
    change (PrimeSamplerBinaryModularStep.run u
      (PrimeSamplerBinaryModularStep.cfg (some stepStart)
        PrimeSamplerBinaryModularStep.initial
        [] [] [] coordinate accumulator [] digit [] prime [] [] [] [] [])).l = none
    simp only [stepStart]
    rw [hr]
    rfl
  obtain ⟨n, hn, hglobal⟩ := BitMachineSubroutineRenaming.lift_outputs_renamed
    stepStacks (Equiv.refl Label) (Equiv.refl Control)
    PrimeSamplerBinaryModularStep.program program (some (.inr .move)) hQ
    (some false, none) (fun _ : Fin 1 => tail)
    (PrimeSamplerBinaryModularStep.cfg (some stepStart)
      PrimeSamplerBinaryModularStep.initial
      [] [] [] coordinate accumulator [] digit [] prime [] [] [] [] [])
    u hhalt
  refine ⟨n, hn.trans hu, ?_⟩
  change run n (stepFrame tail _) = stepFrame tail _ at hglobal
  simp only [stepStart] at hglobal
  rw [show ((advance PrimeSamplerBinaryModularStep.program)^[u]) _ =
    PrimeSamplerBinaryModularStep.run u _ from rfl, hr] at hglobal
  calc
    run n (cfg (some (.inl stepStart))
      (PrimeSamplerBinaryModularStep.initial, some false, none)
      [] [] [] coordinate accumulator [] digit [] prime [] [] [] [] [] tail) =
        run n (stepFrame tail
          (PrimeSamplerBinaryModularStep.cfg (some stepStart)
            PrimeSamplerBinaryModularStep.initial
            [] [] [] coordinate accumulator [] digit [] prime [] [] [] [] [])) := by
          rw [stepFrame_start]
    _ = stepFrame tail
          (PrimeSamplerBinaryModularStep.cfg none
            PrimeSamplerBinaryModularStep.initial
            [] [] [] coordinate [] [] [] [] prime
            (BitMachineBinaryDivision.divideFrom
              (PrimeSamplerBinaryModularStep.sumWord accumulator coordinate digit).reverse
              prime [] []).1
            (BitMachineBinaryDivision.divideFrom
              (PrimeSamplerBinaryModularStep.sumWord accumulator coordinate digit).reverse
              prime [] []).2 [] [] []) := hglobal
    _ = _ := stepFrame_end coordinate accumulator digit prime tail

def phaseCfg (phase : Admin) (marker : Option Bool)
    (coordinate accumulator prime remainder quotient stream : List Bool) :
    Config :=
  cfg (some (.inr (.inr phase)))
    (PrimeSamplerBinaryModularStep.initial, some false, marker)
    [] [] [] coordinate accumulator [] [] [] prime remainder quotient
    [] [] [] stream

private theorem step_move_cons (marker : Option Bool) (x : Bool)
    (coordinate accumulator prime remainder quotient stream : List Bool) :
    TM2.step program
      (phaseCfg .move marker coordinate accumulator prime
        (x :: remainder) quotient stream) =
      some (phaseCfg .move (some x) coordinate (x :: accumulator) prime
        remainder quotient stream) := by
  simp [TM2.step, TM2.stepAux, program, phaseCfg, cfg, bank]
  funext k
  fin_cases k <;> simp [bank]

private theorem step_move_nil (marker : Option Bool)
    (coordinate accumulator prime quotient stream : List Bool) :
    TM2.step program
      (phaseCfg .move marker coordinate accumulator prime [] quotient stream) =
      some (phaseCfg .trim none coordinate accumulator prime [] quotient stream) := by
  simp [TM2.step, TM2.stepAux, program, phaseCfg, cfg, bank]

theorem move_run (marker : Option Bool)
    (coordinate accumulator prime remainder quotient stream : List Bool) :
    run (remainder.length + 1)
      (phaseCfg .move marker coordinate accumulator prime remainder quotient stream) =
      phaseCfg .trim none coordinate (remainder.reverse ++ accumulator)
        prime [] quotient stream := by
  induction remainder generalizing marker accumulator with
  | nil => simpa using
      (run_step (step_move_nil marker coordinate accumulator prime quotient stream) 0)
  | cons x xs ih =>
      rw [List.length_cons, run_step
        (step_move_cons marker x coordinate accumulator prime xs quotient stream)]
      simpa [List.reverse_cons, List.append_assoc] using
        ih (some x) (x :: accumulator)

private theorem step_trim_false (marker : Option Bool)
    (coordinate prime quotient stream : List Bool) (bs : List Bool) :
    TM2.step program
      (phaseCfg .trim marker coordinate (false :: bs) prime [] quotient stream) =
      some (phaseCfg .trim (some false) coordinate bs prime [] quotient stream) := by
  simp [TM2.step, TM2.stepAux, program, phaseCfg, cfg, bank]
  funext k
  fin_cases k <;> simp [bank]

private theorem step_trim_true (marker : Option Bool)
    (coordinate prime quotient stream : List Bool) (bs : List Bool) :
    TM2.step program
      (phaseCfg .trim marker coordinate (true :: bs) prime [] quotient stream) =
      some (phaseCfg .clear (some true) coordinate (true :: bs)
        prime [] quotient stream) := by
  simp [TM2.step, TM2.stepAux, program, phaseCfg, cfg, bank]

private theorem step_trim_nil (marker : Option Bool)
    (coordinate prime quotient stream : List Bool) :
    TM2.step program
      (phaseCfg .trim marker coordinate [] prime [] quotient stream) =
      some (phaseCfg .clear none coordinate [] prime [] quotient stream) := by
  simp [TM2.step, TM2.stepAux, program, phaseCfg, cfg, bank]

theorem trim_run (marker : Option Bool)
    (coordinate word prime quotient stream : List Bool) :
    ∃ outMarker : Option Bool,
      run (BitMachineTrimLeadingZeros.trimTime word)
        (phaseCfg .trim marker coordinate word prime [] quotient stream) =
      phaseCfg .clear outMarker coordinate
        (BitMachineTrimLeadingZeros.trim word) prime [] quotient stream := by
  induction word generalizing marker with
  | nil =>
      exact ⟨none, by simpa [BitMachineTrimLeadingZeros.trimTime,
        BitMachineTrimLeadingZeros.trim] using
        (run_step (step_trim_nil marker coordinate prime quotient stream) 0)⟩
  | cons b bs ih =>
      cases b with
      | false =>
          obtain ⟨out, hout⟩ := ih (some false)
          refine ⟨out, ?_⟩
          rw [BitMachineTrimLeadingZeros.trimTime,
            run_step (step_trim_false marker coordinate prime quotient stream bs)]
          simpa [BitMachineTrimLeadingZeros.trim] using hout
      | true =>
          exact ⟨some true, by
            simpa [BitMachineTrimLeadingZeros.trimTime,
              BitMachineTrimLeadingZeros.trim] using
              (run_step (step_trim_true marker coordinate prime quotient stream bs) 0)⟩

private theorem step_clear_cons (marker : Option Bool) (x : Bool)
    (coordinate accumulator prime quotient stream : List Bool) :
    TM2.step program
      (phaseCfg .clear marker coordinate accumulator prime []
        (x :: quotient) stream) =
      some (phaseCfg .clear (some x) coordinate accumulator prime []
        quotient stream) := by
  simp [TM2.step, TM2.stepAux, program, phaseCfg, cfg, bank]
  funext k
  fin_cases k <;> simp [bank]

private theorem step_clear_nil (marker : Option Bool)
    (coordinate accumulator prime stream : List Bool) :
    TM2.step program
      (phaseCfg .clear marker coordinate accumulator prime [] [] stream) =
      some (phaseCfg .choose none coordinate accumulator prime [] [] stream) := by
  simp [TM2.step, TM2.stepAux, program, phaseCfg, cfg, bank]

theorem clear_run (marker : Option Bool)
    (coordinate accumulator prime quotient stream : List Bool) :
    run (quotient.length + 1)
      (phaseCfg .clear marker coordinate accumulator prime [] quotient stream) =
      phaseCfg .choose none coordinate accumulator prime [] [] stream := by
  induction quotient generalizing marker with
  | nil => simpa using
      (run_step (step_clear_nil marker coordinate accumulator prime stream) 0)
  | cons x qs ih =>
      rw [List.length_cons, run_step
        (step_clear_cons marker x coordinate accumulator prime qs stream)]
      exact ih (some x)

private theorem step_choose_cons (b : Bool) (tail : List Bool)
    (coordinate accumulator prime : List Bool) :
    TM2.step program
      (phaseCfg .choose none coordinate accumulator prime [] [] (b :: tail)) =
      some (cfg (some (.inr (.inl .scan))) initial
        [] [] [] coordinate accumulator [] [] [] prime [] [] [] [] []
        (b :: tail)) := by
  simp [TM2.step, TM2.stepAux, program, phaseCfg, cfg, bank, initial]

private theorem step_choose_nil (coordinate accumulator prime : List Bool) :
    TM2.step program
      (phaseCfg .choose none coordinate accumulator prime [] [] []) =
      some (cfg none (PrimeSamplerBinaryModularStep.initial, some false, none)
        [] [] [] coordinate accumulator [] [] [] prime [] [] [] [] [] []) := by
  simp [TM2.step, TM2.stepAux, program, phaseCfg, cfg, bank]

theorem frame_nonempty (digit tail : List Bool) :
    ∃ b rest, PrimeSamplerBinaryDigitFrame.frame digit tail = b :: rest := by
  unfold PrimeSamplerBinaryDigitFrame.frame
  cases h : PrimeSamplerBinaryDigitFrame.marked digit.reverse with
  | nil => exact ⟨false,tail,by simp [h]⟩
  | cons b rest => exact ⟨b,rest ++ false :: tail,by simp [h]⟩

theorem choose_frame_run (coordinate accumulator prime digit tail : List Bool) :
    run 1 (phaseCfg .choose none coordinate accumulator prime [] []
      (PrimeSamplerBinaryDigitFrame.frame digit tail)) =
      cfg (some (.inr (.inl .scan))) initial
        [] [] [] coordinate accumulator [] [] [] prime [] [] [] [] []
        (PrimeSamplerBinaryDigitFrame.frame digit tail) := by
  obtain ⟨b,rest,hframe⟩ := frame_nonempty digit tail
  rw [hframe]
  simpa [run] using run_step
    (step_choose_cons b rest coordinate accumulator prime) 0

def remainderWord (accumulator coordinate digit prime : List Bool) : List Bool :=
  (BitMachineBinaryDivision.divideFrom
    (PrimeSamplerBinaryModularStep.sumWord accumulator coordinate digit).reverse
    prime [] []).1

def quotientWord (accumulator coordinate digit prime : List Bool) : List Bool :=
  (BitMachineBinaryDivision.divideFrom
    (PrimeSamplerBinaryModularStep.sumWord accumulator coordinate digit).reverse
    prime [] []).2

def digitCost (accumulator coordinate digit prime : List Bool) : ℕ :=
  1 + (digit.length + 1) +
    PrimeSamplerBinaryModularStep.stepCost accumulator coordinate digit prime +
    (remainderWord accumulator coordinate digit prime).length + 1 +
    BitMachineTrimLeadingZeros.trimTime
      (remainderWord accumulator coordinate digit prime).reverse +
    (quotientWord accumulator coordinate digit prime).length + 1

theorem digit_run (accumulator coordinate digit prime tail : List Bool) :
    ∃ t ≤ digitCost accumulator coordinate digit prime,
      run t (phaseCfg .choose none coordinate accumulator prime [] []
        (PrimeSamplerBinaryDigitFrame.frame digit tail)) =
      phaseCfg .choose none coordinate
        (BitMachineTrimLeadingZeros.trim
          (remainderWord accumulator coordinate digit prime).reverse)
        prime [] [] tail := by
  let r := remainderWord accumulator coordinate digit prime
  let q := quotientWord accumulator coordinate digit prime
  have hchoose := choose_frame_run coordinate accumulator prime digit tail
  obtain ⟨n₁, hn₁, hread⟩ := reader_call
    coordinate accumulator prime digit tail
  obtain ⟨n₂, hn₂, hstep⟩ := step_call
    coordinate accumulator digit prime tail
  have hmove := move_run none coordinate [] prime r q tail
  simp only [List.append_nil] at hmove
  obtain ⟨marker, htrim⟩ := trim_run none coordinate r.reverse prime q tail
  have hclear := clear_run marker coordinate
    (BitMachineTrimLeadingZeros.trim r.reverse) prime q tail
  have h₁ := (run_add hchoose n₁).trans hread
  have h₂ := (run_add h₁ n₂).trans hstep
  have h₃ := (run_add h₂ (r.length + 1)).trans hmove
  have h₄ := (run_add h₃ (BitMachineTrimLeadingZeros.trimTime r.reverse)).trans htrim
  have h₅ := (run_add h₄ (q.length + 1)).trans hclear
  refine ⟨1 + n₁ + n₂ + (r.length + 1) +
    BitMachineTrimLeadingZeros.trimTime r.reverse + (q.length + 1), ?_, ?_⟩
  · dsimp [digitCost, r, q] at *
    omega
  · simpa only [digitCost, r, q] using h₅

theorem digit_value (accumulator coordinate digit prime : List Bool)
    (hp : 0 < EncodedCommunication.bitsValue prime) :
    BitMachineBinaryDivision.msbValue
        (BitMachineTrimLeadingZeros.trim
          (remainderWord accumulator coordinate digit prime).reverse) =
      (EncodedCommunication.bitsValue coordinate *
          BitMachineBinaryDivision.msbValue accumulator +
        EncodedCommunication.bitsValue digit) %
          EncodedCommunication.bitsValue prime := by
  rw [BitMachineTrimLeadingZeros.trim_value,
    PrimeSamplerBinaryDigit.msbValue_reverse]
  exact PrimeSamplerBinaryModularStep.step_value accumulator coordinate digit prime hp

theorem digit_accumulator_length (accumulator coordinate digit prime : List Bool)
    (hp : 0 < EncodedCommunication.bitsValue prime) :
    (BitMachineTrimLeadingZeros.trim
      (remainderWord accumulator coordinate digit prime).reverse).length ≤
        prime.length := by
  apply BitMachineTrimLeadingZeros.trim_length_le_of_value_lt_pow
  rw [PrimeSamplerBinaryDigit.msbValue_reverse]
  rw [show EncodedCommunication.bitsValue
      (remainderWord accumulator coordinate digit prime) =
      (EncodedCommunication.bitsValue coordinate *
          BitMachineBinaryDivision.msbValue accumulator +
        EncodedCommunication.bitsValue digit) %
          EncodedCommunication.bitsValue prime from
    PrimeSamplerBinaryModularStep.step_value accumulator coordinate digit prime hp]
  have hmod : (EncodedCommunication.bitsValue coordinate *
      BitMachineBinaryDivision.msbValue accumulator +
      EncodedCommunication.bitsValue digit) %
      EncodedCommunication.bitsValue prime <
      EncodedCommunication.bitsValue prime := Nat.mod_lt _ hp
  exact lt_trans hmod
    (BitMachineBinarySubtract.bitsValue_lt_pow prime)

theorem digitCost_poly (accumulator coordinate digit prime : List Bool) :
    let S := accumulator.length + coordinate.length + digit.length + prime.length
    digitCost accumulator coordinate digit prime ≤ 200 * (S + 1) ^ 2 := by
  let S := accumulator.length + coordinate.length + digit.length + prime.length
  let sum := PrimeSamplerBinaryModularStep.sumWord accumulator coordinate digit
  let r := remainderWord accumulator coordinate digit prime
  let q := quotientWord accumulator coordinate digit prime
  have hs := PrimeSamplerBinaryModularStep.sumWord_length_le
    accumulator coordinate digit prime
  have hsum : sum.length ≤ 2 * S + 1 := by simpa [sum, S] using hs
  have hr := BitMachineBinaryDivision.divideFrom_remainder_length
    sum.reverse prime [] [] sum.length (by simp) (by simp)
  have hrem : r.length ≤ sum.length + prime.length := by
    simpa [r, sum, remainderWord] using hr
  have hq := BitMachineBinaryDivision.divideFrom_quotient_length
    sum.reverse prime [] []
  have hquot : q.length = sum.length := by
    simpa [q, sum, quotientWord] using hq
  have ht := BitMachineTrimLeadingZeros.trimTime_le r.reverse
  simp only [List.length_reverse] at ht
  have hc := PrimeSamplerBinaryModularStep.stepCost_poly
    accumulator coordinate digit prime
  dsimp only at hc
  dsimp [digitCost]
  nlinarith [sq_nonneg (S + 1)]

def evaluateWords (coordinate prime : List Bool) :
    List (List Bool) → List Bool → List Bool
  | [], accumulator => accumulator
  | digit :: tail, accumulator =>
      evaluateWords coordinate prime tail
        (BitMachineTrimLeadingZeros.trim
          (remainderWord accumulator coordinate digit prime).reverse)

def wordCostBound (coordinate prime : List Bool) (D : ℕ) : ℕ :=
  200 * (2 * prime.length + coordinate.length + D + 1) ^ 2

theorem digitCost_le_wordCostBound
    (accumulator coordinate digit prime : List Bool) (D : ℕ)
    (hacc : accumulator.length ≤ prime.length)
    (hdigit : digit.length ≤ D) :
    digitCost accumulator coordinate digit prime ≤
      wordCostBound coordinate prime D := by
  have hc := digitCost_poly accumulator coordinate digit prime
  dsimp only at hc
  dsimp [wordCostBound]
  have hs : accumulator.length + coordinate.length + digit.length +
      prime.length + 1 ≤
      2 * prime.length + coordinate.length + D + 1 := by omega
  nlinarith

theorem choose_nil_run (coordinate accumulator prime : List Bool) :
    run 1 (phaseCfg .choose none coordinate accumulator prime [] [] []) =
      cfg none (PrimeSamplerBinaryModularStep.initial, some false, none)
        [] [] [] coordinate accumulator [] [] [] prime [] [] [] [] [] [] := by
  simpa [run] using run_step
    (step_choose_nil coordinate accumulator prime) 0

theorem evaluateWords_run (coordinate prime : List Bool)
    (hp : 0 < EncodedCommunication.bitsValue prime)
    (D : ℕ) (words : List (List Bool))
    (hwords : ∀ w ∈ words, w.length ≤ D)
    (accumulator : List Bool) (hacc : accumulator.length ≤ prime.length) :
    ∃ t ≤ words.length * wordCostBound coordinate prime D + 1,
      run t (phaseCfg .choose none coordinate accumulator prime [] []
        (PrimeSamplerBinaryDigitStream.encodeWords words [])) =
      cfg none (PrimeSamplerBinaryModularStep.initial, some false, none)
        [] [] [] coordinate (evaluateWords coordinate prime words accumulator)
        [] [] [] prime [] [] [] [] [] [] := by
  induction words generalizing accumulator with
  | nil =>
      refine ⟨1, by simp, ?_⟩
      simpa [PrimeSamplerBinaryDigitStream.encodeWords, evaluateWords]
        using choose_nil_run coordinate accumulator prime
  | cons digit tail ih =>
      have hdigit : digit.length ≤ D := hwords digit (by simp)
      have htail : ∀ w ∈ tail, w.length ≤ D := by
        intro w hw
        exact hwords w (by simp [hw])
      obtain ⟨u, hu, hstep⟩ := digit_run
        accumulator coordinate digit prime
        (PrimeSamplerBinaryDigitStream.encodeWords tail [])
      let next := BitMachineTrimLeadingZeros.trim
        (remainderWord accumulator coordinate digit prime).reverse
      have hnext : next.length ≤ prime.length :=
        digit_accumulator_length accumulator coordinate digit prime hp
      obtain ⟨v, hv, hrest⟩ := ih htail next hnext
      have hchain := (run_add hstep v).trans hrest
      have hcost := digitCost_le_wordCostBound
        accumulator coordinate digit prime D hacc hdigit
      refine ⟨u + v, ?_, ?_⟩
      · simp only [List.length_cons, Nat.add_mul, one_mul]
        omega
      · simpa [PrimeSamplerBinaryDigitStream.encodeWords, evaluateWords, next]
          using hchain

theorem evaluateWords_value (coordinate prime : List Bool)
    (hp : 0 < EncodedCommunication.bitsValue prime)
    (words : List (List Bool)) (accumulator : List Bool) :
    BitMachineBinaryDivision.msbValue
      (evaluateWords coordinate prime words accumulator) =
      (words.map EncodedCommunication.bitsValue).foldl
        (fun h d => (EncodedCommunication.bitsValue coordinate * h + d) %
          EncodedCommunication.bitsValue prime)
        (BitMachineBinaryDivision.msbValue accumulator) := by
  induction words generalizing accumulator with
  | nil => rfl
  | cons digit tail ih =>
      simp only [evaluateWords, List.map_cons, List.foldl_cons]
      rw [ih]
      rw [digit_value accumulator coordinate digit prime hp]

theorem evaluateWords_length (coordinate prime : List Bool)
    (hp : 0 < EncodedCommunication.bitsValue prime)
    (words : List (List Bool)) (accumulator : List Bool)
    (hacc : accumulator.length ≤ prime.length) :
    (evaluateWords coordinate prime words accumulator).length ≤ prime.length := by
  induction words generalizing accumulator with
  | nil => exact hacc
  | cons digit tail ih =>
      exact ih _ (digit_accumulator_length accumulator coordinate digit prime hp)

theorem run_label_horner (labelBits coordinate prime : List Bool)
    (hp : 0 < EncodedCommunication.bitsValue prime) :
    let words := PrimeSamplerBinaryDigitStream.streamWords prime
      (labelBits.length + 1) labelBits.reverse
    ∃ t ≤ (labelBits.length + 1) *
        wordCostBound coordinate prime (labelBits.length + prime.length) + 1,
      run t (phaseCfg .choose none coordinate [] prime [] []
        (PrimeSamplerBinaryDigitStream.encodeWords words [])) =
      cfg none (PrimeSamplerBinaryModularStep.initial, some false, none)
        [] [] [] coordinate (evaluateWords coordinate prime words [])
        [] [] [] prime [] [] [] [] [] [] := by
  dsimp
  let words := PrimeSamplerBinaryDigitStream.streamWords prime
    (labelBits.length + 1) labelBits.reverse
  obtain ⟨u, hu, hr⟩ := evaluateWords_run coordinate prime hp
    (labelBits.length + prime.length) words
    (PrimeSamplerBinaryDigitStream.label_stream_word_length labelBits prime)
    [] (by simp)
  have hlen := PrimeSamplerBinaryDigitStream.streamWords_length_le_fuel
    prime (labelBits.length + 1) labelBits.reverse
  refine ⟨u, ?_, hr⟩
  change words.length ≤ labelBits.length + 1 at hlen
  nlinarith

theorem label_horner_value (labelBits coordinate prime : List Bool)
    (hp : 2 ≤ EncodedCommunication.bitsValue prime)
    (degree : ℕ)
    (hlabel : EncodedCommunication.bitsValue labelBits <
      EncodedCommunication.bitsValue prime ^ degree) :
    let words := PrimeSamplerBinaryDigitStream.streamWords prime
      (labelBits.length + 1) labelBits.reverse
    BitMachineBinaryDivision.msbValue
      (evaluateWords coordinate prime words []) =
      PrimeSamplerEntryAlgorithm.horner
        (EncodedCommunication.bitsValue prime)
        (EncodedCommunication.bitsValue coordinate) degree
        (EncodedCommunication.bitsValue labelBits) := by
  dsimp
  let words := PrimeSamplerBinaryDigitStream.streamWords prime
    (labelBits.length + 1) labelBits.reverse
  have hv := evaluateWords_value coordinate prime (by omega) words []
  have hw := PrimeSamplerBinaryDigitStream.label_stream_values labelBits prime hp
  change words.map EncodedCommunication.bitsValue = _ at hw
  rw [hw] at hv
  have hmain := PrimeSamplerSignificantDigits.evaluate_word_digits
    (EncodedCommunication.bitsValue prime)
    (EncodedCommunication.bitsValue coordinate) degree hp labelBits hlabel
  cases hz : EncodedCommunication.bitsValue labelBits with
  | zero =>
      simp only [hz, ↓reduceIte] at hv
      simp [PrimeSamplerEntryAlgorithm.evaluate,
        PrimeSamplerSignificantDigits.digits_zero, hz] at hmain
      simpa [PrimeSamplerEntryAlgorithm.evaluate] using hv.trans hmain
  | succ v =>
      rw [hz] at hv hmain
      simp only [Nat.succ_ne_zero, ↓reduceIte] at hv
      simpa [PrimeSamplerEntryAlgorithm.evaluate, hz] using hv.trans hmain

end EthInapproximability.CurrentPaper.PrimeSamplerBinaryHornerStream
