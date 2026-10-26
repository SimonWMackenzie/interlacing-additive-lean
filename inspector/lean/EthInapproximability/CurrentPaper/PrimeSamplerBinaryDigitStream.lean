import EthInapproximability.CurrentPaper.PrimeSamplerBinaryDigitFrame
import EthInapproximability.CurrentPaper.PrimeSamplerBinaryQuotientAdvance
import EthInapproximability.CurrentPaper.BitMachineBinaryDivision
import EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming
import EthInapproximability.CurrentPaper.PrimeSamplerBinaryDigit
import EthInapproximability.CurrentPaper.PrimeSamplerSignificantDigits

/-!
# Fixed-bank significant-digit stream controller

This program physically repeats binary division, writes a framed digit, and
tests/transfers the quotient. It uses nine Boolean banks with finite control.
Its zero-quotient branch tests numerical value, not stack emptiness. The
program is stated separately from its end-to-end execution certificate.
-/

namespace EthInapproximability.CurrentPaper.PrimeSamplerBinaryDigitStream

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition

abbrev Stack := Fin 9
abbrev Label := BitMachineBinaryDivision.Label ⊕
  (PrimeSamplerBinaryDigitFrame.Writer.Label ⊕
    (PrimeSamplerBinaryQuotientAdvance.Label ⊕ Unit))
abbrev Control := BitMachineBinaryDivision.Control ×
  (PrimeSamplerBinaryDigitFrame.Writer.Control ×
    PrimeSamplerBinaryQuotientAdvance.Control)
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def initial : Control :=
  (BitMachineBinaryDivision.initial, none,
    PrimeSamplerBinaryQuotientAdvance.initial)

def divisionStacks : (Fin 7 ⊕ Fin 2) ≃ Stack := finSumFinEquiv

def writerPermutation : Stack ≃ Stack where
  toFun i := ![2,8,0,1,3,4,5,6,7] i
  invFun i := ![2,3,0,4,5,6,7,8,1] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def writerStacks : (Fin 2 ⊕ Fin 7) ≃ Stack :=
  finSumFinEquiv.trans writerPermutation

def advancePermutation : Stack ≃ Stack where
  toFun i := ![3,7,0,1,2,4,5,6,8] i
  invFun i := ![2,3,4,0,5,6,7,1,8] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def advanceStacks : (Fin 3 ⊕ Fin 6) ≃ Stack :=
  finSumFinEquiv.trans advancePermutation

def writerLabels :
    (PrimeSamplerBinaryDigitFrame.Writer.Label ⊕
      (BitMachineBinaryDivision.Label ⊕
        (PrimeSamplerBinaryQuotientAdvance.Label ⊕ Unit))) ≃ Label where
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

def advanceLabels :
    (PrimeSamplerBinaryQuotientAdvance.Label ⊕
      (BitMachineBinaryDivision.Label ⊕
        (PrimeSamplerBinaryDigitFrame.Writer.Label ⊕ Unit))) ≃ Label where
  toFun
    | .inl l => .inr (.inr (.inl l))
    | .inr (.inl l) => .inl l
    | .inr (.inr (.inl l)) => .inr (.inl l)
    | .inr (.inr (.inr l)) => .inr (.inr (.inr l))
  invFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inr (.inr (.inl l))
    | .inr (.inr (.inl l)) => .inl l
    | .inr (.inr (.inr l)) => .inr (.inr (.inr l))
  left_inv l := by rcases l with l | (l | (l | l)) <;> rfl
  right_inv l := by rcases l with l | (l | (l | l)) <;> rfl

def writerControl :
    (PrimeSamplerBinaryDigitFrame.Writer.Control ×
      (BitMachineBinaryDivision.Control ×
        PrimeSamplerBinaryQuotientAdvance.Control)) ≃ Control where
  toFun s := (s.2.1, s.1, s.2.2)
  invFun s := (s.2.1, s.1, s.2.2)
  left_inv s := by rcases s with ⟨a,b,c⟩; rfl
  right_inv s := by rcases s with ⟨a,b,c⟩; rfl

def advanceControl :
    (PrimeSamplerBinaryQuotientAdvance.Control ×
      (BitMachineBinaryDivision.Control ×
        PrimeSamplerBinaryDigitFrame.Writer.Control)) ≃ Control where
  toFun s := (s.2.1, s.2.2, s.1)
  invFun s := (s.2.2, s.1, s.2.1)
  left_inv s := by rcases s with ⟨a,b,c⟩; rfl
  right_inv s := by rcases s with ⟨a,b,c⟩; rfl

def admin : Label := .inr (.inr (.inr ()))

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => renameStmt divisionStacks (Equiv.refl Label) (Equiv.refl Control)
      (liftStmt (some (.inl .start)) (BitMachineBinaryDivision.program l))
  | .inr (.inl l) => renameStmt writerStacks writerLabels writerControl
      (liftStmt (some (.inr (.inl .scan)))
        (PrimeSamplerBinaryDigitFrame.Writer.program l))
  | .inr (.inr (.inl l)) =>
      renameStmt advanceStacks advanceLabels advanceControl
        (liftStmt (some (.inr (.inr ())))
          (PrimeSamplerBinaryQuotientAdvance.program l))
  | .inr (.inr (.inr ())) =>
      branch (fun s => s.2.2.seenOne)
        (load (fun _ => initial) (goto (fun _ => .inl .outer)))
        halt

def bank (dividend prime remainder quotient old saved diff scratch stream :
    List Bool) : Stack → List Bool :=
  ![dividend,prime,remainder,quotient,old,saved,diff,scratch,stream]

def cfg (l : Option Label) (s : Control)
    (dividend prime remainder quotient old saved diff scratch stream :
      List Bool) : Config :=
  ⟨l,s,bank dividend prime remainder quotient old saved diff scratch stream⟩

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

private theorem run_step {c d : Config} (h : TM2.step program c = some d)
    (t : ℕ) : run (t + 1) c = run t d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : Config} {t : ℕ} (h : run t c = d)
    (u : ℕ) : run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

def divisionFrame (scratch stream : List Bool)
    (c : BitMachineBinaryDivision.Config) : Config :=
  renameCfg divisionStacks (Equiv.refl Label) (Equiv.refl Control)
    (liftCfg (some (.inl .start))
      (none, PrimeSamplerBinaryQuotientAdvance.initial)
      (fun i : Fin 2 => ![scratch,stream] i) c)

theorem divisionFrame_start (dividend prime scratch stream : List Bool) :
    divisionFrame scratch stream
      (BitMachineBinaryDivision.cfg (some .outer)
        BitMachineBinaryDivision.initial dividend prime [] [] [] [] []) =
    cfg (some (.inl .outer)) initial
      dividend prime [] [] [] [] [] scratch stream := by
  unfold divisionFrame cfg bank
  simp only [renameCfg, liftCfg]
  congr 1
  funext k
  fin_cases k <;>
    simp [divisionStacks, BitMachineBinaryDivision.cfg,
      BitMachineBinaryDivision.bank, finSumFinEquiv, Fin.addCases]

theorem divisionFrame_end (dividend prime scratch stream : List Bool) :
    divisionFrame scratch stream
      (BitMachineBinaryDivision.cfg none BitMachineBinaryDivision.initial
        [] prime (BitMachineBinaryDivision.divideFrom dividend prime [] []).1
        (BitMachineBinaryDivision.divideFrom dividend prime [] []).2 [] [] []) =
    cfg (some (.inr (.inl .start))) initial [] prime
      (BitMachineBinaryDivision.divideFrom dividend prime [] []).1
      (BitMachineBinaryDivision.divideFrom dividend prime [] []).2
      [] [] [] scratch stream := by
  unfold divisionFrame cfg bank
  simp only [renameCfg, liftCfg]
  congr 1
  funext k
  fin_cases k <;>
    simp [divisionStacks, BitMachineBinaryDivision.cfg,
      BitMachineBinaryDivision.bank, finSumFinEquiv, Fin.addCases]

theorem division_call (dividend prime scratch stream : List Bool) :
    ∃ n ≤ BitMachineBinaryDivision.totalTime dividend prime [],
      run n (cfg (some (.inl .outer)) initial
        dividend prime [] [] [] [] [] scratch stream) =
      cfg (some (.inr (.inl .start))) initial [] prime
        (BitMachineBinaryDivision.divideFrom dividend prime [] []).1
        (BitMachineBinaryDivision.divideFrom dividend prime [] []).2
        [] [] [] scratch stream := by
  have hQ : ∀ l, program (.inl l) =
      renameStmt divisionStacks (Equiv.refl Label) (Equiv.refl Control)
        (liftStmt (some (.inl .start))
          (BitMachineBinaryDivision.program l)) := by
    intro l
    rfl
  have hr := BitMachineBinaryDivision.total_run dividend prime [] []
  have hhalt : (((advance BitMachineBinaryDivision.program)^[
      BitMachineBinaryDivision.totalTime dividend prime []])
      (BitMachineBinaryDivision.cfg (some .outer)
        BitMachineBinaryDivision.initial dividend prime [] [] [] [] [])).l = none := by
    change (BitMachineBinaryDivision.run
      (BitMachineBinaryDivision.totalTime dividend prime [])
      (BitMachineBinaryDivision.cfg (some .outer)
        BitMachineBinaryDivision.initial dividend prime [] [] [] [] [])).l = none
    rw [hr]
    rfl
  obtain ⟨n, hn, hglobal⟩ := BitMachineSubroutineRenaming.lift_outputs_renamed
    divisionStacks (Equiv.refl Label) (Equiv.refl Control)
    BitMachineBinaryDivision.program program (some (.inl .start)) hQ
    (none, PrimeSamplerBinaryQuotientAdvance.initial)
    (fun i : Fin 2 => ![scratch,stream] i)
    (BitMachineBinaryDivision.cfg (some .outer)
      BitMachineBinaryDivision.initial dividend prime [] [] [] [] [])
    (BitMachineBinaryDivision.totalTime dividend prime []) hhalt
  refine ⟨n, hn, ?_⟩
  change run n (divisionFrame scratch stream _) =
    divisionFrame scratch stream _ at hglobal
  rw [show ((advance BitMachineBinaryDivision.program)^[
    BitMachineBinaryDivision.totalTime dividend prime []]) _ =
    BitMachineBinaryDivision.run
      (BitMachineBinaryDivision.totalTime dividend prime []) _ from rfl,
      hr] at hglobal
  simpa only [divisionFrame_start, divisionFrame_end] using hglobal

def writerFrame (prime quotient scratch : List Bool)
    (c : TM2.Cfg (fun _ : Fin 2 => Bool)
      PrimeSamplerBinaryDigitFrame.Writer.Label
      PrimeSamplerBinaryDigitFrame.Writer.Control) : Config :=
  renameCfg writerStacks writerLabels writerControl
    (liftCfg (some (.inr (.inl .scan)))
      (BitMachineBinaryDivision.initial,
        PrimeSamplerBinaryQuotientAdvance.initial)
      (fun i : Fin 7 => ![[],prime,quotient,[],[],[],scratch] i) c)

theorem writerFrame_start (prime remainder quotient scratch stream : List Bool) :
    writerFrame prime quotient scratch
      (PrimeSamplerBinaryDigitFrame.Writer.cfg (some .start)
        none remainder stream) =
    cfg (some (.inr (.inl .start))) initial [] prime remainder quotient
      [] [] [] scratch stream := by
  unfold writerFrame cfg bank
  simp only [renameCfg, liftCfg]
  congr 1
  funext k
  fin_cases k <;>
    simp [writerStacks, writerPermutation,
      PrimeSamplerBinaryDigitFrame.Writer.cfg,
      PrimeSamplerBinaryDigitFrame.Writer.bank,
      finSumFinEquiv, Fin.addCases]

theorem writerFrame_end (prime remainder quotient scratch stream : List Bool) :
    writerFrame prime quotient scratch
      (PrimeSamplerBinaryDigitFrame.Writer.cfg none none []
        (PrimeSamplerBinaryDigitFrame.frame remainder stream)) =
    cfg (some (.inr (.inr (.inl .scan)))) initial
      [] prime [] quotient [] [] [] scratch
      (PrimeSamplerBinaryDigitFrame.frame remainder stream) := by
  unfold writerFrame cfg bank
  simp only [renameCfg, liftCfg]
  congr 1
  funext k
  fin_cases k <;>
    simp [writerStacks, writerPermutation,
      PrimeSamplerBinaryDigitFrame.Writer.cfg,
      PrimeSamplerBinaryDigitFrame.Writer.bank,
      finSumFinEquiv, Fin.addCases]

theorem writer_call (prime remainder quotient scratch stream : List Bool) :
    ∃ n ≤ remainder.length + 2,
      run n (cfg (some (.inr (.inl .start))) initial
        [] prime remainder quotient [] [] [] scratch stream) =
      cfg (some (.inr (.inr (.inl .scan)))) initial
        [] prime [] quotient [] [] [] scratch
        (PrimeSamplerBinaryDigitFrame.frame remainder stream) := by
  have hQ : ∀ l, program (writerLabels (.inl l)) =
      renameStmt writerStacks writerLabels writerControl
        (liftStmt (some (.inr (.inl .scan)))
          (PrimeSamplerBinaryDigitFrame.Writer.program l)) := by
    intro l
    rfl
  have hr := PrimeSamplerBinaryDigitFrame.Writer.run_correct remainder stream
  have hhalt : (((advance PrimeSamplerBinaryDigitFrame.Writer.program)^[
      remainder.length + 2])
      (PrimeSamplerBinaryDigitFrame.Writer.cfg (some .start)
        none remainder stream)).l = none := by
    change (PrimeSamplerBinaryDigitFrame.Writer.run (remainder.length + 2)
      (PrimeSamplerBinaryDigitFrame.Writer.cfg (some .start)
        none remainder stream)).l = none
    rw [hr]
    rfl
  obtain ⟨n, hn, hglobal⟩ := BitMachineSubroutineRenaming.lift_outputs_renamed
    writerStacks writerLabels writerControl
    PrimeSamplerBinaryDigitFrame.Writer.program program
    (some (.inr (.inl .scan))) hQ
    (BitMachineBinaryDivision.initial,
      PrimeSamplerBinaryQuotientAdvance.initial)
    (fun i : Fin 7 => ![[],prime,quotient,[],[],[],scratch] i)
    (PrimeSamplerBinaryDigitFrame.Writer.cfg (some .start)
      none remainder stream)
    (remainder.length + 2) hhalt
  refine ⟨n, hn, ?_⟩
  change run n (writerFrame prime quotient scratch _) =
    writerFrame prime quotient scratch _ at hglobal
  rw [show ((advance PrimeSamplerBinaryDigitFrame.Writer.program)^[
    remainder.length + 2]) _ =
    PrimeSamplerBinaryDigitFrame.Writer.run (remainder.length + 2) _ from rfl,
    hr] at hglobal
  simpa only [writerFrame_start, writerFrame_end] using hglobal

def advanceFrame (prime stream : List Bool)
    (c : TM2.Cfg (fun _ : Fin 3 => Bool)
      PrimeSamplerBinaryQuotientAdvance.Label
      PrimeSamplerBinaryQuotientAdvance.Control) : Config :=
  renameCfg advanceStacks advanceLabels advanceControl
    (liftCfg (some (.inr (.inr ())))
      (BitMachineBinaryDivision.initial, none)
      (fun i : Fin 6 => ![prime,[],[],[],[],stream] i) c)

theorem advanceFrame_start (prime quotient stream : List Bool) :
    advanceFrame prime stream
      (PrimeSamplerBinaryQuotientAdvance.cfg (some .scan)
        PrimeSamplerBinaryQuotientAdvance.initial quotient [] []) =
    cfg (some (.inr (.inr (.inl .scan)))) initial
      [] prime [] quotient [] [] [] [] stream := by
  unfold advanceFrame cfg bank
  simp only [renameCfg, liftCfg]
  congr 1
  funext k
  fin_cases k <;>
    simp [advanceStacks, advancePermutation,
      PrimeSamplerBinaryQuotientAdvance.cfg,
      PrimeSamplerBinaryQuotientAdvance.bank,
      finSumFinEquiv, Fin.addCases]

theorem advanceFrame_end (prime quotient stream : List Bool) :
    advanceFrame prime stream
      (PrimeSamplerBinaryQuotientAdvance.cfg none
        ⟨quotient.any id, none⟩ [] []
        (if quotient.any id then quotient.reverse else [])) =
    cfg (some admin)
      (BitMachineBinaryDivision.initial, none, ⟨quotient.any id, none⟩)
      (if quotient.any id then quotient.reverse else [])
      prime [] [] [] [] [] [] stream := by
  unfold advanceFrame cfg bank
  simp only [renameCfg, liftCfg]
  congr 1
  funext k
  fin_cases k <;>
    simp [advanceStacks, advancePermutation,
      PrimeSamplerBinaryQuotientAdvance.cfg,
      PrimeSamplerBinaryQuotientAdvance.bank,
      finSumFinEquiv, Fin.addCases]

theorem advance_call (prime quotient stream : List Bool) :
    ∃ n ≤ 3 * quotient.length + 3,
      run n (cfg (some (.inr (.inr (.inl .scan)))) initial
        [] prime [] quotient [] [] [] [] stream) =
      cfg (some admin)
        (BitMachineBinaryDivision.initial, none, ⟨quotient.any id, none⟩)
        (if quotient.any id then quotient.reverse else [])
        prime [] [] [] [] [] [] stream := by
  have hQ : ∀ l, program (advanceLabels (.inl l)) =
      renameStmt advanceStacks advanceLabels advanceControl
        (liftStmt (some (.inr (.inr ())))
          (PrimeSamplerBinaryQuotientAdvance.program l)) := by
    intro l
    rfl
  have hr := PrimeSamplerBinaryQuotientAdvance.run_correct quotient []
  have hhalt : (((advance PrimeSamplerBinaryQuotientAdvance.program)^[
      3 * quotient.length + 3])
      (PrimeSamplerBinaryQuotientAdvance.cfg (some .scan)
        PrimeSamplerBinaryQuotientAdvance.initial quotient [] [])).l = none := by
    change (PrimeSamplerBinaryQuotientAdvance.run (3 * quotient.length + 3)
      (PrimeSamplerBinaryQuotientAdvance.cfg (some .scan)
        PrimeSamplerBinaryQuotientAdvance.initial quotient [] [])).l = none
    rw [hr]
    rfl
  obtain ⟨n, hn, hglobal⟩ := BitMachineSubroutineRenaming.lift_outputs_renamed
    advanceStacks advanceLabels advanceControl
    PrimeSamplerBinaryQuotientAdvance.program program
    (some (.inr (.inr ()))) hQ
    (BitMachineBinaryDivision.initial, none)
    (fun i : Fin 6 => ![prime,[],[],[],[],stream] i)
    (PrimeSamplerBinaryQuotientAdvance.cfg (some .scan)
      PrimeSamplerBinaryQuotientAdvance.initial quotient [] [])
    (3 * quotient.length + 3) hhalt
  refine ⟨n, hn, ?_⟩
  change run n (advanceFrame prime stream _) =
    advanceFrame prime stream _ at hglobal
  rw [show ((advance PrimeSamplerBinaryQuotientAdvance.program)^[
    3 * quotient.length + 3]) _ =
    PrimeSamplerBinaryQuotientAdvance.run (3 * quotient.length + 3) _ from rfl,
    hr] at hglobal
  simpa only [List.append_nil, advanceFrame_start, advanceFrame_end] using hglobal

private theorem admin_true (prime dividend stream : List Bool) :
    TM2.step program
      (cfg (some admin)
        (BitMachineBinaryDivision.initial, none, ⟨true, none⟩)
        dividend prime [] [] [] [] [] [] stream) =
      some (cfg (some (.inl .outer)) initial
        dividend prime [] [] [] [] [] [] stream) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank, admin, initial]

private theorem admin_false (prime stream : List Bool) :
    TM2.step program
      (cfg (some admin)
        (BitMachineBinaryDivision.initial, none, ⟨false, none⟩)
        [] prime [] [] [] [] [] [] stream) =
      some (cfg none
        (BitMachineBinaryDivision.initial, none, ⟨false, none⟩)
        [] prime [] [] [] [] [] [] stream) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank, admin]

/-- One complete physical division/frame/quotient-test cycle. The `n` bound
charges every executed transition, including the administrative branch. -/
theorem cycle_call (dividend prime stream : List Bool) :
    let r := (BitMachineBinaryDivision.divideFrom dividend prime [] []).1
    let q := (BitMachineBinaryDivision.divideFrom dividend prime [] []).2
    ∃ n ≤ BitMachineBinaryDivision.totalTime dividend prime [] +
        (r.length + 2) + (3 * q.length + 3) + 1,
      run n (cfg (some (.inl .outer)) initial
        dividend prime [] [] [] [] [] [] stream) =
      if q.any id then
        cfg (some (.inl .outer)) initial q.reverse prime
          [] [] [] [] [] [] (PrimeSamplerBinaryDigitFrame.frame r stream)
      else
        cfg none (BitMachineBinaryDivision.initial, none, ⟨false, none⟩)
          [] prime [] [] [] [] [] []
          (PrimeSamplerBinaryDigitFrame.frame r stream) := by
  dsimp
  let r := (BitMachineBinaryDivision.divideFrom dividend prime [] []).1
  let q := (BitMachineBinaryDivision.divideFrom dividend prime [] []).2
  obtain ⟨n₁, hn₁, hd⟩ := division_call dividend prime [] stream
  obtain ⟨n₂, hn₂, hw⟩ := writer_call prime r q [] stream
  obtain ⟨n₃, hn₃, ha⟩ := advance_call prime q
    (PrimeSamplerBinaryDigitFrame.frame r stream)
  have hchain : run (n₁ + n₂ + n₃)
      (cfg (some (.inl .outer)) initial
        dividend prime [] [] [] [] [] [] stream) =
      cfg (some admin)
        (BitMachineBinaryDivision.initial, none, ⟨q.any id, none⟩)
        (if q.any id then q.reverse else []) prime
        [] [] [] [] [] [] (PrimeSamplerBinaryDigitFrame.frame r stream) := by
    exact ((run_add hd n₂).trans hw |> fun h => run_add h n₃).trans ha
  dsimp [r, q] at hn₂ hn₃
  cases hv : q.any id with
  | false =>
      simp only [hv, Bool.false_eq_true, ↓reduceIte] at hchain
      have hstep := admin_false prime (PrimeSamplerBinaryDigitFrame.frame r stream)
      have hfinal := (run_add hchain 1).trans
        (show run 1 _ = _ by simpa [run] using run_step hstep 0)
      refine ⟨n₁ + n₂ + n₃ + 1, ?_, ?_⟩
      · omega
      · simpa [r, q, hv] using hfinal

  | true =>
      simp only [hv, ↓reduceIte] at hchain
      have hstep := admin_true prime q.reverse
        (PrimeSamplerBinaryDigitFrame.frame r stream)
      have hfinal := (run_add hchain 1).trans
        (show run 1 _ = _ by simpa [run] using run_step hstep 0)
      refine ⟨n₁ + n₂ + n₃ + 1, ?_, ?_⟩
      · omega
      · simpa [r, q, hv] using hfinal

def cycleBound (N P : ℕ) : ℕ :=
  (N + 1) * (4 * (N + P + 1) + 5) +
    (N + P + 2) + (3 * N + 3) + 1

theorem cycle_bound (dividend prime : List Bool) (N : ℕ)
    (hN : dividend.length ≤ N) :
    BitMachineBinaryDivision.totalTime dividend prime [] +
      ((BitMachineBinaryDivision.divideFrom dividend prime [] []).1.length + 2) +
      (3 * (BitMachineBinaryDivision.divideFrom dividend prime [] []).2.length + 3) + 1 ≤
      cycleBound N prime.length := by
  have ht := BitMachineBinaryDivision.standard_time_bound dividend prime
  have hr := BitMachineBinaryDivision.divideFrom_remainder_length
    dividend prime [] [] N (by simp; omega) hN
  have hq := BitMachineBinaryDivision.divideFrom_quotient_length
    dividend prime [] []
  simp only [List.length_nil, Nat.add_zero] at hq
  dsimp [cycleBound]
  nlinarith

theorem quotient_value (dividend prime : List Bool)
    (hp : 0 < EncodedCommunication.bitsValue prime) :
    let q := (BitMachineBinaryDivision.divideFrom dividend prime [] []).2
    BitMachineBinaryDivision.msbValue q.reverse =
      BitMachineBinaryDivision.msbValue dividend /
        EncodedCommunication.bitsValue prime := by
  dsimp
  rw [PrimeSamplerBinaryDigit.msbValue_reverse]
  exact (BitMachineBinaryDivision.standard_division_spec dividend prime hp).1

theorem quotient_value_small (dividend prime : List Bool)
    (hp : 2 ≤ EncodedCommunication.bitsValue prime) (n : ℕ)
    (hvalue : BitMachineBinaryDivision.msbValue dividend < 2 ^ (n + 1)) :
    BitMachineBinaryDivision.msbValue
        (BitMachineBinaryDivision.divideFrom dividend prime [] []).2.reverse <
      2 ^ n := by
  rw [quotient_value dividend prime (by omega)]
  apply (Nat.div_lt_iff_lt_mul (by omega)).2
  calc
    BitMachineBinaryDivision.msbValue dividend < 2 ^ (n + 1) := hvalue
    _ = 2 ^ n * 2 := by simp [pow_succ]
    _ ≤ 2 ^ n * EncodedCommunication.bitsValue prime :=
      Nat.mul_le_mul_left _ hp

def streamFuel (prime : List Bool) : ℕ → List Bool → List Bool → List Bool
  | 0, _, stream => stream
  | n + 1, dividend, stream =>
      let result := BitMachineBinaryDivision.divideFrom dividend prime [] []
      let nextStream := PrimeSamplerBinaryDigitFrame.frame result.1 stream
      if result.2.any id then
        streamFuel prime n result.2.reverse nextStream
      else nextStream

/-- Actual nine-bank execution terminates after at most one cycle per bit in
the numerical upper bound. `N` is a separate bound on physical word length:
leading zero bits are allowed and charged rather than silently removed. -/
theorem run_stream_bound (prime : List Bool)
    (hp : 2 ≤ EncodedCommunication.bitsValue prime)
    (N n : ℕ) (dividend stream : List Bool)
    (hlen : dividend.length ≤ N)
    (hvalue : BitMachineBinaryDivision.msbValue dividend < 2 ^ n) :
    ∃ t ≤ (n + 1) * cycleBound N prime.length,
      run t (cfg (some (.inl .outer)) initial
        dividend prime [] [] [] [] [] [] stream) =
      cfg none (BitMachineBinaryDivision.initial, none, ⟨false, none⟩)
        [] prime [] [] [] [] [] []
        (streamFuel prime (n + 1) dividend stream) := by
  induction n generalizing dividend stream with
  | zero =>
      have hz : BitMachineBinaryDivision.msbValue dividend = 0 := by
        simpa using hvalue
      let r := (BitMachineBinaryDivision.divideFrom dividend prime [] []).1
      let q := (BitMachineBinaryDivision.divideFrom dividend prime [] []).2
      have hqv := quotient_value dividend prime (by omega)
      have hqzero : q.any id = false := by
        apply (BitMachineBinaryZeroTest.any_false_iff_value_zero q).2
        change EncodedCommunication.bitsValue
          (BitMachineBinaryDivision.divideFrom dividend prime [] []).2 = 0
        rw [← PrimeSamplerBinaryDigit.msbValue_reverse]
        simpa [q, hz] using hqv
      obtain ⟨t, ht, hr⟩ := cycle_call dividend prime stream
      have hc := cycle_bound dividend prime N hlen
      refine ⟨t, ?_, ?_⟩
      · simpa using ht.trans hc
      · simpa [streamFuel, r, q, hqzero] using hr
  | succ n ih =>
      let r := (BitMachineBinaryDivision.divideFrom dividend prime [] []).1
      let q := (BitMachineBinaryDivision.divideFrom dividend prime [] []).2
      obtain ⟨t, ht, hr⟩ := cycle_call dividend prime stream
      have hc := cycle_bound dividend prime N hlen
      cases hv : q.any id with
      | false =>
          refine ⟨t, ?_, ?_⟩
          · nlinarith
          · simpa [streamFuel, r, q, hv] using hr
      | true =>
          dsimp [q] at hv
          simp only [hv, ↓reduceIte] at hr
          have hlenq : q.reverse.length ≤ N := by
            have hq := BitMachineBinaryDivision.divideFrom_quotient_length
              dividend prime [] []
            simp only [List.length_nil, Nat.add_zero] at hq
            simpa [q] using hq ▸ hlen
          have hvalueq : BitMachineBinaryDivision.msbValue q.reverse <
              2 ^ n := by
            simpa [q] using quotient_value_small dividend prime hp n hvalue
          obtain ⟨u, hu, hrec⟩ := ih q.reverse
            (PrimeSamplerBinaryDigitFrame.frame r stream) hlenq hvalueq
          have hchain := (run_add hr u).trans hrec
          refine ⟨t + u, ?_, ?_⟩
          · nlinarith
          · simpa [streamFuel, r, q, hv] using hchain

theorem run_label_stream (labelBits prime : List Bool)
    (hp : 2 ≤ EncodedCommunication.bitsValue prime) :
    ∃ t ≤ (labelBits.length + 1) * cycleBound labelBits.length prime.length,
      run t (cfg (some (.inl .outer)) initial
        labelBits.reverse prime [] [] [] [] [] [] []) =
      cfg none (BitMachineBinaryDivision.initial, none, ⟨false, none⟩)
        [] prime [] [] [] [] [] []
        (streamFuel prime (labelBits.length + 1) labelBits.reverse []) := by
  apply run_stream_bound prime hp labelBits.length labelBits.length
    labelBits.reverse []
  · simp
  · rw [PrimeSamplerBinaryDigit.msbValue_reverse]
    exact BitMachineBinarySubtract.bitsValue_lt_pow labelBits

def streamWords (prime : List Bool) : ℕ → List Bool → List (List Bool)
  | 0, _ => []
  | n + 1, dividend =>
      let result := BitMachineBinaryDivision.divideFrom dividend prime [] []
      if result.2.any id then streamWords prime n result.2.reverse ++ [result.1]
      else [result.1]

def encodeWords : List (List Bool) → List Bool → List Bool
  | [], tail => tail
  | w :: ws, tail => PrimeSamplerBinaryDigitFrame.frame w (encodeWords ws tail)

theorem encodeWords_append (ws vs : List (List Bool)) (tail : List Bool) :
    encodeWords (ws ++ vs) tail = encodeWords ws (encodeWords vs tail) := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [encodeWords, ih]

theorem streamFuel_eq_encodeWords (prime : List Bool) (n : ℕ)
    (dividend tail : List Bool) :
    streamFuel prime n dividend tail =
      encodeWords (streamWords prime n dividend) tail := by
  induction n generalizing dividend tail with
  | zero => rfl
  | succ n ih =>
      simp only [streamFuel, streamWords]
      cases hq : (BitMachineBinaryDivision.divideFrom dividend prime [] []).2.any id with
      | false => simp [hq, encodeWords]
      | true =>
          simp only [hq, ↓reduceIte]
          rw [ih, encodeWords_append]
          rfl

theorem streamWords_values_pos (prime : List Bool)
    (hp : 2 ≤ EncodedCommunication.bitsValue prime)
    (n : ℕ) (dividend : List Bool)
    (hpos : 0 < BitMachineBinaryDivision.msbValue dividend)
    (hbound : BitMachineBinaryDivision.msbValue dividend < 2 ^ n) :
    (streamWords prime n dividend).map EncodedCommunication.bitsValue =
      PrimeSamplerSignificantDigits.digits
        (EncodedCommunication.bitsValue prime) hp
        (BitMachineBinaryDivision.msbValue dividend) := by
  induction n generalizing dividend with
  | zero => omega
  | succ n ih =>
      let p := EncodedCommunication.bitsValue prime
      let l := BitMachineBinaryDivision.msbValue dividend
      let r := (BitMachineBinaryDivision.divideFrom dividend prime [] []).1
      let q := (BitMachineBinaryDivision.divideFrom dividend prime [] []).2
      have hs := BitMachineBinaryDivision.standard_division_spec dividend prime
        (by omega)
      have hr : EncodedCommunication.bitsValue r = l % p := hs.2
      have hq : BitMachineBinaryDivision.msbValue q.reverse = l / p := by
        rw [PrimeSamplerBinaryDigit.msbValue_reverse]
        exact hs.1
      have hsmall : BitMachineBinaryDivision.msbValue q.reverse < 2 ^ n :=
        quotient_value_small dividend prime hp n hbound
      cases hv : q.any id with
      | false =>
          have hzero : l / p = 0 := by
            rw [← hq, PrimeSamplerBinaryDigit.msbValue_reverse]
            exact (BitMachineBinaryZeroTest.any_false_iff_value_zero q).mp hv
          have hdigit : PrimeSamplerSignificantDigits.digits p hp l =
              PrimeSamplerSignificantDigits.digits p hp (l / p) ++ [l % p] := by
            obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : l ≠ 0)
            rw [hk, PrimeSamplerSignificantDigits.digits_succ]
          change (streamWords prime (n + 1) dividend).map
            EncodedCommunication.bitsValue =
            PrimeSamplerSignificantDigits.digits p hp l
          rw [hdigit]
          simp [streamWords, q, hv, hzero,
            PrimeSamplerSignificantDigits.digits_zero]
          exact hr
      | true =>
          have hqpos : 0 < BitMachineBinaryDivision.msbValue q.reverse := by
            rw [PrimeSamplerBinaryDigit.msbValue_reverse]
            by_contra hnot
            have hzero : EncodedCommunication.bitsValue q = 0 := by omega
            have hfalse := (BitMachineBinaryZeroTest.any_false_iff_value_zero q).2 hzero
            simp [hv] at hfalse
          have hi := ih q.reverse hqpos hsmall
          have hdigit : PrimeSamplerSignificantDigits.digits p hp l =
              PrimeSamplerSignificantDigits.digits p hp (l / p) ++ [l % p] := by
            obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : l ≠ 0)
            rw [hk, PrimeSamplerSignificantDigits.digits_succ]
          change (streamWords prime (n + 1) dividend).map
            EncodedCommunication.bitsValue =
            PrimeSamplerSignificantDigits.digits p hp l
          rw [hdigit]
          simp [streamWords, q, hv, List.map_append, hi, hq]
          exact ⟨rfl, hr⟩

theorem streamWords_values_zero (prime : List Bool)
    (hp : 0 < EncodedCommunication.bitsValue prime)
    (n : ℕ) (dividend : List Bool)
    (hzero : BitMachineBinaryDivision.msbValue dividend = 0) :
    (streamWords prime (n + 1) dividend).map
      EncodedCommunication.bitsValue = [0] := by
  let r := (BitMachineBinaryDivision.divideFrom dividend prime [] []).1
  let q := (BitMachineBinaryDivision.divideFrom dividend prime [] []).2
  have hs := BitMachineBinaryDivision.standard_division_spec dividend prime hp
  have hr : EncodedCommunication.bitsValue r = 0 := by
    simpa [r, hzero] using hs.2
  have hq : q.any id = false := by
    apply (BitMachineBinaryZeroTest.any_false_iff_value_zero q).2
    simpa [q, hzero] using hs.1
  simp [streamWords, q, hq]
  exact hr

/-- The physical stream carries the significant coefficients, with one
explicit zero coefficient in the zero-label case. The latter is harmless to
Horner evaluation and costs one complete, charged division cycle. -/
theorem label_stream_values (labelBits prime : List Bool)
    (hp : 2 ≤ EncodedCommunication.bitsValue prime) :
    let words := streamWords prime (labelBits.length + 1) labelBits.reverse
    words.map EncodedCommunication.bitsValue =
      if EncodedCommunication.bitsValue labelBits = 0 then [0]
      else PrimeSamplerSignificantDigits.digits
        (EncodedCommunication.bitsValue prime) hp
        (EncodedCommunication.bitsValue labelBits) := by
  dsimp
  have hv : BitMachineBinaryDivision.msbValue labelBits.reverse =
      EncodedCommunication.bitsValue labelBits :=
    PrimeSamplerBinaryDigit.msbValue_reverse labelBits
  cases hz : EncodedCommunication.bitsValue labelBits with
  | zero =>
      simp only [hz, ↓reduceIte]
      exact streamWords_values_zero prime (by omega) labelBits.length
        labelBits.reverse (by simpa [hv] using hz)
  | succ v =>
      simp only [Nat.succ_ne_zero, ↓reduceIte]
      have hb : BitMachineBinaryDivision.msbValue labelBits.reverse <
          2 ^ (labelBits.length + 1) := by
        rw [hv]
        have h := BitMachineBinarySubtract.bitsValue_lt_pow labelBits
        exact lt_trans h (pow_lt_pow_right₀ (by omega : 1 < (2 : ℕ))
          (by omega : labelBits.length < labelBits.length + 1))
      simpa only [hv, hz] using streamWords_values_pos prime hp
        (labelBits.length + 1) labelBits.reverse (by omega) hb

theorem label_stream_physical_and_values (labelBits prime : List Bool)
    (hp : 2 ≤ EncodedCommunication.bitsValue prime) :
    let words := streamWords prime (labelBits.length + 1) labelBits.reverse
    ∃ t ≤ (labelBits.length + 1) * cycleBound labelBits.length prime.length,
      run t (cfg (some (.inl .outer)) initial
        labelBits.reverse prime [] [] [] [] [] [] []) =
        cfg none (BitMachineBinaryDivision.initial, none, ⟨false, none⟩)
          [] prime [] [] [] [] [] [] (encodeWords words []) ∧
      words.map EncodedCommunication.bitsValue =
        if EncodedCommunication.bitsValue labelBits = 0 then [0]
        else PrimeSamplerSignificantDigits.digits
          (EncodedCommunication.bitsValue prime) hp
          (EncodedCommunication.bitsValue labelBits) := by
  dsimp
  obtain ⟨t, ht, hr⟩ := run_label_stream labelBits prime hp
  refine ⟨t, ht, ?_, label_stream_values labelBits prime hp⟩
  simpa only [streamFuel_eq_encodeWords] using hr

theorem streamWords_word_length (prime : List Bool) (n N : ℕ)
    (dividend : List Bool) (hlen : dividend.length ≤ N) :
    ∀ w ∈ streamWords prime n dividend, w.length ≤ N + prime.length := by
  induction n generalizing dividend with
  | zero => simp [streamWords]
  | succ n ih =>
      let r := (BitMachineBinaryDivision.divideFrom dividend prime [] []).1
      let q := (BitMachineBinaryDivision.divideFrom dividend prime [] []).2
      have hrem : r.length ≤ N + prime.length :=
        BitMachineBinaryDivision.divideFrom_remainder_length
          dividend prime [] [] N (by simp; omega) hlen
      have hquot : q.reverse.length ≤ N := by
        have h := BitMachineBinaryDivision.divideFrom_quotient_length
          dividend prime [] []
        simpa [q] using h ▸ hlen
      intro w hw
      cases hv : q.any id with
      | false =>
          have : w = r := by simpa [streamWords, q, hv] using hw
          simpa [this] using hrem
      | true =>
          have hmem : w ∈ streamWords prime n q.reverse ∨ w = r := by
            simpa [streamWords, q, hv] using hw
          rcases hmem with hrec | heq
          · exact ih q.reverse hquot w hrec
          · simpa [heq] using hrem

theorem label_stream_word_length (labelBits prime : List Bool) :
    ∀ w ∈ streamWords prime (labelBits.length + 1) labelBits.reverse,
      w.length ≤ labelBits.length + prime.length :=
  streamWords_word_length prime (labelBits.length + 1) labelBits.length
    labelBits.reverse (by simp)

theorem streamWords_length_le_fuel (prime : List Bool) (n : ℕ)
    (dividend : List Bool) : (streamWords prime n dividend).length ≤ n := by
  induction n generalizing dividend with
  | zero => simp [streamWords]
  | succ n ih =>
      simp only [streamWords]
      split
      · simp only [List.length_append, List.length_singleton]
        exact Nat.add_le_add_right (ih _) 1
      · simp


end EthInapproximability.CurrentPaper.PrimeSamplerBinaryDigitStream
