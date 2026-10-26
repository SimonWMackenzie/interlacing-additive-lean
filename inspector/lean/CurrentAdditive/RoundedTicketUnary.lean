import CurrentAdditive.RoundedMachine
import EthInapproximability.CurrentPaper.ProtocolBoundedUnary
import Paper2.RecursiveLabelCodec
import Mathlib.Tactic

/-! Private continuation: physically convert one rounded binary index to the
    existing unary `finCodec` word without rejection or fallback. -/

namespace EthInapproximability.CurrentPaper.RoundedTicketUnary

open Turing Turing.TM2.Stmt BitMachineEncoding
open EncodedCommunication (bitsValue)

abbrev Stack := RoundedMachine.Stack ⊕ Fin 3

inductive Label where
  | rounded (l : RoundedMachine.Label)
  | unary (l : ProtocolBoundedUnary.Label)
  | dropFlag
  deriving DecidableEq, Fintype

abbrev Control := RoundedMachine.Control × (ProtocolBoundedUnary.Control × Option Bool)
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def roundedEmbed : RoundedMachine.Stack ↪ Stack :=
  ⟨Sum.inl, by intro x y h; exact Sum.inl_injective h⟩

def unarySlot : Fin 4 → Stack
  | 0 => .inl (.inl (.inl 0))
  | 1 => .inr 0
  | 2 => .inr 1
  | _ => .inr 2

private theorem unarySlot_injective : Function.Injective unarySlot := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [unarySlot] at h ⊢

def unaryEmbed : Fin 4 ↪ Stack := ⟨unarySlot, unarySlot_injective⟩

def initial : Control := (RoundedMachine.initial, ((none, false), none))

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .rounded l =>
      BitMachineStackEmbedding.stmt roundedEmbed Label.rounded
        (fun v => (v, ((none, false), none))) Prod.fst
        (some (.unary .zeroScan)) (RoundedMachine.program l)
  | .unary l =>
      BitMachineStackEmbedding.stmt unaryEmbed Label.unary
        (fun u => (RoundedMachine.initial, (u, none))) (fun s => s.2.1)
        (some .dropFlag) (ProtocolBoundedUnary.program l)
  | .dropFlag =>
      pop (.inr 2) (fun s bit => (s.1, (s.2.1, bit))) halt

def run (n : ℕ) (c : Config) : Config := ((advance program)^[n]) c

private theorem run_add {c d : Config} {m : ℕ} (h : run m c = d) (n : ℕ) :
    run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

def rightBank (cap work out : List Bool) : Fin 3 → List Bool :=
  fun i => if i = 0 then cap else if i = 1 then work else out

def bank (left : RoundedMachine.Stack → List Bool)
    (cap work out : List Bool) : Stack → List Bool :=
  Sum.elim left (rightBank cap work out)

def cfg (l : Option Label) (v : Control)
    (left : RoundedMachine.Stack → List Bool) (cap work out : List Bool) : Config :=
  ⟨l, v, bank left cap work out⟩

def start (source word suffix : List Bool) (a : ℕ) : Config :=
  cfg (some (.rounded .load)) initial
    (RoundedMachine.cfg (some .load) RoundedMachine.initial
      (RoundedMachine.mulStart source [])
      (List.replicate word.length true) (word ++ suffix) []).stk
    (List.replicate a true) [] [false]

private theorem embedded_rounded_bank
    (before after : RoundedMachine.Stack → List Bool)
    (cap work out : List Bool) :
    BitMachineStackEmbedding.bank roundedEmbed (bank before cap work out) after =
      bank after cap work out := by
  funext k
  rcases k with k | k
  · exact BitMachineStackEmbedding.bank_at roundedEmbed
      (bank before cap work out) after k
  · have h : ¬ ∃ j : RoundedMachine.Stack, roundedEmbed j = Sum.inr k := by
      intro ⟨j, hj⟩
      cases hj
    rw [BitMachineStackEmbedding.bank_outside roundedEmbed
      (bank before cap work out) after (.inr k) h]
    rfl

theorem rounded_run (source word suffix : List Bool) (a : ℕ) :
    ∃ t ≤ RoundedMachine.clock source word,
      run t (start source word suffix a) =
        cfg (some (.unary .zeroScan)) initial
          (RoundedMachine.cfg none RoundedMachine.initial
            (RoundedMachine.productBank source
              (RoundedMachine.outputWord source word)) [] suffix []).stk
          (List.replicate a true) [] [false] := by
  let localStart := RoundedMachine.cfg (some .load) RoundedMachine.initial
    (RoundedMachine.mulStart source [])
    (List.replicate word.length true) (word ++ suffix) []
  let foreign := bank localStart.stk (List.replicate a true) [] [false]
  obtain ⟨t, ht, hr⟩ := RoundedMachine.physical_run source word suffix
  have hhalt : (((advance RoundedMachine.program)^[t]) localStart).l = none := by
    change (RoundedMachine.run t localStart).l = none
    rw [hr]
    rfl
  obtain ⟨u, hu, hrun⟩ := BitMachineStackEmbedding.outputs roundedEmbed foreign
    Label.rounded (fun v => (v, ((none, false), none))) Prod.fst (by intro v; rfl)
    (some (.unary .zeroScan)) RoundedMachine.program program
    (by intro l; rfl) localStart t hhalt
  refine ⟨u, hu.trans ht, ?_⟩
  change (((advance RoundedMachine.program)^[t]) localStart) = _ at hr
  rw [hr] at hrun
  simpa [run, start, cfg, localStart, foreign,
    BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg, embedded_rounded_bank] using hrun

private theorem embedded_unary_start (left : RoundedMachine.Stack → List Bool)
    (q cap : List Bool) (hleft : left (.inl (.inl 0)) = q) :
    BitMachineStackEmbedding.bank unaryEmbed (bank left cap [] [false])
      (ProtocolBoundedUnary.cfg (some .zeroScan) (none, false)
        q cap [] [false]).stk = bank left cap [] [false] := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro k
  fin_cases k <;>
    simp [ProtocolBoundedUnary.cfg, ProtocolBoundedUnary.stackContents,
      unaryEmbed, unarySlot, bank, rightBank, hleft]

theorem unary_run (left : RoundedMachine.Stack → List Bool)
    (q cap : List Bool) (hleft : left (.inl (.inl 0)) = q) :
    ∃ u ≤ (cap.length + 1) * (4 * q.length + 5), ∃ c,
      run u (cfg (some (.unary .zeroScan)) initial left cap [] [false]) =
        BitMachineStackEmbedding.cfg unaryEmbed (bank left cap [] [false])
          Label.unary (fun v => (RoundedMachine.initial, (v, none)))
          (some .dropFlag) c ∧
      c.l = none ∧ c.stk 3 = ProtocolBoundedUnary.result q cap [false] := by
  obtain ⟨t, c, ht, hc, hl, ho, _, _, _⟩ :=
    ProtocolBoundedUnary.bounded_run_framed q cap [false]
  let localStart := ProtocolBoundedUnary.cfg (some .zeroScan) (none, false)
    q cap [] [false]
  let foreign := bank left cap [] [false]
  have hhalt : (((advance ProtocolBoundedUnary.program)^[t]) localStart).l = none := by
    change (ProtocolBoundedUnary.run t localStart).l = none
    rw [hc]
    exact hl
  obtain ⟨u, hu, hrun⟩ := BitMachineStackEmbedding.outputs unaryEmbed foreign
    Label.unary (fun v => (RoundedMachine.initial, (v, none))) (fun s => s.2.1)
    (by intro v; rfl) (some .dropFlag) ProtocolBoundedUnary.program program
    (by intro l; rfl) localStart t hhalt
  refine ⟨u, hu.trans ht, c, ?_, hl, ho⟩
  change (((advance ProtocolBoundedUnary.program)^[t]) localStart) = c at hc
  rw [hc] at hrun
  simpa [run, cfg, localStart, foreign, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    embedded_unary_start left q cap hleft] using hrun

private theorem step_dropFlag (s : Control) (B : Stack → List Bool)
    (tail : List Bool)
    (hout : B (.inr 2) = true :: tail) :
    advance program ⟨some .dropFlag, s, B⟩ =
      ⟨none, (s.1, (s.2.1, some true)), Function.update B (.inr 2) tail⟩ := by
  simp [advance, TM2.step, TM2.stepAux, program, hout]

theorem unary_fin_run (left : RoundedMachine.Stack → List Bool)
    (q cap : List Bool) (hleft : left (.inl (.inl 0)) = q)
    (hlegal : bitsValue q < cap.length) :
    ∃ u c, u ≤ (cap.length + 1) * (4 * q.length + 5) + 1 ∧
      run u (cfg (some (.unary .zeroScan)) initial left cap [] [false]) = c ∧
      c.l = none ∧
      c.stk (.inr 2) = List.replicate (bitsValue q) true ++ [false] ∧
      c.stk (.inl (.inr 1)) = left (.inr 1) := by
  obtain ⟨u, hu, c, hrun, hl, ho⟩ := unary_run left q cap hleft
  let foreign := bank left cap [] [false]
  let D : Config := BitMachineStackEmbedding.cfg unaryEmbed foreign Label.unary
    (fun v => (RoundedMachine.initial, (v, none))) (some .dropFlag) c
  have hlabel : D.l = some .dropFlag := by
    simp [D, BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg, hl]
  have hout : D.stk (.inr 2) =
      true :: (List.replicate (bitsValue q) true ++ [false]) := by
    have he : D.stk (.inr 2) = c.stk 3 := by
      exact BitMachineStackEmbedding.bank_at unaryEmbed foreign c.stk 3
    rw [he, ho]
    simp [ProtocolBoundedUnary.result, Nat.le_of_lt hlegal]
  have htape : D.stk (.inl (.inr 1)) = left (.inr 1) := by
    have hi : ¬ ∃ j : Fin 4, unaryEmbed j = (.inl (.inr 1) : Stack) := by
      intro ⟨j, hj⟩
      fin_cases j <;> simp [unaryEmbed, unarySlot] at hj
    exact BitMachineStackEmbedding.bank_outside unaryEmbed foreign c.stk
      (.inl (.inr 1)) hi
  let E : Config := ⟨none, (D.var.1, (D.var.2.1, some true)),
    Function.update D.stk (.inr 2)
      (List.replicate (bitsValue q) true ++ [false])⟩
  have hstep : advance program D = E := by
    rcases D with ⟨l, s, B⟩
    simp only at hlabel hout ⊢
    cases l with
    | none => contradiction
    | some l =>
        cases l with
        | dropFlag => simpa [E] using step_dropFlag s B _ hout
        | rounded l => cases hlabel
        | unary l => cases hlabel
  refine ⟨u + 1, E, by omega, ?_, rfl, ?_, ?_⟩
  · have h := run_add hrun 1
    change run (u + 1) _ = run 1 D at h
    simpa only [run, Function.iterate_one, hstep] using h
  · simp [E]
  · simpa [E, Function.update_of_ne] using htape

theorem physical_unary (source word suffix : List Bool)
    (ha : 0 < bitsValue source) :
    ∃ t c,
      t ≤ RoundedMachine.clock source word +
        (bitsValue source + 1) *
          (4 * (RoundedMachine.outputWord source word).length + 5) + 1 ∧
      run t (start source word suffix (bitsValue source)) = c ∧
      c.l = none ∧
      c.stk (.inr 2) =
        List.replicate (bitsValue (RoundedMachine.outputWord source word)) true ++
          [false] ∧
      c.stk (.inl (.inr 1)) = suffix := by
  let q := RoundedMachine.outputWord source word
  let left := (RoundedMachine.cfg none RoundedMachine.initial
    (RoundedMachine.productBank source q) [] suffix []).stk
  have hleft : left (.inl (.inl 0)) = q := by
    rfl
  have hlegal : bitsValue q < (List.replicate (bitsValue source) true).length := by
    simpa [q] using RoundedMachine.output_legal source word ha
  obtain ⟨u, c, hu, hrunU, hl, hout, htape⟩ :=
    unary_fin_run left q (List.replicate (bitsValue source) true) hleft hlegal
  obtain ⟨t, ht, hrunR⟩ := rounded_run source word suffix (bitsValue source)
  refine ⟨t + u, c, ?_, ?_, hl, hout, ?_⟩
  · simpa using Nat.add_le_add ht hu
  · exact (run_add hrunR u).trans hrunU
  · simpa [left, RoundedMachine.cfg, RoundedMachine.bank,
      RoundedMachine.rightBank] using htape

theorem outputWord_length_bound (source word : List Bool) :
    (RoundedMachine.outputWord source word).length ≤
      source.length + 2 * word.length := by
  have hm := BitMachineBinaryMultiply.multiplyFrom_length_bound [] source word.reverse
  have hp : (BitMachineBinaryMultiply.multiplyFrom [] source word.reverse).length ≤
      source.length + 2 * word.length := by
    have := le_trans (le_max_left _ _) hm
    simpa only [List.length_reverse, List.length_nil, max_eq_right (Nat.zero_le _)] using this
  apply le_trans ?_ hp
  simp only [RoundedMachine.outputWord, List.length_drop]
  exact Nat.sub_le _ _

theorem physical_unary_polynomial_clock (source word suffix : List Bool)
    (ha : 0 < bitsValue source) :
    ∃ t c,
      t ≤ 100 * (source.length + word.length + 2) ^ 2 +
        (bitsValue source + 1) *
          (4 * (source.length + 2 * word.length) + 5) + 1 ∧
      run t (start source word suffix (bitsValue source)) = c ∧
      c.l = none ∧
      c.stk (.inr 2) =
        List.replicate (bitsValue (RoundedMachine.outputWord source word)) true ++
          [false] ∧
      c.stk (.inl (.inr 1)) = suffix := by
  obtain ⟨t, c, ht, hr, hl, ho, hs⟩ := physical_unary source word suffix ha
  refine ⟨t, c, ?_, hr, hl, ho, hs⟩
  have hround := RoundedMachine.clock_quadratic source word
  have hword := outputWord_length_bound source word
  nlinarith

end EthInapproximability.CurrentPaper.RoundedTicketUnary
