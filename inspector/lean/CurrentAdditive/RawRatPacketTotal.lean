import CurrentAdditive.RawRatPacketCoreBridge
import CurrentAdditive.RawRatCoreClock
import Mathlib.Tactic

set_option maxRecDepth 4096

namespace CurrentAdditive.RawRatPacketTotal

open Turing
open EthInapproximability.CurrentPaper
open BitMachineEncoding
open CurrentAdditive.CodeDCodec
open CurrentAdditive.RawRatPacketWrapper

abbrev P := RawRatCoreController.program
local notation "coreStart" =>
  BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))))
abbrev initial := RawRatPacketCoreBridge.coreInitial

def rawOfBank (B : BitMachineBankCodec.Bank 3) : RawRat :=
  ⟨B 0 = [true], B 1, B 2⟩

theorem raw_bank_eq (B : BitMachineBankCodec.Bank 3)
    (h : B 0 = [] ∨ B 0 = [true]) : rawRatBank (rawOfBank B) = B := by
  funext i
  fin_cases i <;> simp [rawRatBank, rawOfBank] at *
  rcases h with h | h <;> simp [h]

noncomputable def outputBank (B : BitMachineBankCodec.Bank 3) : List Bool :=
  BitMachineBankSerialize.encode
    (List.ofFn (selected (RawRatCoreController.result (rawOfBank B))))

noncomputable def result (input : List Bool) : List Bool :=
  match BitMachineBankCodec.decode 3 input with
  | none => []
  | some B => if B 0 = [] ∨ B 0 = [true] then outputBank B else []

theorem canonical_result (r : RawRat) (hr : r.Valid) :
    result (encodeRawRat r) =
      encodeRawRat (CodeDCanonicalSource.rawOfRat r.value) := by
  have hd : BitMachineBankCodec.decode 3 (encodeRawRat r) =
      some (rawRatBank r) := by simp [encodeRawRat]
  have hs : rawRatBank r 0 = [] ∨ rawRatBank r 0 = [true] := by
    cases r.negative <;> simp [rawRatBank]
  have he : rawOfBank (rawRatBank r) = r := by
    cases r with
    | mk s n d => cases s <;> simp [rawOfBank, rawRatBank]
  simp only [result, hd, hs, outputBank, he]
  exact RawRatPacketCoreBridge.encoded_eq r hr

theorem packed_run_bank (input : List Bool)
    (B : BitMachineBankCodec.Bank 3)
    (hd : BitMachineBankCodec.decode 3 input = some B)
    (hs : B 0 = [] ∨ B 0 = [true]) :
    ∃ t ≤ 7*(input.length+1)+2+
        RawRatCoreController.clock (rawOfBank B)+
        2*(outputBank B).length+4,
      let c := run P coreStart initial t
        (cfg (some (.inl (.scan 0))) (initial,none)
          (fun _ => []) input [] [])
      c.l = none ∧ c.stk (.inr 2) = outputBank B := by
  let r := rawOfBank B
  have hB : rawRatBank r = B := raw_bank_eq B hs
  obtain ⟨q,hq,hv⟩ := RawRatPacketValidate.sign_valid P coreStart initial r
  obtain ⟨t,v,ht,hcore⟩ := RawRatCoreController.run r
  have hcore' : ((advance P)^[t])
      (⟨some coreStart, initial, inputBank B⟩ :
        TM2.Cfg (fun _ : Fin 13 => Bool) _ _) =
      ⟨none,(RawRatCoreController.firstInitial,
        (((((), none), none), (BitMachineBinaryDivision.initial, none)),
          (none,v))),RawRatCoreController.result r⟩ := by
    simpa only [P, initial, ← hB, RawRatPacketCoreBridge.input_eq] using hcore
  obtain ⟨u,hu,hres⟩ := RawRatPacketWrapper.packed_run
    P coreStart initial input B (RawRatCoreController.result r)
    (RawRatCoreController.firstInitial,
      (((((), none), none), (BitMachineBinaryDivision.initial, none)),
        (none,v))) t q hd (by simpa only [← hB] using hv) hcore'
  refine ⟨u, ?_, ?_⟩
  · change u ≤ 7*(input.length+1)+q+t+2*(outputBank B).length+4 at hu
    change t ≤ RawRatCoreController.clock (rawOfBank B) at ht
    omega
  · simpa only [outputBank] using hres

theorem malformed_sign_run (input : List Bool)
    (B : BitMachineBankCodec.Bank 3)
    (hd : BitMachineBankCodec.decode 3 input = some B)
    (hs : ¬ (B 0 = [] ∨ B 0 = [true])) :
    ∃ t ≤ 7*(input.length+1)+3,
      let c := run P coreStart initial t
        (cfg (some (.inl (.scan 0))) (initial,none)
          (fun _ => []) input [] [])
      c.l = none ∧ c.stk (.inr 2) = [] := by
  obtain ⟨a,ha,hparse⟩ := RawRatPacketWrapper.parse_run
    P coreStart initial input B hd
  have hparsed : run P coreStart initial 1
      (cfg (some (.inr (.inr (.inr .parsed)))) (initial,some true)
        (inputBank B) [] [] []) =
      cfg (some (.inr (.inr (.inr .signFirst)))) (initial,some true)
        (inputBank B) [] [] [] := by
    simpa [run] using RawRatPacketWrapper.parsed_step
      P coreStart initial (inputBank B)
  cases hw : B 0 with
  | nil => exact False.elim (hs (Or.inl hw))
  | cons b w =>
      cases b with
      | false =>
          have hS : inputBank B 0 = false :: w := by
            simpa [inputBank] using hw
          have hr := RawRatPacketValidate.sign_false_reject
            P coreStart initial (inputBank B) (initial,some true) w hS
          refine ⟨a+2, by omega, ?_⟩
          dsimp only
          rw [show a+2 = a+1+1 by omega, run_add, run_add, hparse, hparsed]
          simpa only [run, Function.iterate_one] using hr
      | true =>
          cases w with
          | nil => exact False.elim (hs (Or.inr hw))
          | cons b w =>
              have hS : inputBank B 0 = true :: b :: w := by
                simpa [inputBank] using hw
              have hfirst := RawRatPacketValidate.sign_true_head
                P coreStart initial (inputBank B) (initial,some true) (b::w) hS
              have hlast := RawRatPacketValidate.sign_long_reject
                P coreStart initial (inputBank B) (initial,some true) b w hS
              refine ⟨a+3, by omega, ?_⟩
              dsimp only
              rw [show a+3 = a+1+1+1 by omega,
                run_add, run_add, run_add, hparse, hparsed]
              have hstep : run P coreStart initial 1
                  (cfg (some (.inr (.inr (.inr .signFirst)))) (initial,some true)
                    (inputBank B) [] [] []) =
                  cfg (some (.inr (.inr (.inr .signTail))))
                    (initial,some true) (inputBank B) [] [] [] := by
                simpa only [run, Function.iterate_one] using hfirst
              rw [hstep]
              simpa only [run, Function.iterate_one] using hlast

def growthCoefficient : Nat :=
  26 * BitMachineStackGrowth.perStep P

def polynomialCoefficient : Nat :=
  33 + (1 + 2*growthCoefficient) * RawRatCoreClock.polynomialCoefficient

theorem output_size (input : List Bool) (B : BitMachineBankCodec.Bank 3)
    (hd : BitMachineBankCodec.decode 3 input = some B)
    (hs : B 0 = [] ∨ B 0 = [true]) :
    (outputBank B).length ≤ input.length + 10 +
      growthCoefficient * RawRatCoreController.clock (rawOfBank B) := by
  let r := rawOfBank B
  have hB : rawRatBank r = B := raw_bank_eq B hs
  have hi : RawRatCoreClock.inputLength r = input.length := by
    simp [RawRatCoreClock.inputLength, encodeRawRat, hB,
      BitMachineBankCodec.encode_decode hd]
  have hsel := RawRatPacketWrapper.selected_length_le
    (RawRatCoreController.result r)
  have hg := RawRatCoreClock.core_output_encoded_growth r
  change (outputBank B).length ≤
    (BitMachineBankCodec.encode (RawRatCoreController.result r)).length at hsel
  rw [hi] at hg
  change (BitMachineBankCodec.encode (RawRatCoreController.result r)).length ≤
    input.length+10+growthCoefficient*RawRatCoreController.clock r at hg
  change (outputBank B).length ≤ input.length+10+
    growthCoefficient*RawRatCoreController.clock r
  omega

theorem packed_polynomial (input : List Bool) (B : BitMachineBankCodec.Bank 3)
    (hd : BitMachineBankCodec.decode 3 input = some B)
    (hs : B 0 = [] ∨ B 0 = [true]) :
    ∃ t ≤ polynomialCoefficient * (input.length+1)^5,
      let c := run P coreStart initial t
        (cfg (some (.inl (.scan 0))) (initial,none)
          (fun _ => []) input [] [])
      c.l = none ∧ c.stk (.inr 2) = outputBank B := by
  obtain ⟨t,ht,hr⟩ := packed_run_bank input B hd hs
  have hsize := output_size input B hd hs
  let r := rawOfBank B
  have hB : rawRatBank r = B := raw_bank_eq B hs
  have hi : RawRatCoreClock.inputLength r = input.length := by
    simp [RawRatCoreClock.inputLength, encodeRawRat, hB,
      BitMachineBankCodec.encode_decode hd]
  have hc := RawRatCoreClock.core_clock_polynomial r
  rw [hi] at hc
  have hn : input.length+1 ≤ (input.length+1)^5 := by
    exact Nat.le_self_pow (n := 5) (by decide) (input.length+1)
  refine ⟨t, ?_, hr⟩
  change t ≤ 7*(input.length+1)+2+RawRatCoreController.clock r+
    2*(outputBank B).length+4 at ht
  change (outputBank B).length ≤ input.length+10+
    growthCoefficient*RawRatCoreController.clock r at hsize
  have hm := Nat.mul_le_mul_left (1+2*growthCoefficient) hc
  have h33 := Nat.mul_le_mul_left 33 hn
  calc
    t ≤ 9*(input.length+1)+24+
        (1+2*growthCoefficient)*RawRatCoreController.clock r := by
          nlinarith [ht, hsize]
    _ ≤ 33*(input.length+1)^5+
        (1+2*growthCoefficient)*
          (RawRatCoreClock.polynomialCoefficient*(input.length+1)^5) := by omega
    _ = polynomialCoefficient*(input.length+1)^5 := by
      unfold polynomialCoefficient
      ring

noncomputable def machine : BitMachine.Machine :=
  ofFinite (.inr 0) (.inr 2) (.inl (.scan 0))
    (initial,none) (RawRatPacketWrapper.program P coreStart initial)

theorem initial_cfg {L V : Type*}
    (_Q : L → TM2.Stmt (fun _ : Fin 13 => Bool) L V)
    (v : V) (input : List Bool) :
    rawInit (.inr (0 : Fin 3) : Stack)
      (.inl (.scan 0) : Label L) (v,none) input =
    cfg (some (.inl (.scan 0))) (v,none)
      (fun _ => []) input [] [] := by
  simp only [rawInit, cfg, contents]
  congr 1
  funext j
  cases j with
  | inl j => rfl
  | inr j => fin_cases j <;> rfl

theorem outputsWithin (input : List Bool) :
    machine.OutputsWithin input (result input)
      (polynomialCoefficient * (input.length+1)^5) := by
  cases hd : BitMachineBankCodec.decode 3 input with
  | none =>
      obtain ⟨t,ht,hr⟩ := RawRatPacketValidate.framing_reject
        P coreStart initial input hd
      have hb : t ≤ polynomialCoefficient*(input.length+1)^5 := by
        have hn : input.length+1 ≤ (input.length+1)^5 := by
          exact Nat.le_self_pow (n := 5) (by decide) (input.length+1)
        calc
          t ≤ 33*(input.length+1) := by omega
          _ ≤ 33*(input.length+1)^5 := Nat.mul_le_mul_left 33 hn
          _ ≤ polynomialCoefficient*(input.length+1)^5 := by
            apply Nat.mul_le_mul_right
            unfold polynomialCoefficient
            omega
      apply outputsWithin_of_raw_run (.inr 0) (.inr 2) (.inl (.scan 0))
        (initial,none) (RawRatPacketWrapper.program P coreStart initial)
        input (result input) t _ hb
      · change (run P coreStart initial t _).l = none
        rw [initial_cfg P initial input]
        exact hr.1
      · change (run P coreStart initial t _).stk (.inr 2) = result input
        rw [initial_cfg P initial input]
        simpa only [result, hd] using hr.2
  | some B =>
      by_cases hs : B 0 = [] ∨ B 0 = [true]
      · obtain ⟨t,ht,hr⟩ := packed_polynomial input B hd hs
        apply outputsWithin_of_raw_run (.inr 0) (.inr 2) (.inl (.scan 0))
          (initial,none) (RawRatPacketWrapper.program P coreStart initial)
          input (result input) t _ ht
        · change (run P coreStart initial t _).l = none
          rw [initial_cfg P initial input]
          exact hr.1
        · change (run P coreStart initial t _).stk (.inr 2) = result input
          rw [initial_cfg P initial input]
          simpa only [result, hd, hs, dite_true] using hr.2
      · obtain ⟨t,ht,hr⟩ := malformed_sign_run input B hd hs
        have hb : t ≤ polynomialCoefficient*(input.length+1)^5 := by
          have hn : input.length+1 ≤ (input.length+1)^5 := by
            exact Nat.le_self_pow (n := 5) (by decide) (input.length+1)
          calc
            t ≤ 33*(input.length+1) := by omega
            _ ≤ 33*(input.length+1)^5 := Nat.mul_le_mul_left 33 hn
            _ ≤ polynomialCoefficient*(input.length+1)^5 := by
              apply Nat.mul_le_mul_right
              unfold polynomialCoefficient
              omega
        apply outputsWithin_of_raw_run (.inr 0) (.inr 2) (.inl (.scan 0))
          (initial,none) (RawRatPacketWrapper.program P coreStart initial)
          input (result input) t _ hb
        · change (run P coreStart initial t _).l = none
          rw [initial_cfg P initial input]
          exact hr.1
        · change (run P coreStart initial t _).stk (.inr 2) = result input
          rw [initial_cfg P initial input]
          simpa only [result, hd, hs, dite_false] using hr.2

theorem polytime : BitMachine.Polytime result :=
  ⟨machine, polynomialCoefficient, 5, outputsWithin⟩

end CurrentAdditive.RawRatPacketTotal
