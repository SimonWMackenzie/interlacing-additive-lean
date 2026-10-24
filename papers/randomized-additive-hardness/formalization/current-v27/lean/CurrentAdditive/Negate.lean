import CurrentAdditive.GaussPacket
import EthInapproximability.CurrentPaper.BitMachineBankWrapper

/-! A literal two-step TM2 sign change for canonical rational packets. -/

namespace CurrentAdditive.GaussCertificateNegate

open Turing TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineBankCodec
open EthInapproximability.CurrentPaper.BitMachineEncoding

inductive Label where
  | inspect | toggle
  deriving DecidableEq, Fintype

abbrev Control := Bool × Option Bool

def transformed (S : Bank 3) : Bank 3 :=
  fun i =>
    if i = 0 then
      if (S 1).isEmpty then S 0 else
        if (S 0).isEmpty then [true] else (S 0).tail
    else S i

def program : Label → TM2.Stmt (fun _ : Fin 3 => Bool) Label Control
  | .inspect =>
      peek 1 (fun _ b => (b.isSome, none))
        (branch Prod.fst (goto fun _ => .toggle) halt)
  | .toggle =>
      pop 0 (fun v b => (v.1, b))
        (branch (fun v => v.2.isSome) halt
          (push 0 (fun _ => true) halt))

def result (input : List Bool) : List Bool :=
  BitMachineBankWrapper.result transformed input

noncomputable def machine : BitMachine.Machine :=
  BitMachineBankWrapper.machine program .inspect (false, none)

theorem local_run (S : Bank 3) :
    ∃ (t : Nat) (v : Control), t ≤ 2 ∧
        ((advance program)^[t])
          (⟨some .inspect, (false, none), S⟩ :
            TM2.Cfg (fun _ : Fin 3 => Bool) Label Control) =
          ⟨none, v, transformed S⟩ := by
  cases hnum : S 1 with
  | nil =>
      refine ⟨1, (false, none), by omega, ?_⟩
      simp only [Function.iterate_one]
      simp [advance, program, hnum, TM2.step, TM2.stepAux]
      funext i
      fin_cases i <;> simp [transformed, hnum]
  | cons b bs =>
      cases hsign : S 0 with
      | nil =>
          refine ⟨2, (true, none), by omega, ?_⟩
          simp [advance, program, hnum, hsign,
            TM2.step, TM2.stepAux]
          funext i
          fin_cases i <;> simp [transformed, hnum, hsign]
      | cons s rest =>
          refine ⟨2, (true, some s), by omega, ?_⟩
          simp [advance, program, hnum, hsign,
            TM2.step, TM2.stepAux]
          funext i
          fin_cases i <;> simp [transformed, hnum, hsign]

theorem transformed_length (S : Bank 3) :
    (encode (transformed S)).length ≤ (encode S).length + 2 := by
  rw [encode_length, encode_length]
  have h0 : (transformed S 0).length ≤ (S 0).length + 1 := by
    unfold transformed
    split_ifs <;> simp; omega
  have h1 : transformed S 1 = S 1 := by simp [transformed]
  have h2 : transformed S 2 = S 2 := by simp [transformed]
  simp [Fin.sum_univ_succ, h1, h2] at *
  omega

theorem outputs (input : List Bool) :
    machine.OutputsWithin input (result input)
      (7 * (input.length + 1) + 2 + 2 * (input.length + 2) + 4) := by
  apply BitMachineBankWrapper.outputs program .inspect (false, none)
    transformed input 2 (input.length + 2)
  · intro S _
    obtain ⟨t, v, ht, hr⟩ := local_run S
    exact ⟨t, ⟨none, v, transformed S⟩, ht, hr, rfl, rfl⟩
  · intro S hd
    rw [← BitMachineBankCodec.encode_decode hd]
    exact transformed_length S

def negateRaw (r : CurrentAdditive.CodeDCodec.RawRat) :
    CurrentAdditive.CodeDCodec.RawRat :=
  ⟨if r.numerator.isEmpty then r.negative else !r.negative,
    r.numerator, r.denominator⟩

theorem transformed_rawRatBank
    (r : CurrentAdditive.CodeDCodec.RawRat) :
    transformed (CurrentAdditive.CodeDCodec.rawRatBank r) =
      CurrentAdditive.CodeDCodec.rawRatBank (negateRaw r) := by
  cases r with
  | mk sign numerator denominator =>
      cases sign <;> cases numerator <;>
        (funext i; fin_cases i <;> simp [transformed, negateRaw,
          CurrentAdditive.CodeDCodec.rawRatBank])

theorem result_raw (r : CurrentAdditive.CodeDCodec.RawRat) :
    result (CurrentAdditive.CodeDCodec.encodeRawRat r) =
      CurrentAdditive.CodeDCodec.encodeRawRat (negateRaw r) := by
  simp [result, BitMachineBankWrapper.result,
    CurrentAdditive.CodeDCodec.encodeRawRat,
    BitMachineBankCodec.decode_encode, transformed_rawRatBank]

theorem negateRaw_value (r : CurrentAdditive.CodeDCodec.RawRat) :
    (negateRaw r).value = -r.value := by
  cases r with
  | mk sign numerator denominator =>
      cases sign <;> cases numerator <;>
        simp [negateRaw, CurrentAdditive.CodeDCodec.RawRat.value,
          EncodedCommunication.bitsValue]

theorem negateRaw_valid (r : CurrentAdditive.CodeDCodec.RawRat)
    (hr : r.Valid) : (negateRaw r).Valid := by
  simpa [CurrentAdditive.CodeDCodec.RawRat.Valid, negateRaw] using hr

theorem canonical_output (q : ℚ) :
    ∃ r : CurrentAdditive.CodeDCodec.RawRat,
      CurrentAdditive.CodeDCodec.decodeRawRat
        (result (CurrentAdditive.CodeDCodec.encodeRawRat
          (CurrentAdditive.GaussPhysical.rawOfRat q))) = some r ∧
      r.value = -q := by
  let r := negateRaw (CurrentAdditive.GaussPhysical.rawOfRat q)
  refine ⟨r, ?_, ?_⟩
  · rw [result_raw]
    exact CurrentAdditive.CodeDCodec.decodeRawRat_encodeRawRat r
      (negateRaw_valid _ (CurrentAdditive.GaussPhysical.rawOfRat_valid q))
  · rw [negateRaw_value, CurrentAdditive.GaussPhysical.rawOfRat_value]

#print axioms outputs
#print axioms canonical_output

end CurrentAdditive.GaussCertificateNegate
