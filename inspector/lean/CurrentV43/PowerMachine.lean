import EthInapproximability.CurrentPaper.MatrixWeightedPower
import EthInapproximability.CurrentPaper.BitMachineStackRun
import EthInapproximability.CurrentPaper.BitMachineRawSequence
import EthInapproximability.CurrentPaper.BankFieldProjection
import CurrentAdditive.V22UnaryFork

/-! A literal fixed Boolean-stack machine for a variable unary power.
The public packet has exactly two encoded unary fields, base and exponent.
No arithmetic or natural-number value is stored in the finite control.
This adapter supports the v43 runtime construction at `thm:time-tradeoff`.
-/
namespace CurrentV43.PowerMachine
noncomputable section
open Turing EthInapproximability.CurrentPaper BitMachineEncoding BitMachineStackEmbedding
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192

inductive ParseLabel where | first | second deriving DecidableEq, Fintype

def parse : ParseLabel → TM2.Stmt (fun _ : Fin 8 => Bool) ParseLabel Bool
  | .first => .pop 7 (fun _ b => b.getD false)
      (.branch id (.push 1 (fun _ => true) (.goto fun _ => .first))
        (.goto fun _ => .second))
  | .second => .pop 7 (fun _ b => b.isSome)
      (.branch id (.push 6 (fun _ => true) (.goto fun _ => .second))
        (.push 0 (fun _ => true) (.load (fun _ => false) .halt)))

def parseCfg (l : Option ParseLabel) (v : Bool)
    (input base exponent acc : List Bool) : TM2.Cfg (fun _ : Fin 8 => Bool) ParseLabel Bool :=
  ⟨l,v,![acc,base,[],[],[],[],exponent,input]⟩

def parsed (b e : ℕ) : Fin 8 → List Bool :=
  ![[true],List.replicate b true,[],[],[],[],List.replicate e true,[]]

theorem first_run (b : ℕ) (rest acc : List Bool) (c e : ℕ) (v : Bool) :
    ((advance parse)^[b+1])
      (parseCfg (some .first) v (List.replicate b true++false::rest)
        (List.replicate c true) (List.replicate e true) acc) =
      parseCfg (some .second) false rest
        (List.replicate (b+c) true) (List.replicate e true) acc := by
  induction b generalizing c v with
  | zero =>
      simp [advance,parse,parseCfg,TM2.step,TM2.stepAux]
      funext j; fin_cases j <;> rfl
  | succ b ih =>
      rw [Function.iterate_succ_apply]
      have he : advance parse
          (parseCfg (some .first) v (List.replicate (b+1) true++false::rest)
            (List.replicate c true) (List.replicate e true) acc) =
          parseCfg (some .first) true (List.replicate b true++false::rest)
            (List.replicate (c+1) true) (List.replicate e true) acc := by
        simp [advance,parse,parseCfg,TM2.step,TM2.stepAux,List.replicate_succ]
        funext j; fin_cases j <;> rfl
      rw [he,ih]
      simp [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

theorem second_run (e c b : ℕ) (acc : List Bool) (v : Bool) :
    ((advance parse)^[e+1])
      (parseCfg (some .second) v (List.replicate e true)
        (List.replicate b true) (List.replicate c true) acc) =
      parseCfg none false [] (List.replicate b true)
        (List.replicate (e+c) true) (true::acc) := by
  induction e generalizing c v with
  | zero =>
      simp [advance,parse,parseCfg,TM2.step,TM2.stepAux]
      funext j; fin_cases j <;> rfl
  | succ e ih =>
      rw [Function.iterate_succ_apply]
      have he : advance parse
          (parseCfg (some .second) v (List.replicate (e+1) true)
            (List.replicate b true) (List.replicate c true) acc) =
          parseCfg (some .second) true (List.replicate e true)
            (List.replicate b true) (List.replicate (c+1) true) acc := by
        simp [advance,parse,parseCfg,TM2.step,TM2.stepAux,List.replicate_succ]
        funext j; fin_cases j <;> rfl
      rw [he,ih]
      simp [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

theorem parse_run (b e : ℕ) :
    ((advance parse)^[b+e+2])
      (parseCfg (some .first) false (MatrixUnaryArithmetic.encodeInput b e) [] [] []) =
      ⟨none,false,parsed b e⟩ := by
  have ha := first_run b (List.replicate e true) [] 0 0 false
  have hb := second_run e 0 b [] false
  rw [show b+e+2=(e+1)+(b+1) by omega,Function.iterate_add_apply]
  simpa only [MatrixUnaryArithmetic.encodeInput,List.replicate_zero,Nat.add_zero,parseCfg,parsed]
    using (congrArg ((advance parse)^[e+1]) ha).trans hb

def powerSlots : MatrixWeightedPower.Stack ↪ Fin 8 where
  toFun | .inl j => ⟨j.val,by omega⟩ | .inr _ => 6
  inj' := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (Fin.ext (congrArg (fun j : Fin 8 => j.val) h))
      | inr b => have := congrArg Fin.val h; simp at this; omega
    | inr a =>
      cases b with
      | inl b => have := congrArg Fin.val h; simp at this; omega
      | inr b => congr 1; exact Subsingleton.elim a b

def power (l : MatrixWeightedPower.Label) :
    TM2.Stmt (fun _ : Fin 8 => Bool) MatrixWeightedPower.Label MatrixWeightedPower.Control :=
  stackStmt powerSlots (MatrixWeightedPower.program l)

def powered (b e : ℕ) : Fin 8 → List Bool :=
  bank powerSlots (parsed b e)
    (MatrixWeightedPower.cfg none (false,false) (List.replicate (b^e) true)
      (List.replicate b true) [] []).stk

theorem power_run (b e : ℕ) :
    ∃ t ≤ MatrixWeightedPower.powerBound b e,
      ((advance power)^[t])
        (⟨some (.inr MatrixWeightedPower.Admin.test),(false,false),parsed b e⟩ :
          TM2.Cfg (fun _ : Fin 8 => Bool) _ _) = ⟨none,(false,false),powered b e⟩ := by
  let c := MatrixWeightedPower.cfg (some (.inr .test)) (false,false)
    (List.replicate 1 true) (List.replicate b true) [] (List.replicate e true)
  obtain ⟨t,ht,hr⟩ := MatrixWeightedPower.power_run b e
  have hi : bank powerSlots (parsed b e) c.stk = parsed b e := by
    apply bank_eq_self
    intro j
    rcases j with j | j <;> fin_cases j <;> rfl
  have h := BitMachineStackRun.run powerSlots (parsed b e) MatrixWeightedPower.program c t
  change ((advance MatrixWeightedPower.program)^[t]) c = _ at hr
  rw [hr] at h
  exact ⟨t,ht,by simpa only [power,stackCfg,hi,c,powered] using h⟩

def separatedProgram := BitMachineRawSequence.program parse power
  (.inr MatrixWeightedPower.Admin.test) false (false,false)
def separatedStart : BitMachineRawSequence.Label ParseLabel MatrixWeightedPower.Label :=
  BitMachineRawSequence.leftLabel .first
def separatedMachine : BitMachine.Machine :=
  ofFinite (7 : Fin 8) 0 separatedStart (false,(false,false)) separatedProgram
def separatedClock (b e : ℕ) := b+e+3+MatrixWeightedPower.powerBound b e

theorem separated_outputs (b e : ℕ) :
    separatedMachine.OutputsWithin (MatrixUnaryArithmetic.encodeInput b e)
      (List.replicate (b^e) true) (separatedClock b e) := by
  obtain ⟨t,ht,he⟩ := power_run b e
  obtain ⟨u,hu,hr⟩ := BitMachineRawSequence.runs parse power .first
    (.inr MatrixWeightedPower.Admin.test) false false (false,false) (false,false)
    (parseCfg (some .first) false (MatrixUnaryArithmetic.encodeInput b e) [] [] []).stk
    (parsed b e) (powered b e) (b+e+2) t (parse_run b e) he
  have hi : rawInit (7 : Fin 8) separatedStart (false,(false,false))
      (MatrixUnaryArithmetic.encodeInput b e) =
      (⟨some separatedStart,(false,(false,false)),
        (parseCfg (some .first) false (MatrixUnaryArithmetic.encodeInput b e) [] [] []).stk⟩ :
        TM2.Cfg (fun _ : Fin 8 => Bool) _ _) := by
    unfold rawInit parseCfg
    congr 1
    funext j; fin_cases j <;> simp
  have hr' : ((advance separatedProgram)^[u])
      (⟨some separatedStart,(false,(false,false)),
        (parseCfg (some .first) false (MatrixUnaryArithmetic.encodeInput b e) [] [] []).stk⟩ :
        TM2.Cfg (fun _ : Fin 8 => Bool) _ _) = ⟨none,(false,(false,false)),powered b e⟩ := hr
  apply outputsWithin_of_raw_run (7 : Fin 8) 0 separatedStart (false,(false,false))
    separatedProgram (MatrixUnaryArithmetic.encodeInput b e) (List.replicate (b^e) true) u _
    (by dsimp [separatedClock]; omega)
  · rw [hi,hr']
  · rw [hi,hr']
    change powered b e (powerSlots (.inl 0)) = _
    rw [powered,bank_at]
    rfl

def fields (b e : ℕ) : Fin 2 → List Bool := ![List.replicate b true,List.replicate e true]
def input (b e : ℕ) := BitMachineBankCodec.encode (fields b e)
def unpair : BitMachine.Machine :=
  V22UnaryFork.machine (BankFieldProjection.machine (0 : Fin 2)) (BankFieldProjection.machine (1 : Fin 2))
def machine : BitMachine.Machine := BitMachineComposition.composition unpair separatedMachine
def clock (b e : ℕ) := 20*(input b e).length+6*b+6*e+40+MatrixWeightedPower.powerBound b e
def unpairClock (b e : ℕ) := 20*(input b e).length+3*b+3*e+33

theorem unpair_outputs (b e : ℕ) : unpair.OutputsWithin (input b e)
    (MatrixUnaryArithmetic.encodeInput b e) (unpairClock b e) := by
  have ha := BankFieldProjection.outputs (0 : Fin 2) (input b e)
  have hb := BankFieldProjection.outputs (1 : Fin 2) (input b e)
  simp only [input,BankFieldProjection.result_encode,fields,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one] at ha hb
  have hp := V22UnaryFork.outputs (BankFieldProjection.machine (0 : Fin 2))
    (BankFieldProjection.machine (1 : Fin 2)) (input b e) b e
    (8*((input b e).length+1)) (8*((input b e).length+1)) ha hb
  have heq : 4*(input b e).length+8*((input b e).length+1)+8*((input b e).length+1)+
      3*b+3*e+17=unpairClock b e := by dsimp [unpairClock]; ring
  rw [heq] at hp
  exact hp

theorem input_length (b e : ℕ) : (input b e).length = 2*(b+e)+2 := by
  simp [input,BitMachineBankCodec.encode_length,fields,Fin.sum_univ_two]

theorem outputs (b e : ℕ) : machine.OutputsWithin (input b e)
    (List.replicate (b^e) true) (clock b e) := by
  have ha := BankFieldProjection.outputs (0 : Fin 2) (input b e)
  have hb := BankFieldProjection.outputs (1 : Fin 2) (input b e)
  simp only [input,BankFieldProjection.result_encode,fields,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one] at ha hb
  have hp := V22UnaryFork.outputs (BankFieldProjection.machine (0 : Fin 2))
    (BankFieldProjection.machine (1 : Fin 2)) (input b e) b e
    (8*((input b e).length+1)) (8*((input b e).length+1)) ha hb
  have h := BitMachineComposition.composition_outputsWithin unpair separatedMachine hp
    (separated_outputs b e)
  have heq : 4*(input b e).length+8*((input b e).length+1)+8*((input b e).length+1)+
      3*b+3*e+17+2*(MatrixUnaryArithmetic.encodeInput b e).length+2+separatedClock b e =
      clock b e := by
    simp only [clock,separatedClock,MatrixUnaryArithmetic.encodeInput,List.length_append,
      List.length_cons,List.length_replicate]
    ring
  rw [heq] at h
  exact h

theorem clock_le (b e : ℕ) : clock b e ≤ 256*(b+e+b^e+1)^3 := by
  let W := b+e+b^e+1
  have hW : 1≤W := by dsimp [W]; omega
  have hb : b≤W := by dsimp [W]; omega
  have he : e+1≤W := by dsimp [W]; omega
  have hp : b^e+1≤W := by dsimp [W]; omega
  have hW2 : W≤W^2 := by nlinarith
  have hW3 : W≤W^3 := by nlinarith [Nat.mul_le_mul_right W hW2]
  have hprod : (b^e+1)*b≤W^2 := by
    simpa [pow_two] using Nat.mul_le_mul hp hb
  have hinner : 3*(b^e+1)*b+5*(b^e+1)+7≤15*W^2 := by nlinarith
  have hpower := MatrixWeightedPower.powerBound_polynomial b e
  have hpower' : MatrixWeightedPower.powerBound b e≤15*W^3 := by
    calc
      MatrixWeightedPower.powerBound b e ≤
          (e+1)*(3*(b^e+1)*b+5*(b^e+1)+7) := hpower
      _ ≤ W*(15*W^2) := Nat.mul_le_mul he hinner
      _ = 15*W^3 := by ring
  change clock b e≤256*W^3
  rw [clock,input_length]
  have hlin : 20*(2*(b+e)+2)+6*b+6*e+40≤80*W := by dsimp [W]; omega
  nlinarith

theorem outputs_polynomial (b e : ℕ) : machine.OutputsWithin (input b e)
    (List.replicate (b^e) true) (256*(b+e+b^e+1)^3) :=
  BitMachine.outputsWithin_mono machine (outputs b e) (clock_le b e)

theorem clock_le_power (b e : ℕ) (hb : 2≤b) : clock b e≤b^(3*e+17) := by
  have hb0 : 0<b := by omega
  have hbase : b≤b^(e+1) := by
    simpa using Nat.pow_le_pow_right hb0 (show 1≤e+1 by omega)
  have hpow : b^e≤b^(e+1) := Nat.pow_le_pow_right hb0 (by omega)
  have hexp : e≤b^(e+1) := (Nat.lt_two_pow_self (n:=e)).le.trans
    ((Nat.pow_le_pow_left hb e).trans hpow)
  have hone : 1≤b^(e+1) := (show 1≤b by omega).trans hbase
  have hsum : b+e+b^e+1≤4*b^(e+1) := by omega
  have hc : 16384≤b^14 := by
    calc
      16384 = 2^14 := by norm_num
      _ ≤ b^14 := Nat.pow_le_pow_left hb 14
  calc
    clock b e ≤ 256*(b+e+b^e+1)^3 := clock_le b e
    _ ≤ 256*(4*b^(e+1))^3 := Nat.mul_le_mul_left 256 (Nat.pow_le_pow_left hsum 3)
    _ = 16384*b^(3*(e+1)) := by rw [mul_pow,←pow_mul]; ring
    _ ≤ b^14*b^(3*(e+1)) := Nat.mul_le_mul_right _ hc
    _ = b^(3*e+17) := by rw [←pow_add]; congr 1; omega

#print axioms outputs
#print axioms clock_le
#print axioms outputs_polynomial
#print axioms clock_le_power
end
end CurrentV43.PowerMachine
