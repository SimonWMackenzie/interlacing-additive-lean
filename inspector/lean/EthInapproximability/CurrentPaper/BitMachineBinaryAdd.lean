import EthInapproximability.CurrentPaper.BitMachineEncoding
import EthInapproximability.CurrentPaper.BitMachineBankWrapper
import EthInapproximability.CurrentPaper.EncodedCommunication
import Mathlib.Tactic

/-!
# Fixed-width binary addition for the prime-field accessor

Source: frozen v8 `B-effectivity-details.tex`, binary modular Horner arithmetic
in `lem:paper-explicit-balanced-family`. Two equal-length LSB-first Boolean
words occupy banks 0 and 1. The finite controller stores one carry bit; the
answer has exactly one extra high bit in bank 0. Bank 1 and scratch bank 2
finish empty. This is a raw-bank arithmetic primitive, not yet a multiplier
or the complete prime-family entry evaluator.
-/

namespace EthInapproximability.CurrentPaper.BitMachineBinaryAdd

open Turing Turing.TM2.Stmt BitMachineEncoding

def sumBit (a b carry : Bool) : Bool := xor (xor a b) carry
def nextCarry (a b carry : Bool) : Bool :=
  (a && b) || ((a || b) && carry)

theorem bit_identity (a b carry : Bool) :
    a.toNat + b.toNat + carry.toNat =
      (sumBit a b carry).toNat + 2 * (nextCarry a b carry).toNat := by
  cases a <;> cases b <;> cases carry <;> decide

def addPairs : List (Bool × Bool) → Bool → List Bool × Bool
  | [], carry => ([], carry)
  | (a, b) :: rest, carry =>
      let tail := addPairs rest (nextCarry a b carry)
      (sumBit a b carry :: tail.1, tail.2)

theorem addPairs_length (q : List (Bool × Bool)) (carry : Bool) :
    (addPairs q carry).1.length = q.length := by
  induction q generalizing carry with
  | nil => rfl
  | cons p q ih =>
      rcases p with ⟨a, b⟩
      simp [addPairs, ih]

theorem addPairs_value (q : List (Bool × Bool)) (carry : Bool) :
    EncodedCommunication.bitsValue (q.map Prod.fst) +
        EncodedCommunication.bitsValue (q.map Prod.snd) + carry.toNat =
      EncodedCommunication.bitsValue (addPairs q carry).1 +
        2 ^ q.length * (addPairs q carry).2.toNat := by
  induction q generalizing carry with
  | nil => cases carry <;> simp [addPairs, EncodedCommunication.bitsValue]
  | cons p q ih =>
      rcases p with ⟨a, b⟩
      have h := ih (nextCarry a b carry)
      have hb := bit_identity a b carry
      simp only [addPairs, List.map_cons, List.length_cons,
        EncodedCommunication.bitsValue, Nat.bit_val, pow_succ]
      have hm : 2 ^ q.length * 2 * (addPairs q (nextCarry a b carry)).2.toNat =
          2 * (2 ^ q.length * (addPairs q (nextCarry a b carry)).2.toNat) := by ring
      omega

theorem bitsValue_append_high (q : List Bool) (b : Bool) :
    EncodedCommunication.bitsValue (q ++ [b]) =
      EncodedCommunication.bitsValue q + 2 ^ q.length * b.toNat := by
  induction q with
  | nil => cases b <;> simp [EncodedCommunication.bitsValue]
  | cons a q ih =>
      simp only [List.cons_append, List.length_cons, EncodedCommunication.bitsValue,
        Nat.bit_val, ih, pow_succ]
      ring

theorem addPairs_spec (q : List (Bool × Bool)) :
    EncodedCommunication.bitsValue
        ((addPairs q false).1 ++ [(addPairs q false).2]) =
      EncodedCommunication.bitsValue (q.map Prod.fst) +
        EncodedCommunication.bitsValue (q.map Prod.snd) := by
  rw [bitsValue_append_high]
  simpa [addPairs_length] using (addPairs_value q false).symm

inductive Label where
  | scan | restore
  deriving DecidableEq, Fintype

structure Control where
  carry : Bool
  a : Option Bool
  b : Option Bool
  deriving DecidableEq, Fintype

def initial : Control := ⟨false, none, none⟩

def program : Label → TM2.Stmt (fun _ : Fin 3 => Bool) Label Control
  | .scan => pop 0 (fun s a => ⟨s.carry, a, none⟩)
      (pop 1 (fun s b => ⟨s.carry, s.a, b⟩)
        (branch (fun s => s.a.isSome)
          (push 2 (fun s => sumBit (s.a.getD false) (s.b.getD false) s.carry)
            (load (fun s => ⟨nextCarry (s.a.getD false) (s.b.getD false)
                s.carry, none, none⟩)
              (goto (fun _ => .scan))))
          (push 0 (fun s => s.carry) (goto (fun _ => .restore)))))
  | .restore => pop 2 (fun s a => ⟨s.carry, a, none⟩)
      (branch (fun s => s.a.isSome)
        (push 0 (fun s => s.a.getD false) (goto (fun _ => .restore)))
        (load (fun _ => initial) halt))

def bank (a b saved : List Bool) : Fin 3 → List Bool :=
  fun k => if k = 0 then a else if k = 1 then b else saved

def cfg (l : Option Label) (s : Control) (a b saved : List Bool) :
    TM2.Cfg (fun _ : Fin 3 => Bool) Label Control :=
  ⟨l, s, bank a b saved⟩

def run (t : ℕ) (c : TM2.Cfg (fun _ : Fin 3 => Bool) Label Control) :=
  ((advance program)^[t]) c

private theorem run_step {c d : TM2.Cfg (fun _ : Fin 3 => Bool) Label Control}
    (h : TM2.step program c = some d) (t : ℕ) : run (t + 1) c = run t d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : TM2.Cfg (fun _ : Fin 3 => Bool) Label Control}
    {t : ℕ} (h : run t c = d) (u : ℕ) : run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem step_scan_cons (s : Control) (a b : Bool)
    (as bs saved : List Bool) :
    TM2.step program (cfg (some .scan) s (a :: as) (b :: bs) saved) =
      some (cfg (some .scan) ⟨nextCarry a b s.carry, none, none⟩
        as bs (sumBit a b s.carry :: saved)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> simp [bank]

private theorem step_scan_nil (s : Control) (saved : List Bool) :
    TM2.step program (cfg (some .scan) s [] [] saved) =
      some (cfg (some .restore) ⟨s.carry, none, none⟩ [s.carry] [] saved) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> simp [bank]

private theorem step_restore_cons (s : Control) (a b : List Bool) (x : Bool)
    (saved : List Bool) :
    TM2.step program (cfg (some .restore) s a b (x :: saved)) =
      some (cfg (some .restore) ⟨s.carry, some x, none⟩ (x :: a) b saved) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> simp [bank]

private theorem step_restore_nil (s : Control) (a b : List Bool) :
    TM2.step program (cfg (some .restore) s a b []) =
      some (cfg none initial a b []) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

theorem restore_correct (s : Control) (a b saved : List Bool) :
    run (saved.length + 1) (cfg (some .restore) s a b saved) =
      cfg none initial (saved.reverse ++ a) b [] := by
  induction saved generalizing s a with
  | nil => simpa using run_step (step_restore_nil s a b) 0
  | cons x saved ih =>
      rw [List.length_cons, run_step (step_restore_cons s a b x saved)]
      simpa [List.reverse_cons, List.append_assoc] using
        ih ⟨s.carry, some x, none⟩ (x :: a)

theorem scan_correct (q : List (Bool × Bool)) (s : Control) (saved : List Bool) :
    run (2 * q.length + saved.length + 2)
      (cfg (some .scan) s (q.map Prod.fst) (q.map Prod.snd) saved) =
      cfg none initial
        (saved.reverse ++ (addPairs q s.carry).1 ++ [(addPairs q s.carry).2]) [] [] := by
  induction q generalizing s saved with
  | nil =>
      have h := run_step (step_scan_nil s saved) (saved.length + 1)
      simpa [addPairs, List.append_assoc] using
        h.trans (restore_correct ⟨s.carry, none, none⟩ [s.carry] [] saved)
  | cons p q ih =>
      rcases p with ⟨a, b⟩
      have h := run_step (step_scan_cons s a b (q.map Prod.fst) (q.map Prod.snd) saved)
        (2 * q.length + (sumBit a b s.carry :: saved).length + 2)
      rw [show 2 * ((a, b) :: q).length + saved.length + 2 =
          (2 * q.length + (sumBit a b s.carry :: saved).length + 2) + 1 by simp; omega]
      simpa [addPairs, List.reverse_cons, List.append_assoc] using
        h.trans (ih ⟨nextCarry a b s.carry, none, none⟩ (sumBit a b s.carry :: saved))

theorem run_correct (q : List (Bool × Bool)) :
    run (2 * q.length + 2)
      (cfg (some .scan) initial (q.map Prod.fst) (q.map Prod.snd) []) =
      cfg none initial ((addPairs q false).1 ++ [(addPairs q false).2]) [] [] := by
  simpa using scan_correct q initial []

def initialBank (q : List (Bool × Bool)) : Fin 3 → List Bool :=
  bank (q.map Prod.fst) (q.map Prod.snd) []

def finalBank (q : List (Bool × Bool)) : Fin 3 → List Bool :=
  bank ((addPairs q false).1 ++ [(addPairs q false).2]) [] []

def packedInput (q : List (Bool × Bool)) : List Bool :=
  BitMachineBankCodec.encode (initialBank q)

theorem initialBank_code_length (q : List (Bool × Bool)) :
    (packedInput q).length = 4 * q.length + 3 := by
  rw [packedInput, BitMachineBankCodec.encode_length]
  simp [initialBank, bank, Fin.sum_univ_succ]
  omega

theorem finalBank_code_length (q : List (Bool × Bool)) :
    (BitMachineBankCodec.encode (finalBank q)).length = 2 * q.length + 5 := by
  rw [BitMachineBankCodec.encode_length]
  simp [finalBank, bank, Fin.sum_univ_succ, addPairs_length]
  omega

theorem packed_run (q : List (Bool × Bool)) :
    ∃ (u : ℕ) (S' : Fin 3 → List Bool),
      u ≤ 20 * ((packedInput q).length + 1) ∧
      BitMachineBankWrapper.run program .scan initial u
        (BitMachineBankWrapper.cfg
          (some (.inr (.parse (.scan 0)))) (initial, none)
          (fun _ : Fin 3 => []) (packedInput q) [] []) =
        BitMachineBankWrapper.cfg none (initial, none) S' [] []
          (BitMachineBankCodec.encode (finalBank q)) := by
  have hdecode : BitMachineBankCodec.decode 3 (packedInput q) =
      some (initialBank q) := by simp [packedInput]
  let c := cfg none initial ((addPairs q false).1 ++ [(addPairs q false).2]) [] []
  have hlocal : ((advance program)^[2 * q.length + 2])
      (⟨some Label.scan, initial, initialBank q⟩ :
        TM2.Cfg (fun _ : Fin 3 => Bool) Label Control) = c := by
    simpa only [run, cfg, initialBank] using run_correct q
  have hhalt : c.l = none := rfl
  obtain ⟨u, S', hu, hr⟩ := BitMachineBankWrapper.packed_run
    program .scan initial (packedInput q) (initialBank q) hdecode
    (2 * q.length + 2) c hlocal hhalt
  have hfinal : c.stk = finalBank q := rfl
  rw [hfinal] at hu hr
  have he : BitMachineBankSerialize.encode (List.ofFn (finalBank q)) =
      BitMachineBankCodec.encode (finalBank q) := by
    rw [BitMachineBankCodec.encode_eq_list]
    rfl
  rw [he] at hu hr
  refine ⟨u, S', ?_, hr⟩
  rw [initialBank_code_length, finalBank_code_length] at hu
  rw [initialBank_code_length]
  omega

noncomputable def packedMachine : BitMachine.Machine :=
  BitMachineBankWrapper.machine program .scan initial

theorem packed_outputs (q : List (Bool × Bool)) :
    packedMachine.OutputsWithin (packedInput q)
      (BitMachineBankCodec.encode (finalBank q))
      (20 * ((packedInput q).length + 1)) := by
  obtain ⟨u, S', hu, hr⟩ := packed_run q
  change (BitMachineBankWrapper.machine program .scan initial).OutputsWithin
    (packedInput q) (BitMachineBankCodec.encode (finalBank q))
    (20 * ((packedInput q).length + 1))
  apply outputsWithin_of_raw_run (.inr 0) (.inr 2)
    (.inr (.parse (.scan 0))) (initial, none)
    (BitMachineBankWrapper.program program .scan initial)
    (packedInput q)
    (BitMachineBankCodec.encode (finalBank q)) u _ hu
  · rw [BitMachineBankWrapper.initial_cfg]
    change (BitMachineBankWrapper.run program .scan initial u _).l = none
    rw [hr]
    rfl
  · rw [BitMachineBankWrapper.initial_cfg]
    change (BitMachineBankWrapper.run program .scan initial u _).stk (.inr 2) = _
    rw [hr]
    rfl

end EthInapproximability.CurrentPaper.BitMachineBinaryAdd
