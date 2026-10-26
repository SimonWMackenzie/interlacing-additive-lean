import EthInapproximability.CurrentPaper.BitMachineBinaryAdd

/-!
# Unequal-width binary addition

The multiplier's growing accumulator and its fixed multiplicand need not have
equal bitword lengths. This finite three-bank program scans both LSB-first
words until both are exhausted, treating a missing bit as zero. It is a raw
subroutine, not the complete multiplication controller.
-/

namespace EthInapproximability.CurrentPaper.BitMachineBinaryAddAny

open Turing Turing.TM2.Stmt BitMachineEncoding
open BitMachineBinaryAdd (sumBit nextCarry bit_identity)

def addAny : List Bool → List Bool → Bool → List Bool
  | [], [], carry => [carry]
  | a :: as, [], carry =>
      sumBit a false carry :: addAny as [] (nextCarry a false carry)
  | [], b :: bs, carry =>
      sumBit false b carry :: addAny [] bs (nextCarry false b carry)
  | a :: as, b :: bs, carry =>
      sumBit a b carry :: addAny as bs (nextCarry a b carry)

theorem addAny_length (a b : List Bool) (carry : Bool) :
    (addAny a b carry).length = max a.length b.length + 1 := by
  induction a generalizing b carry with
  | nil =>
      induction b generalizing carry with
      | nil => simp [addAny]
      | cons y ys ih =>
          simp only [addAny, List.length_cons, List.length_nil, Nat.zero_le,
            max_eq_right, ih]
  | cons x xs ih =>
      cases b with
      | nil =>
          simp only [addAny, List.length_cons, List.length_nil, Nat.zero_le,
            max_eq_left, ih]
      | cons y ys =>
          simp only [addAny, List.length_cons, ih]
          omega

theorem addAny_value (a b : List Bool) (carry : Bool) :
    EncodedCommunication.bitsValue (addAny a b carry) =
      EncodedCommunication.bitsValue a +
        EncodedCommunication.bitsValue b + carry.toNat := by
  induction a generalizing b carry with
  | nil =>
      induction b generalizing carry with
      | nil => cases carry <;> simp [addAny, EncodedCommunication.bitsValue]
      | cons y ys ih =>
          have h := ih (nextCarry false y carry)
          have hb := bit_identity false y carry
          simp only [addAny, EncodedCommunication.bitsValue, Nat.bit_val] at h ⊢
          simp only [Bool.toNat_false, Nat.zero_add] at hb
          omega
  | cons x xs ih =>
      cases b with
      | nil =>
          have h := ih [] (nextCarry x false carry)
          have hb := bit_identity x false carry
          simp only [addAny, EncodedCommunication.bitsValue, Nat.bit_val] at h ⊢
          simp only [Bool.toNat_false, Nat.add_zero] at hb
          omega
      | cons y ys =>
          have h := ih ys (nextCarry x y carry)
          have hb := bit_identity x y carry
          simp only [addAny, EncodedCommunication.bitsValue, Nat.bit_val] at h ⊢
          omega

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
        (branch (fun s => s.a.isSome || s.b.isSome)
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
  BitMachineBinaryAdd.bank a b saved

def cfg (l : Option Label) (s : Control) (a b saved : List Bool) :
    TM2.Cfg (fun _ : Fin 3 => Bool) Label Control :=
  ⟨l, s, bank a b saved⟩

def run (t : ℕ) (c : TM2.Cfg (fun _ : Fin 3 => Bool) Label Control) :=
  ((advance program)^[t]) c

private theorem run_step {c d : TM2.Cfg (fun _ : Fin 3 => Bool) Label Control}
    (h : TM2.step program c = some d) (t : ℕ) : run (t + 1) c = run t d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem step_scan_both (s : Control) (x y : Bool)
    (a b saved : List Bool) :
    TM2.step program (cfg (some .scan) s (x :: a) (y :: b) saved) =
      some (cfg (some .scan) ⟨nextCarry x y s.carry, none, none⟩
        a b (sumBit x y s.carry :: saved)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank,
    BitMachineBinaryAdd.bank]
  funext k
  fin_cases k <;> simp [BitMachineBinaryAdd.bank]

private theorem step_scan_left (s : Control) (x : Bool)
    (a saved : List Bool) :
    TM2.step program (cfg (some .scan) s (x :: a) [] saved) =
      some (cfg (some .scan) ⟨nextCarry x false s.carry, none, none⟩
        a [] (sumBit x false s.carry :: saved)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank,
    BitMachineBinaryAdd.bank]
  funext k
  fin_cases k <;> simp [BitMachineBinaryAdd.bank]

private theorem step_scan_right (s : Control) (y : Bool)
    (b saved : List Bool) :
    TM2.step program (cfg (some .scan) s [] (y :: b) saved) =
      some (cfg (some .scan) ⟨nextCarry false y s.carry, none, none⟩
        [] b (sumBit false y s.carry :: saved)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank,
    BitMachineBinaryAdd.bank]
  funext k
  fin_cases k <;> simp [BitMachineBinaryAdd.bank]

private theorem step_scan_nil (s : Control) (saved : List Bool) :
    TM2.step program (cfg (some .scan) s [] [] saved) =
      some (cfg (some .restore) ⟨s.carry, none, none⟩ [s.carry] [] saved) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank,
    BitMachineBinaryAdd.bank]
  funext k
  fin_cases k <;> simp [BitMachineBinaryAdd.bank]

private theorem step_restore_cons (s : Control) (a b : List Bool) (x : Bool)
    (saved : List Bool) :
    TM2.step program (cfg (some .restore) s a b (x :: saved)) =
      some (cfg (some .restore) ⟨s.carry, some x, none⟩ (x :: a) b saved) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank,
    BitMachineBinaryAdd.bank]
  funext k
  fin_cases k <;> simp [BitMachineBinaryAdd.bank]

private theorem step_restore_nil (s : Control) (a b : List Bool) :
    TM2.step program (cfg (some .restore) s a b []) =
      some (cfg none initial a b []) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank,
    BitMachineBinaryAdd.bank]

theorem restore_correct (s : Control) (a b saved : List Bool) :
    run (saved.length + 1) (cfg (some .restore) s a b saved) =
      cfg none initial (saved.reverse ++ a) b [] := by
  induction saved generalizing s a with
  | nil => simpa using run_step (step_restore_nil s a b) 0
  | cons x saved ih =>
      rw [List.length_cons, run_step (step_restore_cons s a b x saved)]
      simpa [List.reverse_cons, List.append_assoc] using
        ih ⟨s.carry, some x, none⟩ (x :: a)

theorem scan_correct (a b : List Bool) (s : Control) (saved : List Bool) :
    run (2 * max a.length b.length + saved.length + 2)
      (cfg (some .scan) s a b saved) =
      cfg none initial (saved.reverse ++ addAny a b s.carry) [] [] := by
  induction a generalizing b s saved with
  | nil =>
      induction b generalizing s saved with
      | nil =>
          have h := run_step (step_scan_nil s saved) (saved.length + 1)
          simpa [addAny, List.append_assoc] using
            h.trans (restore_correct ⟨s.carry, none, none⟩ [s.carry] [] saved)
      | cons y ys ih =>
          have h := run_step (step_scan_right s y ys saved)
            (2 * max ([] : List Bool).length ys.length +
              (sumBit false y s.carry :: saved).length + 2)
          rw [show 2 * max ([] : List Bool).length (y :: ys).length + saved.length + 2 =
              (2 * max ([] : List Bool).length ys.length +
                (sumBit false y s.carry :: saved).length + 2) + 1 by simp; omega]
          simpa [addAny, List.reverse_cons, List.append_assoc] using
            h.trans (ih ⟨nextCarry false y s.carry, none, none⟩
              (sumBit false y s.carry :: saved))
  | cons x xs ih =>
      cases b with
      | nil =>
          have h := run_step (step_scan_left s x xs saved)
            (2 * max xs.length ([] : List Bool).length +
              (sumBit x false s.carry :: saved).length + 2)
          rw [show 2 * max (x :: xs).length ([] : List Bool).length + saved.length + 2 =
              (2 * max xs.length ([] : List Bool).length +
                (sumBit x false s.carry :: saved).length + 2) + 1 by simp; omega]
          simpa [addAny, List.reverse_cons, List.append_assoc] using
            h.trans (ih [] ⟨nextCarry x false s.carry, none, none⟩
              (sumBit x false s.carry :: saved))
      | cons y ys =>
          have h := run_step (step_scan_both s x y xs ys saved)
            (2 * max xs.length ys.length +
              (sumBit x y s.carry :: saved).length + 2)
          rw [show 2 * max (x :: xs).length (y :: ys).length + saved.length + 2 =
              (2 * max xs.length ys.length +
                (sumBit x y s.carry :: saved).length + 2) + 1 by simp; omega]
          simpa [addAny, List.reverse_cons, List.append_assoc] using
            h.trans (ih ys ⟨nextCarry x y s.carry, none, none⟩
              (sumBit x y s.carry :: saved))

theorem run_correct (a b : List Bool) :
    run (2 * max a.length b.length + 2)
      (cfg (some .scan) initial a b []) =
      cfg none initial (addAny a b false) [] [] := by
  simpa using scan_correct a b initial []

theorem result_value (a b : List Bool) :
    EncodedCommunication.bitsValue (addAny a b false) =
      EncodedCommunication.bitsValue a + EncodedCommunication.bitsValue b := by
  simpa using addAny_value a b false

end EthInapproximability.CurrentPaper.BitMachineBinaryAddAny
