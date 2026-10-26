import EthInapproximability.CurrentPaper.EncodedCommunication
import EthInapproximability.CurrentPaper.BitMachineEncoding

/-!
# Reading canonical binary fields on Boolean stacks

Source: locked v8 `03-exact-hardness.tex`, NP membership, under the fixed
bit-machine convention in `06-eth.tex`. Fields use the exact self-delimiting
format of `EncodedCommunication`: `true,bit` pairs followed by `false`.
Canonicality is checked by remembering the last payload bit in finite control,
not by expanding the represented number.
-/

namespace EthInapproximability.CurrentPaper.ProtocolBinaryHeader

open Turing TM2.Stmt BitMachineEncoding EncodedCommunication

/-- The empty word represents zero; a nonempty canonical word ends in one. -/
def canonical : List Bool → Bool
  | [] => true
  | [b] => b
  | _ :: b :: bs => canonical (b :: bs)

theorem canonical_of_bits (n : Nat) : canonical n.bits = true := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih =>
      rw [Nat.bits_append_bit n b hn]
      cases h : n.bits with
      | nil =>
          have hz : n = 0 := by simpa [h] using (bitsValue_bits n).symm
          simp [canonical, hn hz]
      | cons c bs => simpa [h, canonical] using ih

theorem bits_of_canonical (bs : List Bool) (h : canonical bs = true) :
    (bitsValue bs).bits = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      cases bs with
      | nil =>
          have hb : b = true := h
          subst b
          rfl
      | cons c bs =>
          have hc : canonical (c :: bs) = true := h
          have hi := ih hc
          have hn : bitsValue (c :: bs) ≠ 0 := by
            intro hz
            simp [hz] at hi
          change (Nat.bit b (bitsValue (c :: bs))).bits = b :: c :: bs
          rw [Nat.bits_append_bit _ b (fun hz => (hn hz).elim), hi]

theorem canonical_iff_bits (bs : List Bool) :
    canonical bs = true ↔ (bitsValue bs).bits = bs := by
  constructor
  · exact bits_of_canonical bs
  · intro h
    rw [← h]
    exact canonical_of_bits _

def canonicalFrom : Option Bool → List Bool → Bool
  | seen, [] => decide (seen ≠ some false)
  | _, b :: bs => canonicalFrom (some b) bs

theorem canonicalFrom_none (bs : List Bool) : canonicalFrom none bs = canonical bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      cases bs with
      | nil => cases b <;> rfl
      | cons c bs => simpa only [canonicalFrom, canonical] using ih

/-- A parser whose finite state remembers only the last payload bit. -/
def readChecked (seen : Option Bool) : List Bool → Option (List Bool × List Bool)
  | [] => none
  | false :: rest => if seen = some false then none else some ([], rest)
  | true :: [] => none
  | true :: b :: rest => (readChecked (some b) rest).map (fun p => (b :: p.1, p.2))

theorem readChecked_spec (input : List Bool) (seen : Option Bool) :
    readChecked seen input = (do
      let (bs, rest) ← readField input
      if canonicalFrom seen bs then some (bs, rest) else none) := by
  induction input using readField.induct generalizing seen with
  | case1 => rfl
  | case2 rest =>
      simp only [readChecked, readField, Bind.bind, Option.bind, canonicalFrom]
      split <;> simp_all
  | case3 => rfl
  | case4 b input ih =>
      simp only [readChecked, readField, ih]
      cases hf : readField input with
      | none => rfl
      | some p =>
          rcases p with ⟨bs, rest⟩
          simp only [Bind.bind, Option.bind, pure, canonicalFrom]
          cases hc : canonicalFrom (some b) bs <;> rfl

theorem readChecked_readNat (input : List Bool) :
    (readChecked none input).map (fun p => (bitsValue p.1, p.2)) = readNat input := by
  rw [readChecked_spec]
  unfold readNat
  cases hf : readField input with
  | none => rfl
  | some p =>
      rcases p with ⟨bs, rest⟩
      simp only [Bind.bind, Option.bind, canonicalFrom_none]
      by_cases hc : canonical bs = true
      · simp [hc, (canonical_iff_bits bs).mp hc]
      · have hn : (bitsValue bs).bits ≠ bs := (canonical_iff_bits bs).not.mp hc
        have hf : canonical bs = false := Bool.eq_false_iff.mpr hc
        simp [hf, hn]

inductive Label where
  | scan | payload | restore
  deriving DecidableEq, Fintype

abbrev Control := Option Bool × Option Bool

def failure : TM2.Stmt (fun _ : Fin 3 => Bool) Label Control :=
  push 2 (fun _ => false) halt

def program : Label → TM2.Stmt (fun _ : Fin 3 => Bool) Label Control
  | .scan =>
      pop 0 (fun s b => (s.1, b))
        (branch (fun s => s.2.isSome)
          (branch (fun s => s.2.getD false) (goto (fun _ => .payload))
            (branch (fun s => decide (s.1 = some false)) failure
              (goto (fun _ => .restore)))) failure)
  | .payload =>
      pop 0 (fun _ b => (b, b))
        (branch (fun s => s.2.isSome)
          (push 1 (fun s => s.2.getD false) (goto (fun _ => .scan))) failure)
  | .restore =>
      pop 1 (fun s b => (s.1, b))
        (branch (fun s => s.2.isSome)
          (push 2 (fun s => s.2.getD false) (goto (fun _ => .restore)))
          (push 2 (fun _ => true) halt))

def stackContents (source saved target : List Bool) : Fin 3 → List Bool :=
  fun k => if k = 0 then source else if k = 1 then saved else target

def cfg (l : Option Label) (s : Control) (source saved target : List Bool) :
    TM2.Cfg (fun _ : Fin 3 => Bool) Label Control :=
  ⟨l, s, stackContents source saved target⟩

def run (n : Nat) (c : TM2.Cfg (fun _ : Fin 3 => Bool) Label Control) :=
  ((advance program)^[n]) c

theorem run_succ_first (n : Nat) (c : TM2.Cfg (fun _ : Fin 3 => Bool) Label Control) :
    run (n + 1) c = run n (advance program c) := by
  exact Function.iterate_succ_apply _ _ _

theorem scan_nil (seen popped : Option Bool) (saved target : List Bool) :
    advance program (cfg (some .scan) (seen, popped) [] saved target) =
      cfg none (seen, none) [] saved (false :: target) := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, stackContents, failure]
  funext k
  fin_cases k <;> rfl

theorem scan_false (seen popped : Option Bool) (source saved target : List Bool) :
    advance program (cfg (some .scan) (seen, popped) (false :: source) saved target) =
      if seen = some false then cfg none (seen, some false) source saved (false :: target)
      else cfg (some .restore) (seen, some false) source saved target := by
  by_cases hs : seen = some false <;>
    simp [advance, TM2.step, TM2.stepAux, program, cfg, stackContents, failure, hs]
  all_goals
    funext k
    fin_cases k <;> rfl

theorem scan_true (seen popped : Option Bool) (source saved target : List Bool) :
    advance program (cfg (some .scan) (seen, popped) (true :: source) saved target) =
      cfg (some .payload) (seen, some true) source saved target := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, stackContents]
  funext k
  fin_cases k <;> rfl

theorem payload_nil (seen popped : Option Bool) (saved target : List Bool) :
    advance program (cfg (some .payload) (seen, popped) [] saved target) =
      cfg none (none, none) [] saved (false :: target) := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, stackContents, failure]
  funext k
  fin_cases k <;> rfl

theorem payload_cons (seen popped : Option Bool) (b : Bool) (source saved target : List Bool) :
    advance program (cfg (some .payload) (seen, popped) (b :: source) saved target) =
      cfg (some .scan) (some b, some b) source (b :: saved) target := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, stackContents, failure]
  funext k
  fin_cases k <;> rfl

theorem restore_nil (seen popped : Option Bool) (source target : List Bool) :
    advance program (cfg (some .restore) (seen, popped) source [] target) =
      cfg none (seen, none) source [] (true :: target) := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, stackContents]
  funext k
  fin_cases k <;> rfl

theorem restore_cons (seen popped : Option Bool) (b : Bool) (source saved target : List Bool) :
    advance program (cfg (some .restore) (seen, popped) source (b :: saved) target) =
      cfg (some .restore) (seen, some b) source saved (b :: target) := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, stackContents]
  funext k
  fin_cases k <;> rfl

theorem restore_correct (seen popped : Option Bool) (source saved target : List Bool) :
    run (saved.length + 1) (cfg (some .restore) (seen, popped) source saved target) =
      cfg none (seen, none) source [] (true :: (saved.reverse ++ target)) := by
  induction saved generalizing popped target with
  | nil => simp [restore_nil, run]
  | cons b saved ih =>
      rw [List.length_cons, run_succ_first, restore_cons, ih]
      simp

def Post (seen : Option Bool) (input saved target : List Bool)
    (c : TM2.Cfg (fun _ : Fin 3 => Bool) Label Control) : Prop :=
  c.l = none ∧ match readChecked seen input with
    | none => c.stk 2 = false :: target
    | some (bs, rest) => c.stk 0 = rest ∧ c.stk 1 = [] ∧
        c.stk 2 = true :: (saved.reverse ++ bs ++ target)

/-- Total correctness and a linear transition bound, including truncated
and noncanonical fields. Successful reads preserve the unused suffix. -/
theorem scan_correct (input : List Bool) (seen popped : Option Bool)
    (saved target : List Bool) :
    ∃ t ≤ 2 * input.length + saved.length + 2,
      Post seen input saved target
        (run t (cfg (some .scan) (seen, popped) input saved target)) := by
  induction input using readField.induct generalizing seen popped saved target with
  | case1 =>
      refine ⟨1, by simp, ?_⟩
      rw [show 1 = 0 + 1 from rfl, run_succ_first, scan_nil]
      simp [Post, readChecked, run, cfg, stackContents]
  | case2 rest =>
      by_cases hs : seen = some false
      · refine ⟨1, by simp, ?_⟩
        rw [show 1 = 0 + 1 from rfl, run_succ_first, scan_false, if_pos hs]
        simp [Post, readChecked, hs, run, cfg, stackContents]
      · refine ⟨saved.length + 2, by simp, ?_⟩
        rw [show saved.length + 2 = (saved.length + 1) + 1 by omega,
          run_succ_first, scan_false, if_neg hs, restore_correct]
        simp [Post, readChecked, hs, cfg, stackContents]
  | case3 =>
      refine ⟨2, by simp, ?_⟩
      rw [show 2 = (0 + 1) + 1 from rfl, run_succ_first, scan_true,
        run_succ_first, payload_nil]
      simp [Post, readChecked, run, cfg, stackContents]
  | case4 b rest ih =>
      obtain ⟨t, ht, hpost⟩ := ih (some b) (some b) (b :: saved) target
      refine ⟨t + 2, by simp at ht ⊢; omega, ?_⟩
      rw [show t + 2 = (t + 1) + 1 by omega, run_succ_first, scan_true,
        run_succ_first, payload_cons]
      unfold Post at hpost ⊢
      refine ⟨hpost.1, ?_⟩
      cases hp : readChecked (some b) rest with
      | none => simpa [readChecked, hp] using hpost.2
      | some pair =>
          rcases pair with ⟨bs, suffix⟩
          simpa [readChecked, hp, List.reverse_cons, List.append_assoc] using hpost.2

/-- One flag bit distinguishes failure from a successfully decoded zero. -/
def result (input : List Bool) : List Bool :=
  match readChecked none input with
  | none => [false]
  | some (bs, _) => true :: bs

noncomputable def machine : BitMachine.Machine :=
  ofFinite (0 : Fin 3) 2 .scan ((none, none) : Control) program

theorem rawInit_eq (input : List Bool) :
    rawInit (0 : Fin 3) .scan ((none, none) : Control) input =
      cfg (some .scan) (none, none) input [] [] := by
  unfold rawInit cfg
  congr 1
  funext k
  fin_cases k <;> rfl

theorem outputs (input : List Bool) :
    machine.OutputsWithin input (result input) (2 * input.length + 2) := by
  obtain ⟨t, ht, hpost⟩ := scan_correct input none none [] []
  apply outputsWithin_of_raw_run (0 : Fin 3) 2 .scan ((none, none) : Control)
    program input (result input) t (2 * input.length + 2) (by simpa using ht)
  · rw [rawInit_eq]
    exact hpost.1
  · rw [rawInit_eq]
    have h := hpost.2
    cases hp : readChecked none input with
    | none => simpa [Post, result, hp] using h
    | some p =>
        rcases p with ⟨bs, suffix⟩
        have hout := h
        simp only [hp] at hout
        simpa [result, hp] using hout.2.2

theorem polytime : BitMachine.Polytime result := by
  refine ⟨machine, 2, 1, ?_⟩
  intro input
  simpa [Nat.mul_add] using outputs input

theorem header_regressions :
    result [] = [false] ∧ result [false] = [true] ∧
      result [true] = [false] ∧ result [true, false, false] = [false] ∧
      result [true, true, false, true] = [true, true] ∧
      result [true, false, true, true, false] = [true, false, true] := by decide

end EthInapproximability.CurrentPaper.ProtocolBinaryHeader
