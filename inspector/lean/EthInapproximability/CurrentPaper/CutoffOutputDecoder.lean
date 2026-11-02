import EthInapproximability.CurrentPaper.BitMachineEncoding
import EthInapproximability.CurrentPaper.BitMachineSubroutine
import EthInapproximability.CurrentPaper.CutoffBitMachineCore
import EthInapproximability.CurrentPaper.ProtocolBoundedUnary

/-!
# Decoding the cutoff program's physical output bits

Source: frozen v8 `05-iteration.tex`, bounded cutoff tests. Each encoded
data symbol is `(bit,false)`; a non-data pair ends the number. This finite
three-stack machine extracts the ordinary little-endian binary word in
linear time, on every input, including malformed or partial output. Its
value agrees exactly with the cutoff clock's existing `decodedNat`.
-/

namespace EthInapproximability.CurrentPaper.CutoffOutputDecoder

open Turing Turing.TM2.Stmt
open BitMachine BitMachineEncoding

abbrev Control := Option Bool × Option Bool
abbrev Config := TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 2) Control

def cfg (l : Option (Fin 2)) (v : Control) (input work out : List Bool) : Config :=
  ⟨l, v, ![input, work, out]⟩

def program : Fin 2 → TM2.Stmt (fun _ : Fin 3 => Bool) (Fin 2) Control
  | 0 => pop 0 (fun v b => (b, v.2))
      (pop 0 (fun v b => (v.1, b))
        (branch (fun v => v.1.isSome && v.2 == some false)
          (push 1 (fun v => v.1.getD false) (goto (fun _ => 0)))
          (goto (fun _ => 1))))
  | 1 => pop 1 (fun v b => (b, v.2))
      (branch (fun v => v.1.isSome)
        (push 2 (fun v => v.1.getD false) (goto (fun _ => 1))) halt)

def run (n : ℕ) (c : Config) : Config := ((advance program)^[n]) c

def bits : List Bool → List Bool
  | a :: false :: rest => a :: bits rest
  | _ => []

def remainder : List Bool → List Bool
  | _ :: false :: rest => remainder rest
  | _ :: true :: rest => rest
  | _ => []

def scans : List Bool → ℕ
  | _ :: false :: rest => scans rest + 1
  | _ => 1

theorem scan_data (a : Bool) (rest work out : List Bool) (v : Control) :
    advance program (cfg (some 0) v (a :: false :: rest) work out) =
      cfg (some 0) (some a, some false) rest (a :: work) out := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]
  funext k
  fin_cases k <;> rfl

theorem scan_end (rest work out : List Bool) (v : Control)
    (h : ∀ a tail, rest ≠ a :: false :: tail) :
    ∃ w, advance program (cfg (some 0) v rest work out) =
      cfg (some 1) w (remainder rest) work out := by
  cases rest with
  | nil =>
      refine ⟨(none, none), ?_⟩
      simp [advance, program, cfg, TM2.step, TM2.stepAux, remainder]
  | cons a tail =>
      cases tail with
      | nil =>
          refine ⟨(some a, none), ?_⟩
          simp [advance, program, cfg, TM2.step, TM2.stepAux, remainder]
          funext k
          fin_cases k <;> rfl
      | cons b tail =>
          cases b with
          | false => exact (h a tail rfl).elim
          | true =>
              refine ⟨(some a, some true), ?_⟩
              simp [advance, program, cfg, TM2.step, TM2.stepAux, remainder]
              funext k
              fin_cases k <;> rfl

theorem scan_run (input work out : List Bool) (v : Control) :
    ∃ w, run (scans input) (cfg (some 0) v input work out) =
      cfg (some 1) w (remainder input) ((bits input).reverse ++ work) out := by
  induction input using bits.induct generalizing work v with
  | case1 a rest ih =>
      obtain ⟨w, hw⟩ := ih (a :: work) (some a, some false)
      refine ⟨w, ?_⟩
      simp only [scans, run, Function.iterate_succ_apply, scan_data]
      simpa only [run, bits, remainder, List.reverse_cons, List.append_assoc,
        List.singleton_append] using hw
  | case2 input h =>
      obtain ⟨w, hw⟩ := scan_end input work out v h
      refine ⟨w, ?_⟩
      have hb : bits input = [] := by cases input with
        | nil => rfl
        | cons a tail => cases tail with
          | nil => rfl
          | cons b tail => cases b with
            | false => exact (h a tail rfl).elim
            | true => rfl
      have hs : scans input = 1 := by cases input with
        | nil => rfl
        | cons a tail => cases tail with
          | nil => rfl
          | cons b tail => cases b with
            | false => exact (h a tail rfl).elim
            | true => rfl
      simpa only [hs, run, Function.iterate_one, hb, List.reverse_nil, List.nil_append] using hw

theorem reverse_run (work input out : List Bool) (v : Control) :
    ∃ w, run (work.length + 1) (cfg (some 1) v input work out) =
      cfg none w input [] (work.reverse ++ out) := by
  induction work generalizing v out with
  | nil =>
      refine ⟨(none, v.2), ?_⟩
      simp [run, advance, program, cfg, TM2.step, TM2.stepAux]
  | cons b work ih =>
      obtain ⟨w, hw⟩ := ih (b :: out) (some b, v.2)
      refine ⟨w, ?_⟩
      have hs : advance program (cfg (some 1) v input (b :: work) out) =
          cfg (some 1) (some b, v.2) input work (b :: out) := by
        simp [advance, program, cfg, TM2.step, TM2.stepAux]
        funext k
        fin_cases k <;> rfl
      simp only [List.length_cons, run, Function.iterate_succ_apply, hs]
      simpa only [run, List.reverse_cons, List.append_assoc, List.singleton_append] using hw

theorem decoder_run (input out : List Bool) (v : Control) :
    ∃ w, run (scans input + (bits input).length + 1) (cfg (some 0) v input [] out) =
      cfg none w (remainder input) [] (bits input ++ out) := by
  obtain ⟨v', hs⟩ := scan_run input [] out v
  rw [List.append_nil] at hs
  obtain ⟨w, hr⟩ := reverse_run (bits input).reverse (remainder input) out v'
  refine ⟨w, ?_⟩
  rw [List.length_reverse, List.reverse_reverse] at hr
  rw [Nat.add_assoc]
  change ((advance program)^[scans input + ((bits input).length + 1)]) _ = _
  rw [Nat.add_comm (scans input), Function.iterate_add_apply,
    show ((advance program)^[scans input]) _ = _ from hs]
  exact hr

theorem decoder_time (input : List Bool) : scans input + (bits input).length + 1 ≤ input.length + 2 := by
  induction input using bits.induct with
  | case1 a rest ih => simp only [scans, bits, List.length_cons]; omega
  | case2 input h =>
      cases input with
      | nil => decide
      | cons a tail => cases tail with
        | nil => simp [scans, bits]
        | cons b tail => cases b with
          | false => exact (h a tail rfl).elim
          | true => simp [scans, bits]

theorem bits_value (input : List Bool) :
    EncodedCommunication.bitsValue (bits input) = CutoffBitMachine.decodedNat input := by
  induction input using bits.induct with
  | case1 a rest ih => simp only [bits, EncodedCommunication.bitsValue,
      CutoffBitMachine.decodedNat, ih]
  | case2 input h =>
      cases input with
      | nil => rfl
      | cons a tail => cases tail with
        | nil => rfl
        | cons b tail => cases b with
          | false => exact (h a tail rfl).elim
          | true => rfl

noncomputable def machine : Machine := ofFinite (0 : Fin 3) 2 (0 : Fin 2)
  (none, none) program

noncomputable def encode (c : Config) : machine.Config :=
  renameCfg (Fintype.equivFin (Fin 3)) (Fintype.equivFin (Fin 2))
    (Fintype.equivFin Control) c

theorem machine_init (input : List Bool) :
    machine.init input = encode (cfg (some 0) (none, none) input [] []) := by
  have hi := ofFinite_init (0 : Fin 3) 2 (0 : Fin 2) (none, none) program input
  change machine.init input = _ at hi
  rw [hi]
  unfold encode
  congr 1
  unfold rawInit cfg
  congr 1
  funext k
  fin_cases k <;> simp

theorem outputs_all (input : List Bool) : machine.OutputsWithin input (bits input) (input.length + 2) := by
  obtain ⟨v, hr⟩ := decoder_run input [] (none, none)
  refine ⟨scans input + (bits input).length + 1, decoder_time input, ?_, ?_⟩
  all_goals
    rw [machine_init]
    have heq := ofFinite_run (0 : Fin 3) 2 (0 : Fin 2) (none, none) program
      (cfg (some 0) (none, none) input [] []) (scans input + (bits input).length + 1)
    change machine.run _ (encode _) = encode (run _ _) at heq
    rw [heq, hr]
  · rfl
  · simp only [encode, renameCfg, cfg, machine, ofFinite]
    have h := congrArg (![remainder input, [], bits input ++ []])
      ((Fintype.equivFin (Fin 3)).symm_apply_apply 2)
    exact h.trans (by simp)

theorem bits_polytime : Polytime bits := by
  refine ⟨machine, 2, 1, fun input => ?_⟩
  exact outputsWithin_mono _ (outputs_all input) (by simp only [pow_one]; omega)

end EthInapproximability.CurrentPaper.CutoffOutputDecoder
