import EthInapproximability.CurrentPaper.BinarySuccessorMachine
import EthInapproximability.CurrentPaper.BitMachineBroadcast
import EthInapproximability.CurrentPaper.SourceListEncoding
import EthInapproximability.CurrentPaper.BitMachineEncoding
import EthInapproximability.CurrentPaper.UnaryBinaryEncoding
import Mathlib.Tactic

/-! Physical successor of the first canonical binary count field. -/

namespace CurrentAdditive.FeatureCountFieldSuccessor

open EthInapproximability.CurrentPaper
open Turing TM2.Stmt BitMachineEncoding
open EthInapproximability.CurrentPaper.EncodedCommunication

inductive Label where
  | read | bit | stop | reverse | done
  deriving DecidableEq, Fintype

abbrev Stack := Fin 3
abbrev Control := Bool × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .read => pop 0 (fun v b => (v.1,b))
      (branch (fun v => v.2.isSome)
        (branch (fun v => v.2.getD false) (goto (fun _ => .bit))
          (goto (fun _ => .stop))) halt)
  | .bit => pop 0 (fun v b => (v.1,b))
      (branch (fun v => v.2.isSome)
        (push 1 (fun _ => true)
          (push 1 (fun v => xor v.1 (v.2.getD false))
            (load (fun v => (v.1 && v.2.getD false,none))
              (goto (fun _ => .read))))) halt)
  | .stop => branch Prod.fst
      (push 1 (fun _ => true)
        (push 1 (fun _ => true)
          (push 1 (fun _ => false) (goto (fun _ => .reverse)))))
      (push 1 (fun _ => false) (goto (fun _ => .reverse)))
  | .reverse => BitMachineBroadcast.scanStep 1 2 .reverse .done
  | .done => halt

def cfg (l : Option Label) (v : Control)
    (source accumulator output : List Bool) : Config :=
  ⟨l,v,![source,accumulator,output]⟩

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add (t u : Nat) (c : Config) :
    run (t+u) c = run u (run t c) := by
  simpa only [run, Nat.add_comm] using
    Function.iterate_add_apply (advance program) u t c

def addCarry (carry : Bool) (q : List Bool) : List Bool :=
  if carry then BinarySuccessorMachine.successor q else q

theorem addCarry_cons (carry b : Bool) (q : List Bool) :
    addCarry carry (b::q) =
      xor carry b :: addCarry (carry && b) q := by
  cases carry <;> cases b <;> rfl

theorem addCarry_empty (carry : Bool) :
    addCarry carry [] = if carry then [true] else [] := by
  cases carry <;> rfl

theorem read_step (carry b : Bool) (q acc output : List Bool) :
    run 2 (cfg (some .read) (carry,none)
      (true :: b :: q) acc output) =
      cfg (some .read) (carry && b,none)
        q (xor carry b :: true :: acc) output := by
  simp [run, advance, TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

theorem stop_step (carry : Bool) (suffix acc output : List Bool) :
    run 2 (cfg (some .read) (carry,none)
      (false :: suffix) acc output) =
      cfg (some .reverse) (carry,some false) suffix
        ((field (addCarry carry [])).reverse ++ acc) output := by
  cases carry <;>
    simp [run, advance, TM2.step, TM2.stepAux, program, cfg,
      addCarry, BinarySuccessorMachine.successor, field] <;>
    (funext k; fin_cases k <;> simp)

theorem header_run (carry : Bool) (q suffix acc output : List Bool) :
    run (2*q.length+2)
      (cfg (some .read) (carry,none) (field q ++ suffix) acc output) =
      cfg (some .reverse) (carry && q.all id,some false) suffix
        ((field (addCarry carry q)).reverse ++ acc) output := by
  induction q generalizing carry acc with
  | nil =>
      simpa [field, addCarry_empty] using stop_step carry suffix acc output
  | cons b q ih =>
      rw [show 2*(b::q).length+2 = 2+(2*q.length+2) by
        simp only [List.length_cons]; omega, run_add]
      simp only [field, List.cons_append]
      rw [read_step]
      rw [ih (carry := carry && b)
        (acc := xor carry b :: true :: acc)]
      have ha := addCarry_cons carry b q
      simp only [ha, field, List.reverse_cons,
        List.append_assoc, List.all_cons]
      congr 1
      cases carry <;> cases b <;> simp

theorem reverse_run (source acc output : List Bool) (v : Control) :
    run (acc.length+2) (cfg (some .reverse) v source acc output) =
      cfg none (v.1,none) source [] (acc.reverse ++ output) := by
  have h := BitMachineBroadcast.scan_run program (1 : Stack) 2
    (by decide) .reverse .done rfl v.1 v.2 acc output
    (![source,acc,output] : Stack → List Bool)
  have he : BitMachineBroadcast.contents (1 : Stack) 2
      (![source,acc,output] : Stack → List Bool) acc output =
      (![source,acc,output] : Stack → List Bool) := by
    funext k
    fin_cases k <;> simp [BitMachineBroadcast.contents]
  rw [he] at h
  have hd : advance program
      (cfg (some .done) (v.1,none) source [] (acc.reverse ++ output)) =
      cfg none (v.1,none) source [] (acc.reverse ++ output) := rfl
  rw [show acc.length+2 = (acc.length+1)+1 by omega,
    run_add]
  change run 1 (run (acc.length+1) _) = _
  have hs : run (acc.length+1)
      (cfg (some .reverse) v source acc output) =
      cfg (some .done) (v.1,none) source [] (acc.reverse ++ output) := by
    have hb : BitMachineBroadcast.contents (1 : Stack) 2
        (![source,acc,output] : Stack → List Bool)
        [] (acc.reverse ++ output) =
        (![source,[],acc.reverse ++ output] : Stack → List Bool) := by
      funext k
      fin_cases k <;> simp [BitMachineBroadcast.contents]
    rw [hb] at h
    simpa only [run, BitMachineBroadcast.run, cfg] using h
  rw [hs]
  exact hd

theorem canonical_run (n : Nat) (suffix : List Bool) :
    ∃ t ≤ 6*((natField n ++ suffix).length+1),
      let c := run t (cfg (some .read) (true,none)
        (natField n ++ suffix) [] [])
      c.l = none ∧ c.stk 0 = suffix ∧
        c.stk 2 = natField (n+1) := by
  let q := n.bits
  have hh := header_run true q suffix [] []
  have ha : addCarry true q = (n+1).bits := by
    simpa [addCarry] using BinarySuccessorMachine.successor_bits n
  rw [ha] at hh
  let acc := (field (n+1).bits).reverse
  have hr := reverse_run suffix acc [] (true && q.all id,some false)
  refine ⟨2*q.length+2 + (acc.length+2), ?_, ?_⟩
  · have hlen := EncodedCommunication.field_length q
    have hsucc : (n+1).bits.length ≤ q.length+1 := by
      simpa only [q, ← BinarySuccessorMachine.successor_bits n] using
        UnaryBinaryEncoding.successor_length n.bits
    have hq : q.length = n.bits.length := rfl
    simp only [natField, List.length_append, acc, List.length_reverse,
      field_length]
    omega
  · rw [run_add]
    change (run (acc.length+2)
      (run (2*q.length+2)
        (cfg (some .read) (true,none) (field q ++ suffix) [] []))).l = none ∧
      (run (acc.length+2)
        (run (2*q.length+2)
          (cfg (some .read) (true,none) (field q ++ suffix) [] []))).stk 0 =
        suffix ∧
      (run (acc.length+2)
        (run (2*q.length+2)
          (cfg (some .read) (true,none) (field q ++ suffix) [] []))).stk 2 =
        field (n+1).bits
    simp only [hh, List.append_nil]
    change (run (acc.length+2)
      (cfg (some .reverse) (true && q.all id,some false)
        suffix acc [])).l = none ∧
      (run (acc.length+2)
        (cfg (some .reverse) (true && q.all id,some false)
          suffix acc [])).stk 0 = suffix ∧
      (run (acc.length+2)
        (cfg (some .reverse) (true && q.all id,some false)
          suffix acc [])).stk 2 = field (n+1).bits
    rw [hr]
    simp [acc, cfg]

theorem malformed_run (input acc output : List Bool)
    (hbad : readField input = none) (carry : Bool) :
    ∃ t ≤ 2*input.length+2,
      (run t (cfg (some .read) (carry,none) input acc output)).l = none ∧
      (run t (cfg (some .read) (carry,none) input acc output)).stk 2 = output := by
  induction input using readField.induct generalizing carry acc with
  | case1 =>
      refine ⟨1, by simp, ?_⟩
      simp [run, cfg, advance, TM2.step, TM2.stepAux, program]
  | case2 suffix =>
      simp [readField] at hbad
  | case3 =>
      refine ⟨2, by simp, ?_⟩
      simp [run, cfg, advance, TM2.step, TM2.stepAux, program]
  | case4 b rest ih =>
      have hrest : readField rest = none := by
        cases hr : readField rest with
        | none => rfl
        | some pair =>
            rcases pair with ⟨q,suffix⟩
            simp [readField, hr] at hbad
      obtain ⟨t, ht, hh⟩ := ih
        (carry := carry && b) (acc := xor carry b :: true :: acc) hrest
      refine ⟨2+t, by simp; omega, ?_⟩
      rw [run_add, read_step]
      exact hh

theorem parsed_run (q suffix : List Bool) :
    ∃ t ≤ 6*((field q ++ suffix).length+1),
      let z := run t (cfg (some .read) (true,none)
        (field q ++ suffix) [] [])
      z.l = none ∧ z.stk 2 = field (BinarySuccessorMachine.successor q) := by
  let acc := (field (addCarry true q)).reverse
  have hh := header_run true q suffix [] []
  have hr := reverse_run suffix acc [] (true && q.all id,some false)
  refine ⟨2*q.length+2 + (acc.length+2), ?_, ?_⟩
  · have hlen := EncodedCommunication.field_length q
    have hsucc := UnaryBinaryEncoding.successor_length q
    simp only [List.length_append, acc, List.length_reverse,
      EncodedCommunication.field_length]
    simp only [addCarry, if_true] at *
    omega
  · rw [run_add]
    simp only [hh, List.append_nil]
    change (run (acc.length+2)
      (cfg (some .reverse) (true && q.all id,some false)
        suffix acc [])).l = none ∧
      (run (acc.length+2)
        (cfg (some .reverse) (true && q.all id,some false)
          suffix acc [])).stk 2 = field (BinarySuccessorMachine.successor q)
    rw [hr]
    simp [acc, addCarry, cfg]

def result (input : List Bool) : List Bool :=
  match readField input with
  | none => []
  | some (q,_) => field (BinarySuccessorMachine.successor q)

noncomputable def machine : BitMachine.Machine :=
  ofFinite (0 : Stack) 2 .read (true,none) program

theorem raw_initial (input : List Bool) :
    rawInit (0 : Stack) .read (true,none) input =
      cfg (some .read) (true,none) input [] [] := by
  unfold rawInit cfg
  congr 1
  funext k
  fin_cases k <;> simp

theorem outputsWithin (input : List Bool) :
    machine.OutputsWithin input (result input) (6*(input.length+1)) := by
  cases hr : readField input with
  | none =>
      obtain ⟨t,ht,hh,hout⟩ := malformed_run input [] [] hr true
      exact outputsWithin_of_raw_run 0 2 .read (true,none) program
        input (result input) t (6*(input.length+1))
        (by omega) (by simpa [raw_initial, run] using hh)
        (by simpa [raw_initial, run, result, hr] using hout)
  | some pair =>
      rcases pair with ⟨q,suffix⟩
      have hi := readField_sound hr
      obtain ⟨t,ht,hh,hout⟩ := parsed_run q suffix
      have hinput : field q ++ suffix = input := hi
      exact outputsWithin_of_raw_run 0 2 .read (true,none) program
        input (result input) t (6*(input.length+1))
        (by simpa [hinput] using ht)
        (by simpa [raw_initial, run, ← hinput] using hh)
        (by simpa [raw_initial, run, result, ← hinput,
          readField_append] using hout)

theorem canonical_outputs (n : Nat) (suffix : List Bool) :
    machine.OutputsWithin (natField n ++ suffix) (natField (n+1))
      (6*((natField n ++ suffix).length+1)) := by
  have h := outputsWithin (natField n ++ suffix)
  simpa [result, natField, readField_append,
    BinarySuccessorMachine.successor_bits] using h

#print axioms canonical_run
#print axioms malformed_run
#print axioms outputsWithin
#print axioms canonical_outputs

end CurrentAdditive.FeatureCountFieldSuccessor
