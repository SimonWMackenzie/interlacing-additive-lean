import EthInapproximability.CurrentPaper.ProtocolBinaryHeader
import EthInapproximability.CurrentPaper.BitMachineInline
import EthInapproximability.CurrentPaper.BitMachineClearBank

/-!
Remove one canonical binary count field physically.  The parser reads only
the first field and leaves the tail on stack 0; malformed fields take a
bounded clearing path and return the empty word.
-/

namespace CurrentAdditive.CodeDStripHeaderV2

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

inductive Admin where
  | afterHeader | rejectClear
  deriving DecidableEq, Fintype

abbrev Label := ProtocolBinaryHeader.Label ⊕ Admin
abbrev Control := ProtocolBinaryHeader.Control × Option Bool
abbrev Config := TM2.Cfg (fun _ : Fin 3 => Bool) Label Control

def program : Label → TM2.Stmt (fun _ : Fin 3 => Bool) Label Control
  | .inl l => BitMachineInline.stmt Sum.inl (fun v => (v,none)) Prod.fst
      (some (.inr .afterHeader)) (ProtocolBinaryHeader.program l)
  | .inr .afterHeader => pop 2 (fun v b => (v.1,b))
      (branch (fun v => v.2 == some true) halt
        (goto (fun _ => .inr .rejectClear)))
  | .inr .rejectClear => pop 0 (fun v b => (v.1,b))
      (branch (fun v => v.2.isSome)
        (goto (fun _ => .inr .rejectClear)) halt)

def result (input : List Bool) : List Bool :=
  match ProtocolBinaryHeader.readChecked none input with
  | none => []
  | some (_, tail) => tail

noncomputable def machine : BitMachine.Machine :=
  ofFinite (0 : Fin 3) 0 (.inl .scan) ((none,none),none) program

def cfg (l : Option Label) (v : Control) (input saved target : List Bool) : Config :=
  ⟨l,v,ProtocolBinaryHeader.stackContents input saved target⟩

theorem initial_eq (input : List Bool) :
    rawInit (0 : Fin 3) (.inl .scan : Label) ((none,none),none) input =
      cfg (some (.inl .scan)) ((none,none),none) input [] [] := by
  unfold rawInit cfg
  congr 1
  funext k
  fin_cases k <;> rfl

theorem header_source_step_le (c : TM2.Cfg (fun _ : Fin 3 => Bool)
    ProtocolBinaryHeader.Label ProtocolBinaryHeader.Control) :
    ((advance ProtocolBinaryHeader.program c).stk 0).length ≤ (c.stk 0).length := by
  rcases c with ⟨l,v,S⟩
  have htail : ((S 0).tail).length ≤ (S 0).length := by
    cases S 0 <;> simp
  cases l with
  | none => simp [advance]
  | some l =>
      cases l
      · cases h0 : (S 0).head?.isSome <;>
          cases h1 : (S 0).head?.getD false <;>
          cases h2 : decide (v.1 = some false) <;>
          simp [advance, ProtocolBinaryHeader.program,
            ProtocolBinaryHeader.failure, TM2.step, TM2.stepAux,
            h0, h1, h2, Function.update_apply, htail]
      · cases h0 : (S 0).head?.isSome <;>
          simp [advance, ProtocolBinaryHeader.program,
            ProtocolBinaryHeader.failure, TM2.step, TM2.stepAux,
            h0, Function.update_apply, htail]
      · cases h0 : (S 1).head?.isSome <;>
          simp [advance, ProtocolBinaryHeader.program,
            ProtocolBinaryHeader.failure, TM2.step, TM2.stepAux,
            h0, Function.update_apply]

theorem header_source_run_le
    (c : TM2.Cfg (fun _ : Fin 3 => Bool)
      ProtocolBinaryHeader.Label ProtocolBinaryHeader.Control) (t : Nat) :
    ((ProtocolBinaryHeader.run t c).stk 0).length ≤ (c.stk 0).length := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [ProtocolBinaryHeader.run, Function.iterate_succ_apply']
      exact (header_source_step_le _).trans ih

theorem parse_run (input : List Bool) :
    ∃ t ≤ 2*input.length+2,
      ∃ c : TM2.Cfg (fun _ : Fin 3 => Bool)
        ProtocolBinaryHeader.Label ProtocolBinaryHeader.Control,
      ((advance program)^[t])
        (cfg (some (.inl .scan)) ((none,none),none) input [] []) =
      BitMachineInline.cfg Sum.inl (fun v => (v,none))
        (some (.inr .afterHeader)) c ∧
      ProtocolBinaryHeader.Post none input [] [] c ∧
      (c.stk 0).length ≤ input.length := by
  obtain ⟨t,ht,hp⟩ := ProtocolBinaryHeader.scan_correct input none none [] []
  obtain ⟨u,hu,hr⟩ := BitMachineInline.outputs Sum.inl
    (fun v : ProtocolBinaryHeader.Control => (v,none)) Prod.fst
    (fun _ => rfl) (some (.inr .afterHeader))
    ProtocolBinaryHeader.program program (fun _ => rfl)
    (ProtocolBinaryHeader.cfg (some .scan) (none,none) input [] []) t hp.1
  refine ⟨u, hu.trans ht, ProtocolBinaryHeader.run t
    (ProtocolBinaryHeader.cfg (some .scan) (none,none) input [] []), ?_, hp, ?_⟩
  · simpa only [cfg, ProtocolBinaryHeader.cfg, BitMachineInline.cfg] using hr
  · exact (header_source_run_le _ t).trans_eq (by rfl)

theorem after_success (c : TM2.Cfg (fun _ : Fin 3 => Bool)
    ProtocolBinaryHeader.Label ProtocolBinaryHeader.Control)
    (hc : c.l = none) (bs : List Bool) (hflag : c.stk 2 = true :: bs) :
    advance program
      (BitMachineInline.cfg Sum.inl (fun v => (v,none))
        (some (.inr .afterHeader)) c) =
    ⟨none, (c.var,some true), Function.update c.stk 2 bs⟩ := by
  simp [BitMachineInline.cfg, hc, advance, program, TM2.step,
    TM2.stepAux, hflag]

theorem after_failure (c : TM2.Cfg (fun _ : Fin 3 => Bool)
    ProtocolBinaryHeader.Label ProtocolBinaryHeader.Control)
    (hc : c.l = none) (bs : List Bool) (hflag : c.stk 2 = false :: bs) :
    advance program
      (BitMachineInline.cfg Sum.inl (fun v => (v,none))
        (some (.inr .afterHeader)) c) =
    ⟨some (.inr .rejectClear), (c.var,some false),
      Function.update c.stk 2 bs⟩ := by
  simp [BitMachineInline.cfg, hc, advance, program, TM2.step,
    TM2.stepAux, hflag]

theorem clear_run (v : Control) (S : Fin 3 → List Bool) :
    ((advance program)^[(S 0).length + 1])
      (⟨some (.inr .rejectClear), v, S⟩ : Config) =
    ⟨none, (v.1,none), Function.update S 0 []⟩ := by
  induction h : S 0 generalizing v S with
  | nil =>
      simp [h, advance, program, TM2.step, TM2.stepAux]
  | cons b rest ih =>
      have hs : advance program
          (⟨some (.inr .rejectClear), v, S⟩ : Config) =
          ⟨some (.inr .rejectClear), (v.1,some b),
            Function.update S 0 rest⟩ := by
        simp [advance, program, TM2.step, TM2.stepAux, h]
      simp only [h, List.length_cons]
      rw [show rest.length + 1 + 1 = (rest.length + 1) + 1 by rfl,
        Function.iterate_succ_apply, hs]
      have hr := ih (v := (v.1,some b))
        (S := Function.update S 0 rest) (by simp)
      simpa [Function.update_idem] using hr

theorem outputs_valid (n : Nat) (tail : List Bool) :
    machine.OutputsWithin
      (EthInapproximability.CurrentPaper.EncodedCommunication.natField n ++ tail)
      tail
      (2*(EthInapproximability.CurrentPaper.EncodedCommunication.natField n ++ tail).length+3) := by
  let input := EthInapproximability.CurrentPaper.EncodedCommunication.natField n ++ tail
  obtain ⟨t,ht,c,hpc,hpost,_⟩ := parse_run input
  have hr : ProtocolBinaryHeader.readChecked none input =
      some (n.bits,tail) := by
    rw [ProtocolBinaryHeader.readChecked_spec]
    simp [input, EthInapproximability.CurrentPaper.EncodedCommunication.natField,
      EthInapproximability.CurrentPaper.EncodedCommunication.readField_append,
      ProtocolBinaryHeader.canonicalFrom_none,
      ProtocolBinaryHeader.canonical_of_bits]
  have hc : c.l = none := hpost.1
  have hp := hpost.2
  simp only [hr, List.reverse_nil, List.nil_append, List.append_nil] at hp
  obtain ⟨htail, _, hflag⟩ := hp
  have hs := after_success c hc n.bits hflag
  apply outputsWithin_of_raw_run (0 : Fin 3) 0 (.inl .scan : Label)
    ((none,none),none) program input tail (t+1)
    (2*input.length+3) (by omega)
  · rw [initial_eq]
    simp only [show t+1 = 1+t by omega, Function.iterate_add_apply, hpc,
      Function.iterate_one, hs]
  · rw [initial_eq]
    simp only [show t+1 = 1+t by omega, Function.iterate_add_apply, hpc,
      Function.iterate_one, hs]
    simpa [Function.update_of_ne (show (0 : Fin 3) ≠ 2 by decide)] using htail

theorem outputs_total (input : List Bool) :
    machine.OutputsWithin input (result input) (3*(input.length+1)+4) := by
  obtain ⟨t,ht,c,hpc,hpost,hsize⟩ := parse_run input
  have hc : c.l = none := hpost.1
  cases hd : ProtocolBinaryHeader.readChecked none input with
  | none =>
      have hflag : c.stk 2 = [false] := by
        simpa [ProtocolBinaryHeader.Post, hd] using hpost.2
      have hs := after_failure c hc [] hflag
      let S := Function.update c.stk 2 []
      have hlen : (S 0).length ≤ input.length := by
        simpa [S, Function.update_of_ne (show (0 : Fin 3) ≠ 2 by decide)] using hsize
      have hclear := clear_run (c.var,some false) S
      have hfirst : ((advance program)^[t+1])
          (cfg (some (.inl .scan)) ((none,none),none) input [] []) =
          (⟨some (.inr .rejectClear), (c.var,some false), S⟩ : Config) := by
        rw [show t+1=1+t by omega, Function.iterate_add_apply, hpc,
          Function.iterate_one, hs]
      have hfull : ((advance program)^[t+1+((S 0).length+1)])
          (cfg (some (.inl .scan)) ((none,none),none) input [] []) =
          ⟨none, (c.var,none), Function.update S 0 []⟩ := by
        rw [show t+1+((S 0).length+1) = ((S 0).length+1)+(t+1) by omega,
          Function.iterate_add_apply, hfirst, hclear]
      apply outputsWithin_of_raw_run (0 : Fin 3) 0 (.inl .scan : Label)
        ((none,none),none) program input (result input)
        (t+1+((S 0).length+1)) (3*(input.length+1)+4) (by omega)
      · rw [initial_eq]
        rw [hfull]
      · rw [initial_eq]
        rw [hfull]
        simp [result, hd]
  | some pair =>
      rcases pair with ⟨bs,tail⟩
      have hp := hpost.2
      simp only [hd, List.reverse_nil, List.nil_append,
        List.append_nil] at hp
      obtain ⟨htail, _, hflag⟩ := hp
      have hs := after_success c hc bs hflag
      apply outputsWithin_of_raw_run (0 : Fin 3) 0 (.inl .scan : Label)
        ((none,none),none) program input (result input)
        (t+1) (3*(input.length+1)+4) (by omega)
      · rw [initial_eq]
        simp only [show t+1=1+t by omega, Function.iterate_add_apply,
          hpc, Function.iterate_one, hs]
      · rw [initial_eq]
        simp only [show t+1=1+t by omega, Function.iterate_add_apply,
          hpc, Function.iterate_one, hs]
        simpa [result, hd,
          Function.update_of_ne (show (0 : Fin 3) ≠ 2 by decide)] using htail

theorem polytime : BitMachine.Polytime result := by
  refine ⟨machine,7,1,?_⟩
  intro input
  have h := outputs_total input
  apply BitMachine.outputsWithin_mono _ h
  simp only [pow_one]
  omega

#print axioms after_success
#print axioms after_failure
#print axioms clear_run
#print axioms outputs_valid
#print axioms outputs_total
#print axioms polytime

end CurrentAdditive.CodeDStripHeaderV2
