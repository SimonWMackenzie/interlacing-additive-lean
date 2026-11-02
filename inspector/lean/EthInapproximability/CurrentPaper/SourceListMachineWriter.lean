import EthInapproximability.CurrentPaper.UnaryBinaryEncoding
import EthInapproximability.CurrentPaper.BitMachineBroadcast

/-!
# Literal length framing of a Boolean payload

Source: frozen v8 `06-eth.tex`, ordered source-output lists. A physical
copy feeds the proved length-to-binary counter; a fixed controller then
writes the canonical length field and, optionally, the original payload.
No natural-number length or encoding function is evaluated by an instruction.
-/

namespace EthInapproximability.CurrentPaper.SourceListMachineWriter

open Turing TM2.Stmt BitMachine BitMachineEncoding BitMachineComposition
open EncodedCommunication

inductive Admin where
  | scan | restore | header | payload | finish | done
  deriving DecidableEq, Fintype

variable (M : Machine)

abbrev Stack := Fin M.stackCount ⊕ Fin 4
abbrev Label := Fin M.labelCount ⊕ Admin
abbrev Control := Fin M.controlCount × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack M => Bool) (Label M) (Control M)

def program (withPayload : Bool) : Label M → TM2.Stmt (fun _ : Stack M => Bool) (Label M) (Control M)
  | .inl l => liftStmt (some .header) (M.program l)
  | .inr .scan => BitMachineBroadcast.scanStep (.inr 0) (.inr 1) (.inr .scan) (.inr .restore)
  | .inr .restore => BitMachineBroadcast.restoreStep (.inr 1) [.inr 0, .inl M.input]
      (.inr .restore) (.inl M.start)
  | .inr .header => pop (.inl M.output) (fun v b => (v.1,b))
      (branch (fun v => v.2.isSome)
        (push (.inr 2) (fun _ => true)
          (push (.inr 2) (fun v => v.2.getD false) (goto (fun _ => .inr .header))))
        (push (.inr 2) (fun _ => false)
          (load (fun v => (v.1,none))
            (goto (fun _ => .inr (if withPayload then .payload else .finish))))))
  | .inr .payload => BitMachineBroadcast.scanStep (.inr 0) (.inr 2) (.inr .payload) (.inr .finish)
  | .inr .finish => BitMachineBroadcast.scanStep (.inr 2) (.inr 3) (.inr .finish) (.inr .done)
  | .inr .done => halt

def foreign (payload saved revout output : List Bool) : Fin 4 → List Bool :=
  ![payload,saved,revout,output]

def cfg (l : Option (Label M)) (v : Control M) (S : Fin M.stackCount → List Bool)
    (payload saved revout output : List Bool) : Config M :=
  ⟨l,v,Sum.elim S (foreign payload saved revout output)⟩

def run (withPayload : Bool) (t : ℕ) (c : Config M) :=
  ((advance (program M withPayload))^[t]) c

theorem run_step (withPayload : Bool) {c d : Config M}
    (h : advance (program M withPayload) c = d) (t : ℕ) :
    run M withPayload (t+1) c = run M withPayload t d :=
  (Function.iterate_succ_apply _ _ _).trans (congrArg (run M withPayload t) h)

theorem run_add (withPayload : Bool) {c d : Config M} {t : ℕ}
    (h : run M withPayload t c = d) (u : ℕ) :
    run M withPayload (t+u) c = run M withPayload u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

theorem initial_copy (withPayload : Bool) (bits : List Bool) :
    run M withPayload (2*bits.length+2)
      (cfg M (some (.inr .scan)) (M.initial,none) (fun _ => []) bits [] [] []) =
      liftCfg (some .header) none (foreign bits [] [] []) (M.init bits) := by
  let bank : Stack M → List Bool := Sum.elim (fun _ => []) (foreign bits [] [] [])
  have hs := BitMachineBroadcast.scan_run (program M withPayload)
    (Sum.inr (0 : Fin 4) : Stack M) (.inr 1) (by simp)
    (.inr .scan) (.inr .restore) rfl M.initial none bits [] bank
  have hi : BitMachineBroadcast.contents (.inr 0) (.inr 1) bank bits [] = bank := by
    funext k
    cases k with
    | inl k => rfl
    | inr k => fin_cases k <;> rfl
  rw [hi] at hs
  simp only [List.append_nil] at hs
  have hr := BitMachineBroadcast.restore_run (program M withPayload)
    (Sum.inr (1 : Fin 4) : Stack M) [.inr 0, .inl M.input]
    (by simp) (by simp) (.inr .restore) (.inl M.start) rfl
    M.initial none bits.reverse (Function.update bank (.inr 0) [])
  simp only [List.length_reverse, List.reverse_reverse] at hr
  have he := (BitMachineBroadcast.run_add (program M withPayload) hs (bits.length+1)).trans hr
  have hf : Function.update
      (BitMachineBroadcast.prepend [.inr 0, .inl M.input] bits (Function.update bank (.inr 0) []))
      (.inr 1) [] = Sum.elim (M.init bits).stk (foreign bits [] [] []) := by
    funext k
    cases k with
    | inl k =>
      have hmem : (Sum.inl k : Stack M) ∈ [.inr 0, .inl M.input] ↔ k = M.input := by
        simp only [List.mem_cons, List.not_mem_nil, reduceCtorEq, Sum.inl.injEq, false_or, or_false]
      simp only [Function.update_apply, reduceCtorEq, ↓reduceIte, BitMachineBroadcast.prepend,
        hmem, bank, Sum.elim_inl, Machine.init]
      by_cases hk : k = M.input <;> simp only [hk, ↓reduceIte, List.append_nil]
    | inr k =>
      have hmem : (Sum.inr k : Stack M) ∈ [.inr 0, .inl M.input] ↔ k = 0 := by
        simp only [List.mem_cons, List.not_mem_nil, reduceCtorEq, Sum.inr.injEq, or_false]
      simp only [Function.update_apply, Sum.inr.injEq, BitMachineBroadcast.prepend,
        hmem, bank, Sum.elim_inr]
      by_cases h0 : k = 0
      · subst k
        have h01 : (0 : Fin 4) ≠ 1 := by decide
        simp only [h01, ↓reduceIte, List.append_nil]
        rfl
      · by_cases h1 : k = 1
        · subst k
          simp only [↓reduceIte]
          rfl
        · simp only [h0, h1, ↓reduceIte]
  rw [hf] at he
  simpa only [run, BitMachineBroadcast.run, cfg, liftCfg, Machine.init,
    Nat.two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he

theorem header_run (withPayload : Bool) (q payload revout output : List Bool)
    (v : Control M) (S : Fin M.stackCount → List Bool) :
    run M withPayload (q.length+1)
      (cfg M (some (.inr .header)) v (Function.update S M.output q) payload [] revout output) =
      cfg M (some (.inr (if withPayload then .payload else .finish))) (v.1,none)
        (Function.update S M.output []) payload [] ((field q).reverse ++ revout) output := by
  induction q generalizing v revout with
  | nil =>
      simp only [List.length_nil, zero_add, run, Function.iterate_one]
      simp only [advance, cfg, TM2.step, program, TM2.stepAux, Sum.elim_inl,
        Function.update_self, List.head?_nil, List.tail_nil, Option.isSome_none,
        cond_false, Option.getD_some, field, List.reverse_singleton, List.singleton_append]
      congr 1
      funext k
      cases k with
      | inl k => by_cases hk : k = M.output <;>
          simp only [Function.update_apply, Sum.inl.injEq, reduceCtorEq,
            Sum.elim_inl, hk, ↓reduceIte]
      | inr k => fin_cases k <;> rfl
  | cons b q ih =>
      have hs : advance (program M withPayload)
          (cfg M (some (.inr .header)) v (Function.update S M.output (b::q)) payload [] revout output) =
          cfg M (some (.inr .header)) (v.1,some b) (Function.update S M.output q)
            payload [] (b::true::revout) output := by
        simp only [advance, cfg, TM2.step, program, TM2.stepAux, Sum.elim_inl,
          Function.update_self, List.head?_cons, List.tail_cons, Option.isSome_some,
          Option.getD_some, cond_true, Option.getD_some]
        congr 1
        funext k
        cases k with
        | inl k => by_cases hk : k = M.output <;>
            simp only [Function.update_apply, Sum.inl.injEq, reduceCtorEq,
              Sum.elim_inl, hk, ↓reduceIte]
        | inr k => fin_cases k <;> rfl
      rw [List.length_cons, run_step M withPayload hs, ih]
      simp only [field, List.reverse_cons, List.append_assoc, List.singleton_append]
      rfl

theorem payload_run (payload revout output : List Bool) (v : Control M)
    (S : Fin M.stackCount → List Bool) :
    run M true (payload.length+1)
      (cfg M (some (.inr .payload)) v S payload [] revout output) =
      cfg M (some (.inr .finish)) (v.1,none) S [] [] (payload.reverse ++ revout) output := by
  have h := BitMachineBroadcast.scan_run (program M true)
    (Sum.inr (0 : Fin 4) : Stack M) (.inr 2) (by simp)
    (.inr .payload) (.inr .finish) rfl v.1 v.2 payload revout
    (Sum.elim S (foreign payload [] revout output))
  have hcfg (xs ys : List Bool) :
      BitMachineBroadcast.contents (.inr 0) (.inr 2)
        (Sum.elim S (foreign payload [] revout output)) xs ys =
      Sum.elim S (foreign xs [] ys output) := by
    funext k
    cases k with
    | inl k => rfl
    | inr k => fin_cases k <;> rfl
  simpa only [run, BitMachineBroadcast.run, cfg, hcfg, Prod.mk.eta] using h

theorem finish_run (withPayload : Bool) (payload revout output : List Bool) (v : Control M)
    (S : Fin M.stackCount → List Bool) :
    run M withPayload (revout.length+2)
      (cfg M (some (.inr .finish)) v S payload [] revout output) =
      cfg M none (v.1,none) S payload [] [] (revout.reverse ++ output) := by
  have h := BitMachineBroadcast.scan_run (program M withPayload)
    (Sum.inr (2 : Fin 4) : Stack M) (.inr 3) (by simp)
    (.inr .finish) (.inr .done) rfl v.1 v.2 revout output
    (Sum.elim S (foreign payload [] revout output))
  have hcfg (xs ys : List Bool) :
      BitMachineBroadcast.contents (.inr 2) (.inr 3)
        (Sum.elim S (foreign payload [] revout output)) xs ys =
      Sum.elim S (foreign payload [] xs ys) := by
    funext k
    cases k with
    | inl k => rfl
    | inr k => fin_cases k <;> rfl
  have hr : run M withPayload (revout.length+1)
      (cfg M (some (.inr .finish)) v S payload [] revout output) =
      cfg M (some (.inr .done)) (v.1,none) S payload [] [] (revout.reverse ++ output) := by
    simpa only [run, BitMachineBroadcast.run, cfg, hcfg, Prod.mk.eta] using h
  rw [show revout.length+2 = (revout.length+1)+1 by omega, run_add M withPayload hr]
  rfl

def framed (withPayload : Bool) (q payload : List Bool) : List Bool :=
  field q ++ if withPayload then payload else []

theorem write_run (withPayload : Bool) (q bits : List Bool) (v : Control M)
    (S : Fin M.stackCount → List Bool) :
    ∃ t ≤ 3*q.length+2*bits.length+5, ∃ c,
      run M withPayload t
        (cfg M (some (.inr .header)) v (Function.update S M.output q) bits [] [] []) = c ∧
      c.l = none ∧ c.stk (.inr 3) = framed withPayload q bits := by
  cases withPayload with
  | false =>
      have hh := header_run M false q bits [] [] v S
      simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil] at hh
      have hf := finish_run M false bits (field q).reverse [] (v.1,none)
        (Function.update S M.output [])
      refine ⟨(q.length+1)+((field q).reverse.length+2), ?_, _,
        (run_add M false hh _).trans hf, rfl, ?_⟩
      · rw [List.length_reverse, field_length]; omega
      · simp only [cfg, Sum.elim_inr, foreign, Matrix.cons_val_three,
          List.reverse_reverse, List.append_nil, framed, Bool.false_eq_true, ↓reduceIte]
        rfl
  | true =>
      have hh := header_run M true q bits [] [] v S
      simp only [Bool.true_eq, ↓reduceIte, List.append_nil] at hh
      have hp := payload_run M bits (field q).reverse [] (v.1,none)
        (Function.update S M.output [])
      have hprefix := (run_add M true hh _).trans hp
      have hf := finish_run M true [] (bits.reverse ++ (field q).reverse) [] (v.1,none)
        (Function.update S M.output [])
      refine ⟨((q.length+1)+(bits.length+1))+((bits.reverse ++ (field q).reverse).length+2),
        ?_, _, (run_add M true hprefix _).trans hf, rfl, ?_⟩
      · simp only [List.length_append, List.length_reverse, field_length]; omega
      · simp only [cfg, Sum.elim_inr, foreign, Matrix.cons_val_three,
          List.reverse_append, List.reverse_reverse, List.append_nil,
          framed, Bool.true_eq, ↓reduceIte]
        rfl

noncomputable def machine (withPayload : Bool) : Machine :=
  ofFinite (Sum.inr (0 : Fin 4) : Stack M) (.inr 3) (.inr .scan)
    (M.initial,none) (program M withPayload)

theorem raw_initial (bits : List Bool) :
    rawInit (Sum.inr (0 : Fin 4) : Stack M) (Sum.inr .scan : Label M)
      (M.initial,none) bits =
      cfg M (some (.inr .scan)) (M.initial,none) (fun _ => []) bits [] [] [] := by
  unfold rawInit cfg
  congr 1
  funext k
  cases k with
  | inl k => rfl
  | inr k => fin_cases k <;> rfl

/-- Every counter transition and every physical copy/framing transition is
charged. The supplied counter is an actual fixed machine, not a length oracle. -/
theorem outputs_of_counter (withPayload : Bool) (bits : List Bool) (bound : ℕ)
    (hcounter : M.OutputsWithin bits bits.length.bits bound) :
    (machine M withPayload).OutputsWithin bits (framed withPayload bits.length.bits bits)
      (bound+7*bits.length+7) := by
  obtain ⟨t,ht,hh,ho,hfirst⟩ := BitMachineCompositionArithmetic.first_halt M hcounter
  let c := M.run t (M.init bits)
  have hcall := BitMachineSubroutine.lift_run_until M.program (program M withPayload)
    (some Admin.header) (fun _ => rfl) none (foreign bits [] [] []) (M.init bits) t hfirst
  have hcall' : run M withPayload t
      (liftCfg (some .header) none (foreign bits [] [] []) (M.init bits)) =
      cfg M (some (.inr .header)) (c.var,none) c.stk bits [] [] [] := by
    change run M withPayload t _ =
      liftCfg (some Admin.header) none (foreign bits [] [] []) (M.run t (M.init bits)) at hcall
    simpa only [liftCfg, hh, cfg, c, Option.map_some] using hcall
  have hupdate : Function.update c.stk M.output bits.length.bits = c.stk := by
    have hout : c.stk M.output = bits.length.bits := ho
    rw [← hout, Function.update_eq_self]
  obtain ⟨u,hu,final,hrun,hhalt,hout⟩ := write_run M withPayload bits.length.bits bits (c.var,none) c.stk
  rw [hupdate] at hrun
  have hall := (run_add M withPayload
    ((run_add M withPayload (initial_copy M withPayload bits) t).trans hcall') u).trans hrun
  have htime : (2*bits.length+2)+t+u ≤ bound+7*bits.length+7 := by
    have hlen := UnaryBinaryEncoding.bits_length_le bits.length
    omega
  apply outputsWithin_of_raw_run (.inr 0) (.inr 3) (.inr .scan)
    (M.initial,none) (program M withPayload) bits _ ((2*bits.length+2)+t+u) _ htime
  · rw [raw_initial]
    change (run M withPayload _ _).l = none
    rw [hall]
    exact hhalt
  · rw [raw_initial]
    change (run M withPayload _ _).stk (.inr 3) = _
    rw [hall]
    exact hout

noncomputable abbrev counter := UnaryBinaryEncoding.machine

def result (withPayload : Bool) (bits : List Bool) : List Bool :=
  natField bits.length ++ if withPayload then bits else []

noncomputable def framingMachine (withPayload : Bool) : Machine := machine counter withPayload

theorem outputs (withPayload : Bool) (bits : List Bool) :
    (framingMachine withPayload).OutputsWithin bits (result withPayload bits)
      ((UnaryBinaryEncoding.coefficient+7)*(bits.length+1)^2) := by
  have h := outputs_of_counter counter withPayload bits _ (UnaryBinaryEncoding.outputs bits)
  apply BitMachine.outputsWithin_mono _ h
  nlinarith [Nat.zero_le bits.length]

theorem polytime (withPayload : Bool) : BitMachine.Polytime (result withPayload) :=
  ⟨framingMachine withPayload, UnaryBinaryEncoding.coefficient+7, 2, outputs withPayload⟩

theorem result_length (withPayload : Bool) (bits : List Bool) :
    (result withPayload bits).length ≤ 3*bits.length+1 := by
  have hn := UnaryBinaryEncoding.bits_length_le bits.length
  cases withPayload <;> simp only [result, natField, List.length_append, field_length,
    Bool.false_eq_true, Bool.true_eq, ↓reduceIte, List.length_nil] <;> omega

end EthInapproximability.CurrentPaper.SourceListMachineWriter
