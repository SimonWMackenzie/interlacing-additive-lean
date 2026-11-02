import CurrentAdditive.CodeDCodec
import EthInapproximability.CurrentPaper.BitMachineBankSerialize
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding
import Mathlib.Tactic

/-! A fixed three-field interface around a thirteen-stack RawRat program.
The physical parser and serializer are the reviewed bank-codec programs. -/

namespace CurrentAdditive.RawRatPacketWrapper

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open BitMachineEncoding

abbrev Stack := Fin 13 ⊕ Fin 3
abbrev Bank := Fin 13 → List Bool
abbrev Control (V : Type*) := V × Option Bool

inductive Admin where
  | parsed | signFirst | signTail | returned
  deriving DecidableEq, Fintype

abbrev Label (L : Type*) :=
  BitMachineBankCodec.ParserLabel 3 ⊕
    (L ⊕ (BitMachineBankSerialize.Label 3 ⊕ Admin))

def parseSlot : BitMachineBankCodec.Stack 3 ↪ Stack where
  toFun
    | .inl i => .inl ⟨i.val, by omega⟩
    | .inr j => .inr j
  inj' := by
    intro a b h
    cases a <;> cases b <;> simp_all [Fin.ext_iff]

def coreSlot : Fin 13 ↪ Stack where
  toFun := Sum.inl
  inj' := Sum.inl_injective

def serIndex : Fin 3 → Fin 13
  | 0 => 0
  | 1 => 1
  | 2 => 11

def serSlot : BitMachineBankSerialize.Stack 3 ↪ Stack where
  toFun
    | .inl i => .inl (serIndex i)
    | .inr j => .inr j
  inj' := by
    intro a b h
    cases a with
    | inl a =>
        cases b with
        | inl b =>
            have hi : serIndex a = serIndex b := Sum.inl.inj h
            fin_cases a <;> fin_cases b <;> simp_all [serIndex]
        | inr b => cases h
    | inr a =>
        cases b with
        | inl b => cases h
        | inr b => exact congrArg Sum.inr (Sum.inr.inj h)

def selected (S : Bank) : BitMachineBankSerialize.Bank 3 :=
  ![S 0, S 1, S 11]

theorem selected_length_le (S : Bank) :
    (BitMachineBankSerialize.encode (List.ofFn (selected S))).length ≤
      (BitMachineBankCodec.encode S).length := by
  change ((List.ofFn (selected S)).flatMap
    EncodedCommunication.field).length ≤ (BitMachineBankCodec.encode S).length
  rw [← BitMachineBankCodec.encode_eq_list,
    BitMachineBankCodec.encode_length,
    BitMachineBankCodec.encode_length]
  simp [selected, Fin.sum_univ_succ]
  omega

def inputBank (S : BitMachineBankCodec.Bank 3) : Bank :=
  fun i => if h : i.val < 3 then S ⟨i.val, h⟩ else []

def contents (S : Bank) (source saved output : List Bool) : Stack → List Bool :=
  Sum.elim S (fun j => if j = 0 then source else if j = 1 then saved else output)

def cfg {L V : Type*} (l : Option (Label L)) (v : Control V)
    (S : Bank) (source saved output : List Bool) :
    TM2.Cfg (fun _ : Stack => Bool) (Label L) (Control V) :=
  ⟨l,v,contents S source saved output⟩

def program {L V : Type*}
    (P : L → TM2.Stmt (fun _ : Fin 13 => Bool) L V)
    (start : L) (initial : V) : Label L →
    TM2.Stmt (fun _ : Stack => Bool) (Label L) (Control V)
  | .inl l => BitMachineStackEmbedding.stmt parseSlot Sum.inl
      (fun b => (initial,b)) Prod.snd (some (.inr (.inr (.inr .parsed))))
      (BitMachineBankCodec.parser 3 l)
  | .inr (.inl l) => BitMachineStackEmbedding.stmt coreSlot
      (fun l => .inr (.inl l)) (fun v => (v,none)) Prod.fst
      (some (.inr (.inr (.inr .returned)))) (P l)
  | .inr (.inr (.inl l)) => BitMachineStackEmbedding.stmt serSlot
      (fun l => .inr (.inr (.inl l))) (fun b => (initial,b)) Prod.snd none
      (BitMachineBankSerialize.program 3 l)
  | .inr (.inr (.inr .parsed)) => branch (fun v => v.2.getD false)
      (goto (fun _ => .inr (.inr (.inr .signFirst)))) halt
  | .inr (.inr (.inr .signFirst)) => peek (.inl 0)
      (fun v b => (v.1,b))
      (branch (fun v => v.2.isSome)
        (branch (fun v => v.2.getD false)
          (goto (fun _ => .inr (.inr (.inr .signTail)))) halt)
        (load (fun _ => (initial,none))
          (goto (fun _ => .inr (.inl start)))))
  | .inr (.inr (.inr .signTail)) => pop (.inl 0) (fun v b => (v.1,b))
      (peek (.inl 0) (fun v b => (v.1,b))
        (branch (fun v => v.2.isNone)
          (push (.inl 0) (fun _ => true)
            (load (fun _ => (initial,none))
              (goto (fun _ => .inr (.inl start))))) halt))
  | .inr (.inr (.inr .returned)) => load (fun _ => (initial,none))
      (goto (fun _ => .inr (.inr (.inl (.emit 0)))))

def run {L V : Type*}
    (P : L → TM2.Stmt (fun _ : Fin 13 => Bool) L V)
    (start : L) (initial : V) (t : Nat)
    (c : TM2.Cfg (fun _ : Stack => Bool) (Label L) (Control V)) :=
  ((advance (program P start initial))^[t]) c

theorem run_add {L V : Type*}
    (P : L → TM2.Stmt (fun _ : Fin 13 => Bool) L V)
    (start : L) (initial : V) (a b : Nat)
    (c : TM2.Cfg (fun _ : Stack => Bool) (Label L) (Control V)) :
    run P start initial (a+b) c = run P start initial b (run P start initial a c) := by
  simpa only [run, Nat.add_comm] using
    Function.iterate_add_apply (advance (program P start initial)) b a c

theorem parse_bank_contents (S : BitMachineBankCodec.Bank 3)
    (source saved output : List Bool) :
    BitMachineStackEmbedding.bank parseSlot (fun _ : Stack => [])
      (BitMachineBankCodec.contents S source saved output) =
      contents (inputBank S) source saved output := by
  funext j
  cases j with
  | inl j =>
      by_cases hj : j.val < 3
      · let k : Fin 3 := ⟨j.val, hj⟩
        have hk : parseSlot (.inl k) = (.inl j : Stack) := by
          simp [parseSlot, k]
        have hb := BitMachineStackEmbedding.bank_at parseSlot
          (fun _ : Stack => [])
          (BitMachineBankCodec.contents S source saved output) (.inl k)
        have hb' : BitMachineStackEmbedding.bank parseSlot (fun _ : Stack => [])
            (BitMachineBankCodec.contents S source saved output) (.inl j) = S k := by
          simpa only [hk, BitMachineBankCodec.contents, Sum.elim_inl] using hb
        rw [hb']
        simp [contents, inputBank, k, hj]
      · have ho : ¬ ∃ k, parseSlot k = (.inl j : Stack) := by
          rintro ⟨k, hk⟩
          cases k with
          | inl k =>
              have hv := congrArg (fun x : Stack => x) hk
              simp [parseSlot, Fin.ext_iff] at hv
              omega
          | inr k => cases hk
        rw [BitMachineStackEmbedding.bank_outside parseSlot _ _ _ ho]
        simp [contents, inputBank, hj]
  | inr j =>
      have hk : parseSlot (.inr j) = (.inr j : Stack) := rfl
      have hb := BitMachineStackEmbedding.bank_at parseSlot
        (fun _ : Stack => [])
        (BitMachineBankCodec.contents S source saved output) (.inr j)
      simpa only [hk, BitMachineBankCodec.contents, contents, Sum.elim_inr] using hb

theorem parse_start {L V : Type*} (initial : V) (input : List Bool) :
    BitMachineStackEmbedding.cfg parseSlot (fun _ : Stack => []) Sum.inl
      (fun b => (initial,b)) (some (.inr (.inr (.inr .parsed))))
      (BitMachineBankCodec.parserCfg (some (.scan 0)) none
        (fun _ => []) input [] []) =
    (cfg (some (.inl (.scan 0))) (initial,none)
      (fun _ => []) input [] [] :
      TM2.Cfg (fun _ : Stack => Bool) (Label L) (Control V)) := by
  unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg cfg
  congr 1
  have he : inputBank (fun _ : Fin 3 => []) = (fun _ : Fin 13 => []) := by
    funext i
    simp [inputBank]
  simpa only [BitMachineBankCodec.parserCfg, he] using
    parse_bank_contents (fun _ => []) input [] []

theorem parse_end {L V : Type*} (initial : V)
    (S : BitMachineBankCodec.Bank 3) :
    BitMachineStackEmbedding.cfg parseSlot (fun _ : Stack => []) Sum.inl
      (fun b => (initial,b)) (some (.inr (.inr (.inr .parsed))))
      (BitMachineBankCodec.parserCfg none (some true) S [] [] []) =
    (cfg (some (.inr (.inr (.inr .parsed)))) (initial,some true)
      (inputBank S) [] [] [] :
      TM2.Cfg (fun _ : Stack => Bool) (Label L) (Control V)) := by
  unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg cfg
  congr 1
  simpa only [BitMachineBankCodec.parserCfg] using
    parse_bank_contents S [] [] []

theorem parse_run {L V : Type*}
    (P : L → TM2.Stmt (fun _ : Fin 13 => Bool) L V)
    (start : L) (initial : V) (input : List Bool)
    (S : BitMachineBankCodec.Bank 3)
    (hd : BitMachineBankCodec.decode 3 input = some S) :
    ∃ t ≤ 7*(input.length+1),
      run P start initial t
        (cfg (some (.inl (.scan 0))) (initial,none) (fun _ => []) input [] []) =
      cfg (some (.inr (.inr (.inr .parsed)))) (initial,some true)
        (inputBank S) [] [] [] := by
  obtain ⟨t,ht,hp⟩ := BitMachineBankCodec.parser_correct 3 input []
  rw [hd] at hp
  change BitMachineBankCodec.parserRun t
    (BitMachineBankCodec.parserCfg (some (.scan 0)) none (fun _ => []) input [] []) =
    BitMachineBankCodec.parserCfg none (some true) S [] [] [] at hp
  have hh := congrArg (fun c => c.l) hp
  change _ = none at hh
  obtain ⟨u,hu,hr⟩ := BitMachineStackEmbedding.outputs parseSlot
    (fun _ : Stack => []) Sum.inl (fun b => (initial,b)) Prod.snd
    (fun _ => rfl) (some (.inr (.inr (.inr .parsed))))
    (BitMachineBankCodec.parser 3) (program P start initial) (fun _ => rfl)
    (BitMachineBankCodec.parserCfg (some (.scan 0)) none
      (fun _ => []) input [] []) t hh
  refine ⟨u, hu.trans ht, ?_⟩
  change run P start initial u _ = _ at hr
  rw [parse_start initial input] at hr
  unfold BitMachineBankCodec.parserRun at hp
  rw [hp] at hr
  exact hr.trans (parse_end initial S)

theorem ser_start {L V : Type*} (initial : V) (S : Bank) :
    BitMachineStackEmbedding.cfg serSlot (contents S [] [] [])
      (fun l => (.inr (.inr (.inl l)) : Label L))
      (fun b => (initial,b)) none
      (BitMachineBankSerialize.cfg (some (.emit 0)) none (selected S) [] [] []) =
    (cfg (some (.inr (.inr (.inl (.emit 0))))) (initial,none)
      S [] [] [] : TM2.Cfg (fun _ : Stack => Bool) (Label L) (Control V)) := by
  unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg cfg
  congr 1
  apply BitMachineStackEmbedding.bank_eq_self
  intro k
  cases k with
  | inl k =>
      fin_cases k <;> simp [serSlot, serIndex, selected,
        BitMachineBankSerialize.cfg, BitMachineBankSerialize.contents, contents]
  | inr k =>
      fin_cases k <;> simp [serSlot, BitMachineBankSerialize.cfg,
        BitMachineBankSerialize.contents, contents]

theorem ser_output {L V : Type*} (initial : V) (S : Bank)
    (T : BitMachineBankSerialize.Bank 3) :
    (BitMachineStackEmbedding.cfg serSlot (contents S [] [] [])
      (fun l => (.inr (.inr (.inl l)) : Label L))
      (fun b => (initial,b)) none
      (BitMachineBankSerialize.cfg none none T [] []
        (BitMachineBankSerialize.encode (List.ofFn (selected S))))).stk (.inr 2) =
    BitMachineBankSerialize.encode (List.ofFn (selected S)) := by
  unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg
  have hk : serSlot (.inr (2 : Fin 3)) = (.inr 2 : Stack) := rfl
  change BitMachineStackEmbedding.bank serSlot (contents S [] [] [])
    (BitMachineBankSerialize.cfg none none T [] []
      (BitMachineBankSerialize.encode (List.ofFn (selected S)))).stk
    (.inr 2) = _
  rw [← hk, BitMachineStackEmbedding.bank_at]
  rfl

theorem serialize_run {L V : Type*}
    (P : L → TM2.Stmt (fun _ : Fin 13 => Bool) L V)
    (start : L) (initial : V) (S : Bank) :
    ∃ t ≤ 2*(BitMachineBankSerialize.encode (List.ofFn (selected S))).length+2,
      let c := run P start initial t
        (cfg (some (.inr (.inr (.inl (.emit 0))))) (initial,none) S [] [] [])
      c.l = none ∧ c.stk (.inr 2) =
        BitMachineBankSerialize.encode (List.ofFn (selected S)) := by
  obtain ⟨t,T,ht,hs⟩ := BitMachineBankSerialize.serialize (selected S) [] []
  have hh := congrArg (fun c => c.l) hs
  change _ = none at hh
  obtain ⟨u,hu,hr⟩ := BitMachineStackEmbedding.outputs serSlot
    (contents S [] [] [])
    (fun l => (.inr (.inr (.inl l)) : Label L))
    (fun b => (initial,b)) Prod.snd (fun _ => rfl) none
    (BitMachineBankSerialize.program 3) (program P start initial) (fun _ => rfl)
    (BitMachineBankSerialize.cfg (some (.emit 0)) none (selected S) [] [] []) t hh
  refine ⟨u, hu.trans ht, ?_⟩
  dsimp only
  change run P start initial u _ = _ at hr
  rw [ser_start initial S] at hr
  unfold BitMachineBankSerialize.run at hs
  rw [hs] at hr
  rw [hr]
  exact ⟨rfl, by simpa only [List.append_nil] using ser_output initial S T⟩

theorem parsed_step {L V : Type*}
    (P : L → TM2.Stmt (fun _ : Fin 13 => Bool) L V)
    (start : L) (initial : V) (S : Bank) :
    advance (program P start initial)
      (cfg (some (.inr (.inr (.inr .parsed)))) (initial,some true) S [] [] []) =
    cfg (some (.inr (.inr (.inr .signFirst)))) (initial,some true) S [] [] [] := by
  simp [advance, program, TM2.step, TM2.stepAux, cfg]

theorem returned_step {L V : Type*}
    (P : L → TM2.Stmt (fun _ : Fin 13 => Bool) L V)
    (start : L) (initial v : V) (S : Bank) :
    advance (program P start initial)
      (cfg (some (.inr (.inr (.inr .returned)))) (v,none) S [] [] []) =
    cfg (some (.inr (.inr (.inl (.emit 0))))) (initial,none) S [] [] [] := by
  simp [advance, program, TM2.step, TM2.stepAux, cfg]

theorem core_start {L V : Type*} (start : L) (initial : V) (S : Bank) :
    BitMachineStackEmbedding.cfg coreSlot (contents S [] [] [])
      (fun l => (.inr (.inl l) : Label L))
      (fun v => (v,none)) (some (.inr (.inr (.inr .returned))))
      (⟨some start,initial,S⟩ : TM2.Cfg (fun _ : Fin 13 => Bool) L V) =
    (cfg (some (.inr (.inl start))) (initial,none) S [] [] [] :
      TM2.Cfg (fun _ : Stack => Bool) (Label L) (Control V)) := by
  unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg cfg
  congr 1
  apply BitMachineStackEmbedding.bank_eq_self
  intro k
  fin_cases k <;> simp [coreSlot, contents]

theorem core_end {L V : Type*} (initial v : V) (S T : Bank) :
    BitMachineStackEmbedding.cfg coreSlot (contents S [] [] [])
      (fun l => (.inr (.inl l) : Label L))
      (fun v => (v,none)) (some (.inr (.inr (.inr .returned))))
      (⟨none,v,T⟩ : TM2.Cfg (fun _ : Fin 13 => Bool) L V) =
    (cfg (some (.inr (.inr (.inr .returned)))) (v,none) T [] [] [] :
      TM2.Cfg (fun _ : Stack => Bool) (Label L) (Control V)) := by
  unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg cfg
  congr 1
  funext j
  cases j with
  | inl j =>
      have hk : coreSlot j = (.inl j : Stack) := rfl
      rw [← hk, BitMachineStackEmbedding.bank_at]
      rfl
  | inr j =>
      have ho : ¬ ∃ k, coreSlot k = (.inr j : Stack) := by
        rintro ⟨k,h⟩
        cases h
      rw [BitMachineStackEmbedding.bank_outside coreSlot _ _ _ ho]
      fin_cases j <;> rfl

theorem core_run {L V : Type*}
    (P : L → TM2.Stmt (fun _ : Fin 13 => Bool) L V)
    (start : L) (initial : V) (S T : Bank) (v : V) (t : Nat)
    (h : ((advance P)^[t])
      (⟨some start, initial, S⟩ : TM2.Cfg (fun _ : Fin 13 => Bool) L V) =
      ⟨none,v,T⟩) :
    ∃ u ≤ t,
      run P start initial u
        (cfg (some (.inr (.inl start))) (initial,none) S [] [] []) =
      cfg (some (.inr (.inr (.inr .returned)))) (v,none) T [] [] [] := by
  have hh := congrArg (fun c => c.l) h
  change (((advance P)^[t])
    (⟨some start, initial, S⟩ : TM2.Cfg (fun _ : Fin 13 => Bool) L V)).l = none at hh
  obtain ⟨u,hu,hr⟩ := BitMachineStackEmbedding.outputs coreSlot
    (contents S [] [] []) (fun l => (.inr (.inl l) : Label L))
    (fun v => (v,none)) Prod.fst (fun _ => rfl)
    (some (.inr (.inr (.inr .returned)))) P (program P start initial)
    (fun _ => rfl) (⟨some start,initial,S⟩ : TM2.Cfg (fun _ : Fin 13 => Bool) L V)
    t hh
  refine ⟨u,hu,?_⟩
  change run P start initial u _ = _ at hr
  rw [core_start start initial S] at hr
  rw [h] at hr
  exact hr.trans (core_end initial v S T)

theorem packed_run {L V : Type*}
    (P : L → TM2.Stmt (fun _ : Fin 13 => Bool) L V)
    (start : L) (initial : V) (input : List Bool)
    (B : BitMachineBankCodec.Bank 3) (T : Bank) (v : V) (t : Nat)
    (q : Nat)
    (hd : BitMachineBankCodec.decode 3 input = some B)
    (hvalidate : run P start initial q
      (cfg (some (.inr (.inr (.inr .signFirst)))) (initial,some true)
        (inputBank B) [] [] []) =
      cfg (some (.inr (.inl start))) (initial,none) (inputBank B) [] [] [])
    (hcore : ((advance P)^[t])
      (⟨some start,initial,inputBank B⟩ : TM2.Cfg (fun _ : Fin 13 => Bool) L V) =
      ⟨none,v,T⟩) :
    ∃ u ≤ 7*(input.length+1) + q + t +
        2*(BitMachineBankSerialize.encode (List.ofFn (selected T))).length+4,
      let c := run P start initial u
        (cfg (some (.inl (.scan 0))) (initial,none) (fun _ => []) input [] [])
      c.l = none ∧ c.stk (.inr 2) =
        BitMachineBankSerialize.encode (List.ofFn (selected T)) := by
  obtain ⟨a,ha,hp⟩ := parse_run P start initial input B hd
  obtain ⟨b,hb,hc⟩ := core_run P start initial (inputBank B) T v t hcore
  obtain ⟨d,hd',hs⟩ := serialize_run P start initial T
  refine ⟨a+1+q+b+1+d, by omega, ?_⟩
  dsimp only
  rw [run_add, run_add, run_add, run_add, run_add, hp]
  have hp1 : run P start initial 1
      (cfg (some (.inr (.inr (.inr .parsed)))) (initial,some true)
        (inputBank B) [] [] []) =
      cfg (some (.inr (.inr (.inr .signFirst)))) (initial,some true)
        (inputBank B) [] [] [] := by
    simpa [run] using parsed_step P start initial (inputBank B)
  have hr1 : run P start initial 1
      (cfg (some (.inr (.inr (.inr .returned)))) (v,none) T [] [] []) =
      cfg (some (.inr (.inr (.inl (.emit 0))))) (initial,none) T [] [] [] := by
    simpa [run] using returned_step P start initial v T
  rw [hp1, hvalidate, hc, hr1]
  exact hs

end CurrentAdditive.RawRatPacketWrapper
