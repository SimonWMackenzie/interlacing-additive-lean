import EthInapproximability.CurrentPaper.BitMachineBankCodec
import EthInapproximability.CurrentPaper.BitMachineBankSerialize

/-!
# Packed input and output for a fixed finite stack program

Source: frozen v8 `B-effectivity-details.tex`, concrete implementation.
The wrapper parses every bank word, executes literal local instructions,
then writes every final bank word. Malformed packets are rejected before
the local program is called. Local runtime hypotheses below are explicit
implementation interfaces, not completed sampler or verifier endpoints.
-/

namespace EthInapproximability.CurrentPaper.BitMachineBankWrapper

open Turing TM2.Stmt BitMachineEncoding BitMachineComposition BitMachineSubroutine

variable {K : ℕ} {L V : Type*}

inductive Admin (K : ℕ) where
  | parse : BitMachineBankCodec.ParserLabel K → Admin K
  | parsed
  | returned
  | serialize : BitMachineBankSerialize.Label K → Admin K
  deriving DecidableEq, Fintype

abbrev Stack (K : ℕ) := Fin K ⊕ Fin 3
abbrev Label (K : ℕ) (L : Type*) := L ⊕ Admin K
abbrev Control (V : Type*) := V × Option Bool
abbrev Bank (K : ℕ) := Fin K → List Bool

def program (P : L → TM2.Stmt (fun _ : Fin K => Bool) L V)
    (start : L) (initial : V) : Label K L →
    TM2.Stmt (fun _ : Stack K => Bool) (Label K L) (Control V)
  | .inl l => liftStmt (some (.returned : Admin K)) (P l)
  | .inr (.parse l) => BitMachineInline.stmt (fun l => .inr (.parse l))
      (fun v => (initial, v)) Prod.snd (some (.inr .parsed)) (BitMachineBankCodec.parser K l)
  | .inr .parsed => branch (fun v => v.2.getD false)
      (load (fun _ => (initial, none)) (goto (fun _ => .inl start))) halt
  | .inr .returned => load (fun _ => (initial, none))
      (goto (fun _ => .inr (.serialize (.emit 0))))
  | .inr (.serialize l) => BitMachineInline.stmt (fun l => .inr (.serialize l))
      (fun v => (initial, v)) Prod.snd none (BitMachineBankSerialize.program K l)

def cfg (l : Option (Label K L)) (v : Control V) (S : Bank K)
    (source saved output : List Bool) :
    TM2.Cfg (fun _ : Stack K => Bool) (Label K L) (Control V) :=
  ⟨l, v, BitMachineBankCodec.contents S source saved output⟩

def run (P : L → TM2.Stmt (fun _ : Fin K => Bool) L V)
    (start : L) (initial : V) (t : ℕ)
    (c : TM2.Cfg (fun _ : Stack K => Bool) (Label K L) (Control V)) :=
  ((advance (program P start initial))^[t]) c

theorem run_one (P : L → TM2.Stmt (fun _ : Fin K => Bool) L V)
    (start : L) (initial : V)
    (c : TM2.Cfg (fun _ : Stack K => Bool) (Label K L) (Control V)) :
    run P start initial 1 c = advance (program P start initial) c := by simp [run]

theorem run_add (P : L → TM2.Stmt (fun _ : Fin K => Bool) L V)
    (start : L) (initial : V) (t u : ℕ)
    (c : TM2.Cfg (fun _ : Stack K => Bool) (Label K L) (Control V)) :
    run P start initial (t+u) c = run P start initial u (run P start initial t c) := by
  simpa only [run, Nat.add_comm] using
    Function.iterate_add_apply (advance (program P start initial)) u t c

theorem parse_run (P : L → TM2.Stmt (fun _ : Fin K => Bool) L V)
    (start : L) (initial : V) (input : List Bool) (S : Bank K)
    (hdecode : BitMachineBankCodec.decode K input = some S) :
    ∃ t ≤ (2*K+1)*(input.length+1),
      run P start initial t
        (cfg (some (.inr (.parse (.scan 0)))) (initial, none) (fun _ => []) input [] []) =
        cfg (some (.inr .parsed)) (initial, some true) S [] [] [] := by
  obtain ⟨t, ht, hp⟩ := BitMachineBankCodec.parser_correct K input []
  rw [hdecode] at hp
  change BitMachineBankCodec.parserRun t
      (BitMachineBankCodec.parserCfg (some (.scan 0)) none (fun _ => []) input [] []) =
    BitMachineBankCodec.parserCfg none (some true) S [] [] [] at hp
  have hh := congrArg (fun c => c.l) hp
  change _ = none at hh
  obtain ⟨u, hu, hr⟩ := BitMachineInline.outputs
    (fun l => Sum.inr (.parse l) : BitMachineBankCodec.ParserLabel K → Label K L)
    (fun v => (initial, v)) Prod.snd (fun _ => rfl) (some (.inr .parsed))
    (BitMachineBankCodec.parser K) (program P start initial) (fun _ => rfl)
    (BitMachineBankCodec.parserCfg (some (.scan 0)) none (fun _ => []) input [] []) t hh
  refine ⟨u, hu.trans ht, ?_⟩
  change run P start initial u _ = _ at hr
  unfold BitMachineBankCodec.parserRun at hp
  rw [hp] at hr
  exact hr

theorem parsed_step (P : L → TM2.Stmt (fun _ : Fin K => Bool) L V)
    (start : L) (initial : V) (S : Bank K) :
    advance (program P start initial)
      (cfg (some (.inr .parsed)) (initial, some true) S [] [] []) =
      liftCfg (some (.returned : Admin K)) none (fun _ : Fin 3 => [])
        (⟨some start, initial, S⟩ : TM2.Cfg (fun _ : Fin K => Bool) L V) := by
  simp only [advance, program, cfg, TM2.step, TM2.stepAux, Option.getD_some,
    cond_true, liftCfg, BitMachineBankCodec.contents, ite_self]

theorem local_run (P : L → TM2.Stmt (fun _ : Fin K => Bool) L V)
    (start : L) (initial : V) (S : Bank K) (t : ℕ)
    (c : TM2.Cfg (fun _ : Fin K => Bool) L V)
    (h : ((advance P)^[t]) ⟨some start, initial, S⟩ = c) (hh : c.l = none) :
    ∃ u ≤ t,
      run P start initial u
        (liftCfg (some (.returned : Admin K)) none (fun _ : Fin 3 => [])
          (⟨some start, initial, S⟩ : TM2.Cfg (fun _ : Fin K => Bool) L V)) =
        cfg (some (.inr .returned)) (c.var, none) c.stk [] [] [] := by
  obtain ⟨u, hu, hr⟩ := lift_outputs P (program P start initial)
    (some (.returned : Admin K)) (fun _ => rfl) none (fun _ : Fin 3 => [])
    (⟨some start, initial, S⟩ : TM2.Cfg (fun _ : Fin K => Bool) L V) t (by rw [h, hh])
  refine ⟨u, hu, ?_⟩
  rw [h] at hr
  change run P start initial u _ = _ at hr
  simpa only [liftCfg, hh, Option.map_some, cfg, BitMachineBankCodec.contents, ite_self] using hr

theorem returned_step (P : L → TM2.Stmt (fun _ : Fin K => Bool) L V)
    (start : L) (initial v : V) (S : Bank K) :
    advance (program P start initial)
      (cfg (some (.inr .returned)) (v, none) S [] [] []) =
      cfg (some (.inr (.serialize (.emit 0)))) (initial, none) S [] [] [] := rfl

theorem serialize_run (P : L → TM2.Stmt (fun _ : Fin K => Bool) L V)
    (start : L) (initial : V) (S : Bank K) :
    ∃ (t : ℕ) (S' : Bank K), t ≤ 2*(BitMachineBankSerialize.encode (List.ofFn S)).length+2 ∧
      run P start initial t
        (cfg (some (.inr (.serialize (.emit 0)))) (initial, none) S [] [] []) =
        cfg none (initial, none) S' [] [] (BitMachineBankSerialize.encode (List.ofFn S)) := by
  obtain ⟨t, S', ht, hs⟩ := BitMachineBankSerialize.serialize S [] []
  have hh := congrArg (fun c => c.l) hs
  change _ = none at hh
  obtain ⟨u, hu, hr⟩ := BitMachineInline.outputs
    (fun l => Sum.inr (.serialize l) : BitMachineBankSerialize.Label K → Label K L)
    (fun v => (initial, v)) Prod.snd (fun _ => rfl) none
    (BitMachineBankSerialize.program K) (program P start initial) (fun _ => rfl)
    (BitMachineBankSerialize.cfg (some (.emit 0)) none S [] [] []) t hh
  refine ⟨u, S', hu.trans ht, ?_⟩
  change run P start initial u _ = _ at hr
  unfold BitMachineBankSerialize.run at hs
  rw [hs] at hr
  simpa only [BitMachineInline.cfg, BitMachineBankSerialize.cfg, List.append_nil] using hr

/-- Operational composition on a valid bank packet. The only local premise
is an actual execution of the chosen concrete finite program. -/
theorem packed_run (P : L → TM2.Stmt (fun _ : Fin K => Bool) L V)
    (start : L) (initial : V) (input : List Bool) (S : Bank K)
    (hdecode : BitMachineBankCodec.decode K input = some S) (t : ℕ)
    (c : TM2.Cfg (fun _ : Fin K => Bool) L V)
    (h : ((advance P)^[t]) ⟨some start, initial, S⟩ = c) (hh : c.l = none) :
    ∃ (u : ℕ) (S' : Bank K),
      u ≤ (2*K+1)*(input.length+1) + t +
        2*(BitMachineBankSerialize.encode (List.ofFn c.stk)).length+4 ∧
      run P start initial u
        (cfg (some (.inr (.parse (.scan 0)))) (initial, none) (fun _ => []) input [] []) =
        cfg none (initial, none) S' [] [] (BitMachineBankSerialize.encode (List.ofFn c.stk)) := by
  obtain ⟨a, ha, hp⟩ := parse_run P start initial input S hdecode
  obtain ⟨b, hb, hl⟩ := local_run P start initial S t c h hh
  obtain ⟨d, S', hd, hs⟩ := serialize_run P start initial c.stk
  refine ⟨a + 1 + b + 1 + d, S', by omega, ?_⟩
  rw [run_add, run_add, run_add, run_add, hp]
  simp only [run_one]
  rw [parsed_step, hl, returned_step, hs]

theorem reject_run (P : L → TM2.Stmt (fun _ : Fin K => Bool) L V)
    (start : L) (initial : V) (input : List Bool)
    (hdecode : BitMachineBankCodec.decode K input = none) :
    ∃ t ≤ (2*K+1)*(input.length+1)+1,
      let c := run P start initial t
        (cfg (some (.inr (.parse (.scan 0)))) (initial, none) (fun _ => []) input [] [])
      c.l = none ∧ c.stk (.inr 2) = [] := by
  obtain ⟨t, ht, hp⟩ := BitMachineBankCodec.parser_correct K input []
  rw [hdecode] at hp
  change (BitMachineBankCodec.parserRun t _).l = none ∧
    (BitMachineBankCodec.parserRun t _).var = some false ∧
    (BitMachineBankCodec.parserRun t _).stk (.inr 2) = [] at hp
  let c : TM2.Cfg (fun _ : Stack K => Bool) (BitMachineBankCodec.ParserLabel K) (Option Bool) :=
    BitMachineBankCodec.parserRun t
    (BitMachineBankCodec.parserCfg (some (.scan 0)) none (fun _ => []) input [] [])
  change c.l = none ∧ c.var = some false ∧ c.stk (.inr 2) = [] at hp
  obtain ⟨u, hu, hr⟩ := BitMachineInline.outputs
    (fun l => Sum.inr (.parse l) : BitMachineBankCodec.ParserLabel K → Label K L)
    (fun v => (initial, v)) Prod.snd (fun _ => rfl) (some (.inr .parsed))
    (BitMachineBankCodec.parser K) (program P start initial) (fun _ => rfl)
    (BitMachineBankCodec.parserCfg (some (.scan 0)) none (fun _ => []) input [] []) t hp.1
  change run P start initial u
      (cfg (some (.inr (.parse (.scan 0)))) (initial, none) (fun _ => []) input [] []) =
    BitMachineInline.cfg _ _ _ c at hr
  have hf : advance (program P start initial)
      (BitMachineInline.cfg (fun l => Sum.inr (.parse l)) (fun v => (initial, v))
        (some (.inr .parsed)) c) =
      (⟨none, (initial, some false), c.stk⟩ :
        TM2.Cfg (fun _ : Stack K => Bool) (Label K L) (Control V)) := by
    simp only [BitMachineInline.cfg, hp.1, hp.2.1, advance, TM2.step, program,
      TM2.stepAux, Option.getD_some, cond_false]
  refine ⟨u+1, by omega, ?_⟩
  dsimp only
  rw [run_add, run_one, hr, hf]
  exact ⟨rfl, hp.2.2⟩

def result (F : Bank K → Bank K) (input : List Bool) : List Bool :=
  match BitMachineBankCodec.decode K input with
  | none => []
  | some S => BitMachineBankCodec.encode (F S)

noncomputable def machine [Fintype L] [Fintype V]
    (P : L → TM2.Stmt (fun _ : Fin K => Bool) L V) (start : L) (initial : V) :
    BitMachine.Machine :=
  ofFinite (.inr 0) (.inr 2) (.inr (.parse (.scan 0))) (initial, none) (program P start initial)

theorem initial_cfg (initial : V) (input : List Bool) :
    rawInit (Sum.inr (0 : Fin 3) : Stack K) (Sum.inr (.parse (.scan 0)) : Label K L)
      (initial, none) input =
      cfg (some (.inr (.parse (.scan 0)))) (initial, none) (fun _ => []) input [] [] := by
  simp only [rawInit, cfg, BitMachineBankCodec.contents]
  congr 1
  funext j
  cases j with
  | inl j => simp
  | inr j => fin_cases j <;> rfl

/-- Any concrete raw-bank computation can be called on a single packed input.
Both the local execution and output-size bound are exposed here; a caller
must prove them for its chosen algorithm. -/
theorem outputs [Fintype L] [Fintype V]
    (P : L → TM2.Stmt (fun _ : Fin K => Bool) L V) (start : L) (initial : V)
    (F : Bank K → Bank K) (input : List Bool) (time size : ℕ)
    (hlocal : ∀ S, BitMachineBankCodec.decode K input = some S →
      ∃ (t : ℕ) (c : TM2.Cfg (fun _ : Fin K => Bool) L V), t ≤ time ∧
        ((advance P)^[t]) ⟨some start, initial, S⟩ = c ∧ c.l = none ∧ c.stk = F S)
    (hsize : ∀ S, BitMachineBankCodec.decode K input = some S →
      (BitMachineBankCodec.encode (F S)).length ≤ size) :
    (machine P start initial).OutputsWithin input (result F input)
      ((2*K+1)*(input.length+1)+time+2*size+4) := by
  cases hd : BitMachineBankCodec.decode K input with
  | none =>
      obtain ⟨t, ht, hh, ho⟩ := reject_run P start initial input hd
      apply outputsWithin_of_raw_run (.inr 0) (.inr 2) (.inr (.parse (.scan 0)))
        (initial, none) (program P start initial) input (result F input) t _ (by omega)
      · simpa only [initial_cfg, run] using hh
      · simpa only [initial_cfg, run, result, hd] using ho
  | some S =>
      obtain ⟨t, c, ht, hc, hh, hout⟩ := hlocal S hd
      obtain ⟨u, S', hu, hr⟩ := packed_run P start initial input S hd t c hc hh
      have he : BitMachineBankSerialize.encode (List.ofFn c.stk) =
          BitMachineBankCodec.encode (F S) := by
        rw [hout, BitMachineBankCodec.encode_eq_list]
        rfl
      rw [he] at hu hr
      have hs := hsize S hd
      apply outputsWithin_of_raw_run (.inr 0) (.inr 2) (.inr (.parse (.scan 0)))
        (initial, none) (program P start initial) input (result F input) u _ (by omega)
      · change (run P start initial u _).l = none
        rw [initial_cfg, hr]
        rfl
      · change (run P start initial u _).stk (.inr 2) = result F input
        rw [initial_cfg, hr]
        simp [cfg, BitMachineBankCodec.contents, result, hd]

/-- Polynomial raw execution and polynomial output size yield a genuine
single-input polynomial-time machine, including malformed-packet handling. -/
theorem polytime [Fintype L] [Fintype V]
    (P : L → TM2.Stmt (fun _ : Fin K => Bool) L V) (start : L) (initial : V)
    (F : Bank K → Bank K) (ct dt cs ds : ℕ)
    (hlocal : ∀ S, ∃ (t : ℕ) (c : TM2.Cfg (fun _ : Fin K => Bool) L V),
      t ≤ ct*((BitMachineBankCodec.encode S).length+1)^dt ∧
      ((advance P)^[t]) ⟨some start, initial, S⟩ = c ∧ c.l = none ∧ c.stk = F S)
    (hsize : ∀ S, (BitMachineBankCodec.encode (F S)).length ≤
      cs*((BitMachineBankCodec.encode S).length+1)^ds) :
    BitMachine.Polytime (result F) := by
  refine ⟨machine P start initial, 2*K+1+ct+2*cs+4, dt+ds+1, ?_⟩
  intro input
  have ho := outputs P start initial F input
    (ct*(input.length+1)^dt) (cs*(input.length+1)^ds) (by
      intro S hd
      have he := BitMachineBankCodec.encode_decode hd
      simpa only [he] using hlocal S) (by
      intro S hd
      have he := BitMachineBankCodec.encode_decode hd
      simpa only [he] using hsize S)
  apply BitMachine.outputsWithin_mono _ ho
  have hbase : 1 ≤ input.length+1 := by omega
  have ht := Nat.pow_le_pow_right hbase (show dt ≤ dt+ds+1 by omega)
  have hs := Nat.pow_le_pow_right hbase (show ds ≤ dt+ds+1 by omega)
  have hlin := Nat.pow_le_pow_right hbase (show 1 ≤ dt+ds+1 by omega)
  have hone : 1 ≤ (input.length+1)^(dt+ds+1) := Nat.one_le_pow _ _ hbase
  simp only [pow_one] at hlin
  nlinarith

end EthInapproximability.CurrentPaper.BitMachineBankWrapper
