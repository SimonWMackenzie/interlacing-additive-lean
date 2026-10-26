import CurrentAdditive.GaussContextSubroutine
import CurrentAdditive.RationalProductCellSelect
import CurrentAdditive.CodeDPairProductTargetV2
import CurrentAdditive.GaussCellSpec

namespace CurrentAdditive.GaussPhysical.GaussBranchSelect

open EthInapproximability.CurrentPaper
open Turing TM2.Stmt BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineBankCodec

abbrev Stack := BitMachineBankCodec.Stack 12
abbrev Bank := BitMachineBankCodec.Bank 12
abbrev SerLabel := BitMachineBankSerialize.Label 2
abbrev Label := BitMachineBankCodec.ParserLabel 12 ⊕
  ((Bool × SerLabel) ⊕ Fin 2)
abbrev Control := Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def pick (flag : Bool) : Fin 12 := if flag then 3 else 2

theorem pick_ne_four (flag : Bool) : pick flag ≠ (4 : Fin 12) := by
  cases flag <;> decide

def selected (flag : Bool) (S : Bank) : BitMachineBankSerialize.Bank 2 :=
  RationalProductCellSelect.selected (pick flag) 4 S

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineInline.stmt Sum.inl id id
      (some (.inr (.inr 0))) (BitMachineBankCodec.parser 12 l)
  | .inr (.inr 0) => branch (fun v => v.getD false)
      (goto (fun _ => .inr (.inr 1))) halt
  | .inr (.inr 1) => peek (.inl 0) (fun _ bit => bit)
      (load (fun v => some (v.getD false))
      (branch (fun v => v.getD false)
        (load (fun _ => none)
          (goto (fun _ => .inr (.inl (true, .emit 0)))))
        (load (fun _ => none)
          (goto (fun _ => .inr (.inl (false, .emit 0)))))))
  | .inr (.inl (flag, l)) =>
      BitMachineStackEmbedding.stmt
        (RationalProductCellSelect.serSlots (pick flag) 4 (pick_ne_four flag))
        (fun l => .inr (.inl (flag, l))) id id none
        (BitMachineBankSerialize.program 2 l)

def cfg (l : Option Label) (v : Control) (S : Bank)
    (source saved output : List Bool) : Config :=
  ⟨l, v, BitMachineBankCodec.contents S source saved output⟩

def run (n : ℕ) (c : Config) : Config := ((advance program)^[n]) c

theorem run_add (t u : ℕ) (c : Config) :
    run (t+u) c = run u (run t c) := by
  simpa only [run, Nat.add_comm] using
    Function.iterate_add_apply (advance program) u t c

theorem parse_run (input : List Bool) (S : Bank)
    (hd : BitMachineBankCodec.decode 12 input = some S) :
    ∃ t ≤ 25*(input.length+1),
      run t (cfg (some (.inl (.scan 0))) none (fun _ => []) input [] []) =
        cfg (some (.inr (.inr 0))) (some true) S [] [] [] := by
  obtain ⟨t,ht,hp⟩ := BitMachineBankCodec.parser_correct 12 input []
  rw [hd] at hp
  change BitMachineBankCodec.parserRun t
    (BitMachineBankCodec.parserCfg (some (.scan 0)) none
      (fun _ => []) input [] []) =
    BitMachineBankCodec.parserCfg none (some true) S [] [] [] at hp
  have hh := congrArg (fun c => c.l) hp
  change _ = none at hh
  obtain ⟨u,hu,hr⟩ := BitMachineInline.outputs
    (Sum.inl : BitMachineBankCodec.ParserLabel 12 → Label)
    id id (fun _ => rfl) (some (.inr (.inr 0)))
    (BitMachineBankCodec.parser 12) program (fun _ => rfl)
    (BitMachineBankCodec.parserCfg (some (.scan 0)) none
      (fun _ => []) input [] []) t hh
  refine ⟨u, hu.trans ht, ?_⟩
  unfold BitMachineBankCodec.parserRun at hp
  rw [hp] at hr
  exact hr

theorem parsed_step (S : Bank) :
    advance program (cfg (some (.inr (.inr 0))) (some true) S [] [] []) =
      cfg (some (.inr (.inr 1))) (some true) S [] [] [] := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]

theorem dispatch_step (S : Bank) :
    let flag := (S 0).head?.getD false
    advance program (cfg (some (.inr (.inr 1))) (some true) S [] [] []) =
      cfg (some (.inr (.inl (flag, .emit 0)))) none S [] [] [] := by
  cases h : (S 0).head? with
  | none =>
      simp [advance, TM2.step, TM2.stepAux, program, cfg,
        BitMachineBankCodec.contents, h]
  | some b =>
      cases b <;>
        simp [advance, TM2.step, TM2.stepAux, program, cfg,
          BitMachineBankCodec.contents, h]

private theorem ser_start (flag : Bool) (S : Bank) :
    cfg (some (.inr (.inl (flag, .emit 0)))) none S [] [] [] =
      BitMachineStackEmbedding.cfg
        (RationalProductCellSelect.serSlots (pick flag) 4 (pick_ne_four flag))
        (cfg (some (.inr (.inl (flag, .emit 0)))) none S [] [] []).stk
        (fun l => .inr (.inl (flag, l))) id none
        (BitMachineBankSerialize.cfg (some (.emit 0)) none
          (selected flag S) [] [] []) := by
  unfold cfg BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg
  congr 1
  apply (BitMachineStackEmbedding.bank_eq_self
    (RationalProductCellSelect.serSlots (pick flag) 4 (pick_ne_four flag))
    (cfg (some (.inr (.inl (flag, .emit 0)))) none S [] [] []).stk
    (BitMachineBankSerialize.cfg (some (.emit 0)) none
      (selected flag S) [] [] []).stk) ?_ |>.symm
  intro k
  cases k with
  | inl k =>
      fin_cases k <;> cases flag <;>
        simp [RationalProductCellSelect.serSlots, selected, pick,
          RationalProductCellSelect.selected, cfg,
          BitMachineBankCodec.contents, BitMachineBankSerialize.cfg,
          BitMachineBankSerialize.contents]
  | inr k =>
      fin_cases k <;>
        simp [RationalProductCellSelect.serSlots, cfg,
          BitMachineBankCodec.contents, BitMachineBankSerialize.cfg,
          BitMachineBankSerialize.contents]

private theorem ser_program_eq (flag : Bool) (l : SerLabel) :
    program (.inr (.inl (flag, l))) =
      BitMachineStackEmbedding.stmt
        (RationalProductCellSelect.serSlots (pick flag) 4 (pick_ne_four flag))
        (fun l => .inr (.inl (flag, l))) id id none
        (BitMachineBankSerialize.program 2 l) := rfl

theorem serialize_run (flag : Bool) (S : Bank) :
    ∃ t ≤ 2*(BitMachineBankSerialize.encode (List.ofFn (selected flag S))).length+2,
      let c := run t (cfg (some (.inr (.inl (flag, .emit 0)))) none S [] [] [])
      c.l = none ∧ c.stk (.inr 2) =
        BitMachineBankSerialize.encode (List.ofFn (selected flag S)) ∧
      ∀ j : Fin 12, j ≠ pick flag → j ≠ 4 → c.stk (.inl j) = S j := by
  obtain ⟨t,T,ht,hs⟩ := BitMachineBankSerialize.serialize
    (selected flag S) [] []
  have hh := congrArg (fun c => c.l) hs
  change _ = none at hh
  obtain ⟨u,hu,hr⟩ := BitMachineStackEmbedding.outputs
    (RationalProductCellSelect.serSlots (pick flag) 4 (pick_ne_four flag))
    (cfg (some (.inr (.inl (flag, .emit 0)))) none S [] [] []).stk
    (fun l => .inr (.inl (flag, l))) id id (by intro v; rfl) none
    (BitMachineBankSerialize.program 2) program
    (ser_program_eq flag)
    (BitMachineBankSerialize.cfg (some (.emit 0)) none
      (selected flag S) [] [] []) t
    (by simpa only [BitMachineBankSerialize.run] using hh)
  refine ⟨u, hu.trans ht, ?_⟩
  change _ ∧ _ ∧ _
  rw [← ser_start flag S] at hr
  change run u _ = _ at hr
  unfold BitMachineBankSerialize.run at hs
  rw [hs] at hr
  constructor
  · exact congrArg (fun c => c.l) hr
  constructor
  · have ho := congrArg (fun c => c.stk (.inr 2)) hr
    simp only [BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg] at ho
    rw [← show (RationalProductCellSelect.serSlots
      (pick flag) 4 (pick_ne_four flag)) (.inr 2) = (.inr 2 : Stack) by rfl,
      BitMachineStackEmbedding.bank_at] at ho
    simpa [BitMachineBankSerialize.cfg,
      BitMachineBankSerialize.contents] using ho
  · intro j hja hjb
    have hout : ¬ ∃ k : BitMachineBankSerialize.Stack 2,
        RationalProductCellSelect.serSlots
          (pick flag) 4 (pick_ne_four flag) k = (.inl j : Stack) := by
      rintro ⟨k,hk⟩
      cases k with
      | inl k =>
          fin_cases k
          · exact hja (Sum.inl.inj hk).symm
          · exact hjb (Sum.inl.inj hk).symm
      | inr k => cases hk
    have hj := congrArg (fun c => c.stk (.inl j)) hr
    simp only [BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg] at hj
    rw [BitMachineStackEmbedding.bank_outside _ _ _ _ hout] at hj
    exact hj

theorem valid_run (input : List Bool) (S : Bank)
    (hd : BitMachineBankCodec.decode 12 input = some S) :
    ∃ t ≤ 35*(input.length+1),
      let c := run t
        (cfg (some (.inl (.scan 0))) none (fun _ => []) input [] [])
      c.l = none ∧ c.stk (.inr 2) =
        BitMachineBankSerialize.encode
          (List.ofFn (selected ((S 0).head?.getD false) S)) ∧
      ∀ j : Fin 12, j ≠ pick ((S 0).head?.getD false) → j ≠ 4 →
        c.stk (.inl j) = S j := by
  let flag := (S 0).head?.getD false
  obtain ⟨t,ht,hp⟩ := parse_run input S hd
  obtain ⟨u,hu,hs⟩ := serialize_run flag S
  refine ⟨t+1+1+u, ?_, ?_⟩
  · have hl := RationalProductCellSelect.output_length
      (pick flag) 4 input S hd
    dsimp [selected] at hu ⊢
    omega
  · rw [run_add (t+1+1) u, run_add (t+1) 1,
      run_add t 1, hp]
    change
      let c := run u (advance program (advance program
        (cfg (some (.inr (.inr 0))) (some true) S [] [] [])))
      c.l = none ∧ c.stk (.inr 2) =
        BitMachineBankSerialize.encode
          (List.ofFn (selected ((S 0).head?.getD false) S)) ∧
      ∀ j : Fin 12, j ≠ pick ((S 0).head?.getD false) → j ≠ 4 →
        c.stk (.inl j) = S j
    rw [parsed_step, dispatch_step]
    exact hs

theorem reject_run (input : List Bool)
    (hd : BitMachineBankCodec.decode 12 input = none) :
    ∃ t ≤ 25*(input.length+1)+1,
      let c := run t
        (cfg (some (.inl (.scan 0))) none (fun _ => []) input [] [])
      c.l = none ∧ c.stk (.inr 2) = [] := by
  obtain ⟨t,ht,hp⟩ := BitMachineBankCodec.parser_correct 12 input []
  rw [hd] at hp
  change (BitMachineBankCodec.parserRun t _).l = none ∧
    (BitMachineBankCodec.parserRun t _).var = some false ∧
    (BitMachineBankCodec.parserRun t _).stk (.inr 2) = [] at hp
  let c : TM2.Cfg (fun _ : BitMachineBankCodec.Stack 12 => Bool)
      (BitMachineBankCodec.ParserLabel 12) Control :=
    BitMachineBankCodec.parserRun t
      (BitMachineBankCodec.parserCfg (some (.scan 0)) none
        (fun _ => []) input [] [])
  change c.l = none ∧ c.var = some false ∧ c.stk (.inr 2) = [] at hp
  obtain ⟨u,hu,hr⟩ := BitMachineInline.outputs
    (Sum.inl : BitMachineBankCodec.ParserLabel 12 → Label)
    id id (fun _ => rfl) (some (.inr (.inr 0)))
    (BitMachineBankCodec.parser 12) program (fun _ => rfl)
    (BitMachineBankCodec.parserCfg (some (.scan 0)) none
      (fun _ => []) input [] []) t hp.1
  refine ⟨u+1, by omega, ?_⟩
  have hr' : run u
      (cfg (some (.inl (.scan 0))) none (fun _ => []) input [] []) =
      BitMachineInline.cfg Sum.inl id (some (.inr (.inr 0))) c := hr
  change _ ∧ _
  rw [run_add u 1, hr']
  simp only [run, Function.iterate_one]
  simp [advance, TM2.step, TM2.stepAux, program, BitMachineInline.cfg,
    hp.1, hp.2.1, hp.2.2]

def result (input : List Bool) : List Bool :=
  match BitMachineBankCodec.decode 12 input with
  | none => []
  | some S => BitMachineBankSerialize.encode
      (List.ofFn (selected ((S 0).head?.getD false) S))

noncomputable def machine : BitMachine.Machine :=
  ofFinite (.inr 0 : Stack) (.inr 2 : Stack)
    (.inl (.scan 0) : Label) (none : Control) program

theorem initial_cfg (input : List Bool) :
    rawInit (.inr 0 : Stack) (.inl (.scan 0) : Label) none input =
      cfg (some (.inl (.scan 0))) none (fun _ => []) input [] [] := by
  unfold rawInit cfg BitMachineBankCodec.contents
  congr 1
  funext k
  cases k with
  | inl k => simp
  | inr k => fin_cases k <;> rfl

theorem outputs (input : List Bool) :
    machine.OutputsWithin input (result input)
      (35*(input.length+1)) := by
  cases hd : BitMachineBankCodec.decode 12 input with
  | none =>
      obtain ⟨t,ht,hh,ho⟩ := reject_run input hd
      apply outputsWithin_of_raw_run (.inr 0 : Stack) (.inr 2)
        (.inl (.scan 0)) none program input
        (result input) t _ (by omega)
      · simpa only [initial_cfg, run] using hh
      · simpa only [initial_cfg, run, result, hd] using ho
  | some S =>
      obtain ⟨t,ht,hh,ho,_⟩ := valid_run input S hd
      apply outputsWithin_of_raw_run (.inr 0 : Stack) (.inr 2)
        (.inl (.scan 0)) none program input
        (result input) t _ ht
      · simpa only [initial_cfg, run] using hh
      · simpa only [initial_cfg, run, result, hd] using ho

theorem polytime : BitMachine.Polytime result := by
  refine ⟨machine, 35, 1, ?_⟩
  intro input
  simpa only [pow_one] using outputs input

theorem result_cellPacket (flag : Bool)
    (current column row pivot : CurrentAdditive.CodeDCodec.RawRat) :
    result (CurrentAdditive.GaussPhysical.cellPacket
      flag current column row pivot) =
      CurrentAdditive.CodeDPairProductTargetV2.pairBytes
        (if flag then row else column) pivot := by
  cases flag <;>
    simp only [CurrentAdditive.GaussPhysical.cellPacket,
      result, BitMachineBankCodec.decode_encode]
  · rw [BitMachineBankSerialize.encode,
      ← BitMachineBankCodec.encode_eq_list]
    unfold CurrentAdditive.CodeDPairProductTargetV2.pairBytes
    congr 1
  · rw [BitMachineBankSerialize.encode,
      ← BitMachineBankCodec.encode_eq_list]
    unfold CurrentAdditive.CodeDPairProductTargetV2.pairBytes
    congr 1

theorem outputs_cellPacket (flag : Bool)
    (current column row pivot : CurrentAdditive.CodeDCodec.RawRat) :
    machine.OutputsWithin
      (CurrentAdditive.GaussPhysical.cellPacket
        flag current column row pivot)
      (CurrentAdditive.CodeDPairProductTargetV2.pairBytes
        (if flag then row else column) pivot)
      (35*((CurrentAdditive.GaussPhysical.cellPacket
        flag current column row pivot).length+1)) := by
  simpa only [result_cellPacket] using
    outputs (CurrentAdditive.GaussPhysical.cellPacket
      flag current column row pivot)

theorem cellPacket_retains_context (flag : Bool)
    (current column row pivot : CurrentAdditive.CodeDCodec.RawRat) :
    ∃ t ≤ 35*((CurrentAdditive.GaussPhysical.cellPacket
        flag current column row pivot).length+1),
      let c := run t (cfg (some (.inl (.scan 0))) none (fun _ => [])
        (CurrentAdditive.GaussPhysical.cellPacket
          flag current column row pivot) [] [])
      c.l = none ∧ c.stk (.inr 2) =
        CurrentAdditive.CodeDPairProductTargetV2.pairBytes
          (if flag then row else column) pivot ∧
      c.stk (.inl 1) = CurrentAdditive.CodeDCodec.encodeRawRat current ∧
      (if flag then
        c.stk (.inl 2) = CurrentAdditive.CodeDCodec.encodeRawRat column
       else
        c.stk (.inl 3) = CurrentAdditive.CodeDCodec.encodeRawRat row) := by
  let S := CurrentAdditive.GaussPhysical.cellBank
    flag current column row pivot
  obtain ⟨t,ht,hh,ho,hkeep⟩ := valid_run
    (CurrentAdditive.GaussPhysical.cellPacket
      flag current column row pivot) S
    (CurrentAdditive.GaussPhysical.decode_cellPacket
      flag current column row pivot)
  have hflag : ((S 0).head?.getD false) = flag := by
    simp [S, CurrentAdditive.GaussPhysical.cellBank]
  rw [hflag] at ho hkeep
  refine ⟨t,ht,hh,?_,?_,?_⟩
  · rw [← result_cellPacket]
    simpa [result, CurrentAdditive.GaussPhysical.decode_cellPacket] using ho
  · simpa [S, CurrentAdditive.GaussPhysical.cellBank] using
      hkeep 1 (by cases flag <;> decide) (by decide)
  · cases flag
    · simpa [S, pick, CurrentAdditive.GaussPhysical.cellBank] using
        hkeep 3 (by decide) (by decide)
    · simpa [S, pick, CurrentAdditive.GaussPhysical.cellBank] using
        hkeep 2 (by decide) (by decide)

end CurrentAdditive.GaussPhysical.GaussBranchSelect
