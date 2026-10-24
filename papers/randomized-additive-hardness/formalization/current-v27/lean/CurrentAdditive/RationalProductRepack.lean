import CurrentAdditive.RationalProductCodeDBridge
import EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming
import EthInapproximability.CurrentPaper.BitMachineBankSerialize

/-!
Physical continuation of the frozen twelve-field rational product packet.
The parser loads all twelve fields.  Bank 1 and bank 2 are cleared; bank 6
is then popped into bank 1, reversing its little-endian denominator word.
The serializer emits the empty sign field, bank 0, and bank 1 as precisely
the three fields of `CodeDCodec.RawRat`.
-/

namespace EthInapproximability.CurrentPaper.RationalProductRepack

set_option maxRecDepth 4096

open Turing TM2.Stmt BitMachineEncoding BitMachineComposition

abbrev Stack := BitMachineBankCodec.Stack 12
abbrev Bank := BitMachineBankCodec.Bank 12

inductive Admin where
  | parsed | clearOne | clearTwo | reverse
  deriving DecidableEq, Fintype

abbrev Label := BitMachineBankCodec.ParserLabel 12 ⊕
  (BitMachineBankSerialize.Label 3 ⊕ Admin)
abbrev Control := Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def serPerm : Fin 15 ≃ Fin 15 where
  toFun := ![2,0,1,12,13,14,3,4,5,6,7,8,9,10,11]
  invFun := ![1,2,0,6,7,8,9,10,11,12,13,14,3,4,5]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def serStack : (BitMachineBankSerialize.Stack 3 ⊕ Fin 9) ≃ Stack :=
  (((finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6).sumCongr
    (Equiv.refl (Fin 9))).trans
    (finSumFinEquiv : (Fin 6 ⊕ Fin 9) ≃ Fin 15)).trans
    serPerm |>.trans (finSumFinEquiv : Stack ≃ Fin 15).symm

def serLabel : (BitMachineBankSerialize.Label 3 ⊕
    (BitMachineBankCodec.ParserLabel 12 ⊕ Admin)) ≃ Label where
  toFun := fun x => match x with
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inl l
    | .inr (.inr a) => .inr (.inr a)
  invFun := fun x => match x with
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inl l
    | .inr (.inr a) => .inr (.inr a)
  left_inv := by intro x; rcases x with x | (x | x) <;> rfl
  right_inv := by intro x; rcases x with x | (x | x) <;> rfl

def serControl : (Option Bool × Unit) ≃ Control where
  toFun := Prod.fst
  invFun := fun v => (v, ())
  left_inv := by intro x; rcases x with ⟨x, ⟨⟩⟩; rfl
  right_inv := by intro x; rfl

def serStmt (l : BitMachineBankSerialize.Label 3) :
    TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  renameStmt serStack serLabel serControl
    (liftStmt (none : Option (BitMachineBankCodec.ParserLabel 12 ⊕ Admin))
      (BitMachineBankSerialize.program 3 l))

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineInline.stmt Sum.inl id id
      (some (.inr (.inr .parsed))) (BitMachineBankCodec.parser 12 l)
  | .inr (.inl l) => serStmt l
  | .inr (.inr .parsed) => branch (fun v => v.getD false)
      (goto (fun _ => .inr (.inr .clearOne))) halt
  | .inr (.inr .clearOne) => pop (.inl 1) (fun _ b => b)
      (branch Option.isSome (goto (fun _ => .inr (.inr .clearOne)))
        (goto (fun _ => .inr (.inr .clearTwo))))
  | .inr (.inr .clearTwo) => pop (.inl 2) (fun _ b => b)
      (branch Option.isSome (goto (fun _ => .inr (.inr .clearTwo)))
        (goto (fun _ => .inr (.inr .reverse))))
  | .inr (.inr .reverse) => pop (.inl 6) (fun _ b => b)
      (branch Option.isSome
        (push (.inl 1) (fun v => v.getD false)
          (goto (fun _ => .inr (.inr .reverse))))
        (load (fun _ => none) (goto (fun _ => .inr (.inl (.emit 0))))))

def cfg (l : Option Label) (v : Control) (S : Bank)
    (source saved output : List Bool) : Config :=
  ⟨l, v, BitMachineBankCodec.contents S source saved output⟩

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add (t u : ℕ) (c : Config) : run (t+u) c = run u (run t c) := by
  simpa only [run, Nat.add_comm] using Function.iterate_add_apply (advance program) u t c

theorem run_succ (t : ℕ) (c : Config) :
    run (t+1) c = run t (advance program c) :=
  Function.iterate_succ_apply _ _ _

theorem parse_run (input : List Bool) (S : Bank)
    (hd : BitMachineBankCodec.decode 12 input = some S) :
    ∃ t ≤ 25*(input.length+1),
      run t (cfg (some (.inl (.scan 0))) none (fun _ => []) input [] []) =
        cfg (some (.inr (.inr .parsed))) (some true) S [] [] [] := by
  obtain ⟨t, ht, hp⟩ := BitMachineBankCodec.parser_correct 12 input []
  rw [hd] at hp
  change BitMachineBankCodec.parserRun t
    (BitMachineBankCodec.parserCfg (some (.scan 0)) none (fun _ => []) input [] []) =
      BitMachineBankCodec.parserCfg none (some true) S [] [] [] at hp
  have hh := congrArg (fun c => c.l) hp
  change _ = none at hh
  obtain ⟨u, hu, hr⟩ := BitMachineInline.outputs
    (Sum.inl : BitMachineBankCodec.ParserLabel 12 → Label) id id
    (fun _ => rfl) (some (.inr (.inr .parsed)))
    (BitMachineBankCodec.parser 12) program (fun _ => rfl)
    (BitMachineBankCodec.parserCfg (some (.scan 0)) none (fun _ => []) input [] []) t hh
  refine ⟨u, hu.trans ht, ?_⟩
  unfold BitMachineBankCodec.parserRun at hp
  rw [hp] at hr
  exact hr

theorem reject_run (input : List Bool)
    (hd : BitMachineBankCodec.decode 12 input = none) :
    ∃ t ≤ 25*(input.length+1)+1,
      let c := run t (cfg (some (.inl (.scan 0))) none (fun _ => []) input [] [])
      c.l = none ∧ c.stk (.inr 2) = [] := by
  obtain ⟨t, ht, hp⟩ := BitMachineBankCodec.parser_correct 12 input []
  rw [hd] at hp
  change (BitMachineBankCodec.parserRun t _).l = none ∧
    (BitMachineBankCodec.parserRun t _).var = some false ∧
    (BitMachineBankCodec.parserRun t _).stk (.inr 2) = [] at hp
  let c : TM2.Cfg (fun _ : Stack => Bool) (BitMachineBankCodec.ParserLabel 12) Control :=
    BitMachineBankCodec.parserRun t
      (BitMachineBankCodec.parserCfg (some (.scan 0)) none (fun _ => []) input [] [])
  change c.l = none ∧ c.var = some false ∧ c.stk (.inr 2) = [] at hp
  obtain ⟨u, hu, hr⟩ := BitMachineInline.outputs
    (Sum.inl : BitMachineBankCodec.ParserLabel 12 → Label) id id
    (fun _ => rfl) (some (.inr (.inr .parsed)))
    (BitMachineBankCodec.parser 12) program (fun _ => rfl)
    (BitMachineBankCodec.parserCfg (some (.scan 0)) none (fun _ => []) input [] []) t hp.1
  have hf : advance program
      (BitMachineInline.cfg (Sum.inl : BitMachineBankCodec.ParserLabel 12 → Label) id
        (some (.inr (.inr .parsed))) c) =
      (⟨none, some false, c.stk⟩ : Config) := by
    simp only [BitMachineInline.cfg, hp.1, hp.2.1, id_eq, advance, TM2.step,
      program, TM2.stepAux, Option.getD_some, cond_false]
  refine ⟨u+1, by omega, ?_⟩
  change _ ∧ _
  change run u (cfg (some (.inl (.scan 0))) none (fun _ => []) input [] []) =
    BitMachineInline.cfg (Sum.inl : BitMachineBankCodec.ParserLabel 12 → Label) id
      (some (.inr (.inr .parsed))) c at hr
  rw [run_add]
  simp only [run, Function.iterate_one] at hr ⊢
  rw [hr, hf]
  exact ⟨rfl, hp.2.2⟩

def clearStmt (source : Stack) (again next : Label) :
    TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  pop source (fun _ b => b)
    (branch Option.isSome (goto (fun _ => again)) (goto (fun _ => next)))

theorem clear_loop (source : Stack) (again next : Label)
    (hp : program again = clearStmt source again next)
    (v : Control) (S : Stack → List Bool) :
    run ((S source).length+1) ⟨some again, v, S⟩ =
      ⟨some next, none, Function.update S source []⟩ := by
  generalize hs : S source = word
  induction word generalizing S v with
  | nil =>
      simp [run, advance, TM2.step, hp, clearStmt, TM2.stepAux, hs]
  | cons b word ih =>
      have hstep : advance program ⟨some again, v, S⟩ =
          (⟨some again, some b, Function.update S source word⟩ : Config) := by
        simp [advance, TM2.step, hp, clearStmt, TM2.stepAux, hs]
      rw [List.length_cons, run_succ, hstep,
        ih (some b) (Function.update S source word) (Function.update_self source word S)]
      congr 1
      funext k
      by_cases hk : k = source <;> simp [Function.update_apply, hk]

theorem clearOne_run (v : Control) (S : Stack → List Bool) :
    run ((S (.inl 1)).length+1)
      ⟨some (.inr (.inr .clearOne)), v, S⟩ =
      ⟨some (.inr (.inr .clearTwo)), none, Function.update S (.inl 1) []⟩ := by
  apply clear_loop
  rfl

theorem clearTwo_run (v : Control) (S : Stack → List Bool) :
    run ((S (.inl 2)).length+1)
      ⟨some (.inr (.inr .clearTwo)), v, S⟩ =
      ⟨some (.inr (.inr .reverse)), none, Function.update S (.inl 2) []⟩ := by
  apply clear_loop
  rfl

theorem reverse_nil (v : Control) (S : Stack → List Bool)
    (hs : S (.inl 6) = []) :
    advance program ⟨some (.inr (.inr .reverse)), v, S⟩ =
      ⟨some (.inr (.inl (.emit 0))), none, S⟩ := by
  simp [advance, TM2.step, program, TM2.stepAux, hs]

theorem reverse_cons (v : Control) (S : Stack → List Bool)
    (b : Bool) (word : List Bool) (hs : S (.inl 6) = b :: word) :
    advance program ⟨some (.inr (.inr .reverse)), v, S⟩ =
      ⟨some (.inr (.inr .reverse)), some b,
        Function.update (Function.update S (.inl 6) word)
          (.inl 1) (b :: S (.inl 1))⟩ := by
  simp [advance, TM2.step, program, TM2.stepAux, hs,
    show (.inl (1 : Fin 12) : Stack) ≠ .inl 6 by decide]

theorem reverse_run (v : Control) (S : Stack → List Bool) :
    run ((S (.inl 6)).length+1)
      ⟨some (.inr (.inr .reverse)), v, S⟩ =
      ⟨some (.inr (.inl (.emit 0))), none,
        Function.update (Function.update S (.inl 6) [])
          (.inl 1) ((S (.inl 6)).reverse ++ S (.inl 1))⟩ := by
  generalize hs : S (.inl 6) = word
  induction word generalizing S v with
  | nil =>
      simp only [List.length_nil, Nat.zero_add, run, Function.iterate_one,
        List.reverse_nil, List.nil_append]
      rw [reverse_nil v S hs]
      congr 1
      funext k
      by_cases hk6 : k = (.inl 6 : Stack)
      · subst k; simp [hs]
      · by_cases hk1 : k = (.inl 1 : Stack)
        · subst k; simp
        · simp [hk6, hk1]
  | cons b word ih =>
      rw [List.length_cons, run_succ, reverse_cons v S b word hs,
        ih (some b) (Function.update (Function.update S (.inl 6) word)
          (.inl 1) (b :: S (.inl 1))) (by simp)]
      congr 1
      funext k
      fin_cases k <;> simp [Function.update_apply, List.reverse_cons,
        List.append_assoc, hs]

def serWords (S : Stack → List Bool) : BitMachineBankSerialize.Bank 3 :=
  ![[], S (.inl 0), S (.inl 1)]

def serForeign (S : Stack → List Bool) : Fin 9 → List Bool :=
  fun j => S (.inl ⟨j.val+3, by omega⟩)

theorem ser_initial (S : Stack → List Bool)
    (h2 : S (.inl 2) = [])
    (ha : ∀ j : Fin 3, S (.inr j) = []) :
    renameCfg serStack serLabel serControl
      (liftCfg none () (serForeign S)
        (BitMachineBankSerialize.cfg (some (.emit 0)) none (serWords S) [] [] [])) =
      (⟨some (.inr (.inl (.emit 0))), none, S⟩ : Config) := by
  unfold renameCfg liftCfg BitMachineBankSerialize.cfg
  simp only [Option.map_some, serLabel, serControl]
  congr 1
  funext k
  cases k with
  | inl k =>
      fin_cases k <;> simp [serStack, serPerm, serWords, serForeign,
        BitMachineBankSerialize.contents, finSumFinEquiv, Fin.addCases, h2]
  | inr k =>
      fin_cases k <;> simp [serStack, serPerm, serWords, serForeign,
        BitMachineBankSerialize.contents, finSumFinEquiv, Fin.addCases, ha]

theorem ser_output (S : Stack → List Bool)
    (source : List Bool) (words : BitMachineBankSerialize.Bank 3)
    (T : BitMachineBankSerialize.Bank 3) :
    (renameCfg serStack serLabel serControl
      (liftCfg none () (serForeign S)
        (BitMachineBankSerialize.cfg none none T source []
          (BitMachineBankSerialize.encode (List.ofFn words))))).stk (.inr 2) =
      BitMachineBankSerialize.encode (List.ofFn words) := by
  have hk : serStack.symm (.inr (2 : Fin 3)) =
      (.inl (.inr (2 : Fin 3)) : BitMachineBankSerialize.Stack 3 ⊕ Fin 9) := by decide
  simp [renameCfg, liftCfg, BitMachineBankSerialize.cfg,
    BitMachineBankSerialize.contents, hk]

theorem serialize_run (S : Stack → List Bool)
    (h2 : S (.inl 2) = []) (ha : ∀ j : Fin 3, S (.inr j) = []) :
    ∃ t ≤ 2*(BitMachineBankSerialize.encode (List.ofFn (serWords S))).length+2,
      let c := run t ⟨some (.inr (.inl (.emit 0))), none, S⟩
      c.l = none ∧ c.stk (.inr 2) =
        BitMachineBankSerialize.encode (List.ofFn (serWords S)) := by
  obtain ⟨t,T,ht,hs⟩ := BitMachineBankSerialize.serialize (serWords S) [] []
  have hh := congrArg (fun c => c.l) hs
  change _ = none at hh
  obtain ⟨u,hu,hr⟩ := BitMachineSubroutineRenaming.lift_outputs_renamed
    serStack serLabel serControl (BitMachineBankSerialize.program 3) program
    (none : Option (BitMachineBankCodec.ParserLabel 12 ⊕ Admin))
    (by intro l; rfl) () (serForeign S)
    (BitMachineBankSerialize.cfg (some (.emit 0)) none (serWords S) [] [] []) t hh
  refine ⟨u, hu.trans ht, ?_⟩
  dsimp only
  change run u _ = _ at hr
  rw [ser_initial S h2 ha] at hr
  unfold BitMachineBankSerialize.run at hs
  rw [hs] at hr
  rw [hr]
  constructor
  · rfl
  · simpa only [List.append_nil] using ser_output S [] (serWords S) T

def repackBank (S : Bank) : BitMachineBankCodec.Bank 3 :=
  ![[], S 0, (S 6).reverse]

def result (input : List Bool) : List Bool :=
  match BitMachineBankCodec.decode 12 input with
  | none => []
  | some S => BitMachineBankCodec.encode (repackBank S)

noncomputable def machine : BitMachine.Machine :=
  ofFinite (.inr 0) (.inr 2) (.inl (.scan 0)) none program

theorem parsed_step (S : Bank) :
    advance program (cfg (some (.inr (.inr .parsed))) (some true) S [] [] []) =
      ⟨some (.inr (.inr .clearOne)), some true,
        BitMachineBankCodec.contents S [] [] []⟩ := rfl

theorem initial_cfg (input : List Bool) :
    rawInit (.inr 0 : Stack) (.inl (.scan 0) : Label) none input =
      cfg (some (.inl (.scan 0))) none (fun _ => []) input [] [] := by
  unfold rawInit cfg BitMachineBankCodec.contents
  congr 1
  funext k
  cases k with
  | inl k => simp
  | inr k => fin_cases k <;> rfl

theorem valid_run (input : List Bool) (S : Bank)
    (hd : BitMachineBankCodec.decode 12 input = some S) :
    ∃ t ≤ 40*(input.length+1),
      let c := run t (cfg (some (.inl (.scan 0))) none (fun _ => []) input [] [] )
      c.l = none ∧ c.stk (.inr 2) = BitMachineBankCodec.encode (repackBank S) := by
  let B₀ : Stack → List Bool := BitMachineBankCodec.contents S [] [] []
  let B₁ := Function.update B₀ (.inl 1) []
  let B₂ := Function.update B₁ (.inl 2) []
  let B₃ := Function.update (Function.update B₂ (.inl 6) [])
    (.inl 1) ((S 6).reverse)
  obtain ⟨a,ha,hp⟩ := parse_run input S hd
  have hstep : advance program
      (cfg (some (.inr (.inr .parsed))) (some true) S [] [] []) =
      ⟨some (.inr (.inr .clearOne)), some true, B₀⟩ := parsed_step S
  have hclear1 : run ((S 1).length+1)
      ⟨some (.inr (.inr .clearOne)), some true, B₀⟩ =
      ⟨some (.inr (.inr .clearTwo)), none, B₁⟩ := by
    simpa only [show B₀ (.inl 1) = S 1 from rfl] using
      clearOne_run (some true) B₀
  have hclear2 : run ((S 2).length+1)
      ⟨some (.inr (.inr .clearTwo)), none, B₁⟩ =
      ⟨some (.inr (.inr .reverse)), none, B₂⟩ := by
    simpa only [show B₁ (.inl 2) = S 2 by rfl] using clearTwo_run none B₁
  have hreverse : run ((S 6).length+1)
      ⟨some (.inr (.inr .reverse)), none, B₂⟩ =
      ⟨some (.inr (.inl (.emit 0))), none, B₃⟩ := by
    have h6 : B₂ (.inl 6) = S 6 := by rfl
    have h1 : B₂ (.inl 1) = [] := by rfl
    simpa only [h6, h1, List.append_nil] using reverse_run none B₂
  have h2 : B₃ (.inl 2) = [] := by rfl
  have haux : ∀ j : Fin 3, B₃ (.inr j) = [] := by
    intro j; fin_cases j <;> rfl
  obtain ⟨z,hz,hser⟩ := serialize_run B₃ h2 haux
  have hwords : serWords B₃ = repackBank S := by
    funext j; fin_cases j <;> rfl
  have hencode : BitMachineBankSerialize.encode (List.ofFn (serWords B₃)) =
      BitMachineBankCodec.encode (repackBank S) := by
    rw [hwords, BitMachineBankCodec.encode_eq_list]
    rfl
  have hlen0 := BitMachineBankCodec.decoded_word_length hd (0 : Fin 12)
  have hlen1 := BitMachineBankCodec.decoded_word_length hd (1 : Fin 12)
  have hlen2 := BitMachineBankCodec.decoded_word_length hd (2 : Fin 12)
  have hlen6 := BitMachineBankCodec.decoded_word_length hd (6 : Fin 12)
  have hout : (BitMachineBankCodec.encode (repackBank S)).length ≤
      4*input.length+3 := by
    rw [BitMachineBankCodec.encode_length]
    simp [Fin.sum_univ_succ, repackBank]
    omega
  refine ⟨a+1+((S 1).length+1)+((S 2).length+1)+((S 6).length+1)+z,
    ?_, ?_⟩
  · rw [hencode] at hz
    omega
  · dsimp only
    have hrun : run (a+1+((S 1).length+1)+((S 2).length+1)+
        ((S 6).length+1)+z)
        (cfg (some (.inl (.scan 0))) none (fun _ => []) input [] []) =
        run z (run ((S 6).length+1) (run ((S 2).length+1)
          (run ((S 1).length+1) (run 1
            (run a (cfg (some (.inl (.scan 0))) none (fun _ => []) input [] [])))))) := by
      simp only [← run_add]
    rw [hrun, hp]
    have hone : run 1 (cfg (some (.inr (.inr .parsed))) (some true) S [] [] []) =
        ⟨some (.inr (.inr .clearOne)), some true, B₀⟩ := hstep
    rw [hone, hclear1, hclear2, hreverse]
    change (run z ⟨some (.inr (.inl (.emit 0))), none, B₃⟩).l = none ∧
      (run z ⟨some (.inr (.inl (.emit 0))), none, B₃⟩).stk (.inr 2) = _
    rw [← hencode]
    exact hser

theorem outputs (input : List Bool) :
    machine.OutputsWithin input (result input) (40*(input.length+1)) := by
  cases hd : BitMachineBankCodec.decode 12 input with
  | none =>
      obtain ⟨t,ht,hh,ho⟩ := reject_run input hd
      apply outputsWithin_of_raw_run (.inr 0 : Stack) (.inr 2)
        (.inl (.scan 0)) none program input (result input) t _ (by omega)
      · simpa only [initial_cfg, run] using hh
      · simpa only [initial_cfg, run, result, hd] using ho
  | some S =>
      obtain ⟨t,ht,hh,ho⟩ := valid_run input S hd
      apply outputsWithin_of_raw_run (.inr 0 : Stack) (.inr 2)
        (.inl (.scan 0)) none program input (result input) t _ ht
      · simpa only [initial_cfg, run] using hh
      · simpa only [initial_cfg, run, result, hd] using ho

theorem polytime : BitMachine.Polytime result := by
  refine ⟨machine, 40, 1, ?_⟩
  intro input
  simpa only [pow_one] using outputs input

theorem result_encoded (S : Bank) :
    result (BitMachineBankCodec.encode S) =
      BitMachineBankCodec.encode (repackBank S) := by
  simp [result]

def readRawRat (bits : List Bool) : Option CurrentAdditive.CodeDCodec.RawRat :=
  CurrentAdditive.CodeDCodec.decodeRawRat bits

theorem result_eq_rawRat (S : Bank) :
    result (BitMachineBankCodec.encode S) =
      CurrentAdditive.CodeDCodec.encodeRawRat
        ⟨false, S 0, (S 6).reverse⟩ := by
  rw [result_encoded]
  apply congrArg
  funext i
  fin_cases i <;> rfl

end EthInapproximability.CurrentPaper.RationalProductRepack
