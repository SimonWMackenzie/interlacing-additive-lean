import EthInapproximability.CurrentPaper.BitMachineBankCodec
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding
import EthInapproximability.CurrentPaper.BitMachineBankSerialize

/-! Literal packet reassociation. The program parses both input records,
serializes the new inner record, then serializes the outer record. -/

namespace CurrentAdditive.CylinderEvalReassociate

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineBankCodec

abbrev Stack := Fin 12

inductive Label where
  | parse (context : Bool) (l : ParserLabel 2)
  | emit (outer : Bool) (l : BitMachineBankSerialize.Label 2)
  | afterParse (context : Bool)
  | afterEmit
  deriving DecidableEq,Fintype

def parseStack (p : Bool) : BitMachineBankCodec.Stack 2 ↪ Stack :=
  if p then {
    toFun := Sum.elim (fun k => ![5,6] k) (fun k => ![3,1,2] k)
    inj' := by decide } else {
    toFun := Sum.elim (fun k => ![3,4] k) (fun k => ![0,1,2] k)
    inj' := by decide }

def emitStack (p : Bool) : BitMachineBankSerialize.Stack 2 ↪ Stack :=
  if p then {
    toFun := Sum.elim (fun k => ![7,6] k) (fun k => ![9,8,10] k)
    inj' := by decide } else {
    toFun := Sum.elim (fun k => ![5,4] k) (fun k => ![9,8,7] k)
    inj' := by decide }

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .parse p l => BitMachineStackEmbedding.stmt (parseStack p) (.parse p)
      id id (some (.afterParse p)) (parser 2 l)
  | .emit p l => BitMachineStackEmbedding.stmt (emitStack p) (.emit p)
      id id (if p then none else some .afterEmit) (BitMachineBankSerialize.program 2 l)
  | .afterParse false => .load (fun _ => none) (.goto (fun _ => .parse true (.scan 0)))
  | .afterParse true => .load (fun _ => none) (.goto (fun _ => .emit false (.emit 0)))
  | .afterEmit => .load (fun _ => none) (.goto (fun _ => .emit true (.emit 0)))

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label (Option Bool)
def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

noncomputable def parseFrame (p : Bool) (S : Stack → List Bool)
    (c : TM2.Cfg (fun _ : BitMachineBankCodec.Stack 2 => Bool) (ParserLabel 2) (Option Bool)) : Config :=
  BitMachineStackEmbedding.cfg (parseStack p) S (.parse p) id (some (.afterParse p)) c

noncomputable def emitFrame (p : Bool) (S : Stack → List Bool)
    (c : TM2.Cfg (fun _ : BitMachineBankSerialize.Stack 2 => Bool)
      (BitMachineBankSerialize.Label 2) (Option Bool)) : Config :=
  BitMachineStackEmbedding.cfg (emitStack p) S (.emit p) id
    (if p then none else some .afterEmit) c

theorem run_add {c c' : Config} {n : ℕ} (h : run n c=c') (m : ℕ) :
    run (n+m) c=run m c' := by
  rw [Nat.add_comm,run,Function.iterate_add_apply]
  exact congrArg (run m) h

private theorem embeddedBank_eq {K J : Type} [DecidableEq K] [DecidableEq J]
    (e : K ↪ J) (S : J → List Bool) (T : K → List Bool) (U : J → List Bool)
    (hin : ∀ k,U (e k)=T k) (hout : ∀ j, (¬∃ k,e k=j) → U j=S j) :
    BitMachineStackEmbedding.bank e S T=U := by
  classical
  funext j
  by_cases h : ∃ k,e k=j
  · obtain ⟨k,rfl⟩ := h
    rw [BitMachineStackEmbedding.bank_at]
    exact (hin k).symm
  · rw [BitMachineStackEmbedding.bank_outside _ _ _ _ h]
    exact (hout j h).symm

def input (q a b : List Bool) : List Bool := encode ![encode ![q,a],b]
def output (q a b : List Bool) : List Bool := encode ![encode ![q,b],a]

def parseWords (p : Bool) (q a b : List Bool) : Bank 2 :=
  if p then ![q,a] else ![encode ![q,a],b]

def stage (p : Bool) (q a b : List Bool) : Stack → List Bool :=
  if p then fun k => if k=3 then encode ![q,a] else if k=4 then b else []
  else fun k => if k=0 then input q a b else []

def loaded (q a b : List Bool) : Stack → List Bool :=
  fun k => if k=4 then b else if k=5 then q else if k=6 then a else []

def parsedStage (p : Bool) (q a b : List Bool) : Stack → List Bool :=
  if p then loaded q a b else stage true q a b

theorem parse_initial (p : Bool) (q a b : List Bool) :
    parseFrame p (stage p q a b)
      (parserCfg (some (.scan 0)) none (fun _ => []) (encode (parseWords p q a b)) [] []) =
      ⟨some (.parse p (.scan 0)),none,stage p q a b⟩ := by
  unfold parseFrame BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg BitMachineInline.cfg
  congr 1
  apply BitMachineStackEmbedding.bank_eq_self
  intro k
  cases p <;> cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

theorem parse_final (p : Bool) (q a b : List Bool) :
    parseFrame p (stage p q a b)
      (parserCfg none (some true) (parseWords p q a b) [] [] []) =
      ⟨some (.afterParse p),some true,parsedStage p q a b⟩ := by
  unfold parseFrame BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg BitMachineInline.cfg
  congr 1
  apply embeddedBank_eq
  · intro k
    cases p <;> cases k with
    | inl k => fin_cases k <;> rfl
    | inr k => fin_cases k <;> rfl
  · intro k hk
    cases p <;> fin_cases k
    all_goals first
      | rfl
      | exact (hk ⟨Sum.inl (0 : Fin 2),rfl⟩).elim
      | exact (hk ⟨Sum.inl (1 : Fin 2),rfl⟩).elim
      | exact (hk ⟨Sum.inr (0 : Fin 3),rfl⟩).elim

theorem parse_run (p : Bool) (q a b : List Bool) :
    ∃ t≤5*((encode (parseWords p q a b)).length+1),
      run t ⟨some (.parse p (.scan 0)),none,stage p q a b⟩ =
      ⟨some (.afterParse p),some true,parsedStage p q a b⟩ := by
  let words := parseWords p q a b
  obtain ⟨t,ht,hr⟩ := parser_correct 2 (encode words) []
  rw [decode_encode] at hr
  change BitMachineBankCodec.parserRun t
    (parserCfg (some (.scan 0)) none (fun _ => []) (encode words) [] []) =
    parserCfg none (some true) words [] [] [] at hr
  obtain ⟨u,hu,he⟩ := BitMachineStackEmbedding.outputs (parseStack p) (stage p q a b)
    (.parse p) id id (by intro v; rfl) (some (.afterParse p))
    (parser 2) program (by intro l; rfl)
    (parserCfg (some (.scan 0)) none (fun _ => []) (encode words) [] []) t
    (by change (BitMachineBankCodec.parserRun t _).l=none; rw [hr]; rfl)
  change run u (parseFrame p _ _) = parseFrame p _ (BitMachineBankCodec.parserRun t _) at he
  rw [hr,parse_initial,parse_final] at he
  exact ⟨u,hu.trans ht,he⟩

theorem loaded_run (q a b : List Bool) :
    ∃ t≤10*((input q a b).length+1)+1,
      run t ⟨some (.parse false (.scan 0)),none,stage false q a b⟩ =
      ⟨some (.afterParse true),some true,loaded q a b⟩ := by
  obtain ⟨t,ht,hr⟩ := parse_run false q a b
  obtain ⟨u,hu,he⟩ := parse_run true q a b
  have hstep : run 1 ⟨some (.afterParse false),some true,parsedStage false q a b⟩=
      ⟨some (.parse true (.scan 0)),none,stage true q a b⟩ := rfl
  have htotal := (run_add ((run_add hr 1).trans hstep) u).trans he
  have hctx := word_length_le_encode (![encode ![q,a],b]) (0 : Fin 2)
  change (encode ![q,a]).length≤(input q a b).length at hctx
  change t≤5*((input q a b).length+1) at ht
  change u≤5*((encode ![q,a]).length+1) at hu
  exact ⟨t+1+u,by omega,htotal⟩

theorem emitBank_at (p : Bool) (S : Stack → List Bool)
    (T : BitMachineBankSerialize.Stack 2 → List Bool) (k : Stack) :
    BitMachineStackEmbedding.bank (emitStack p) S T k =
      if k=(if p then 7 else 5) then T (.inl 0)
      else if k=(if p then 6 else 4) then T (.inl 1)
      else if k=9 then T (.inr 0) else if k=8 then T (.inr 1)
      else if k=(if p then 10 else 7) then T (.inr 2) else S k := by
  cases p <;> fin_cases k
  all_goals first
    | exact BitMachineStackEmbedding.bank_at (emitStack _) S T (Sum.inl (0 : Fin 2))
    | exact BitMachineStackEmbedding.bank_at (emitStack _) S T (Sum.inl (1 : Fin 2))
    | exact BitMachineStackEmbedding.bank_at (emitStack _) S T (Sum.inr (0 : Fin 3))
    | exact BitMachineStackEmbedding.bank_at (emitStack _) S T (Sum.inr (1 : Fin 3))
    | exact BitMachineStackEmbedding.bank_at (emitStack _) S T (Sum.inr (2 : Fin 3))
    | exact BitMachineStackEmbedding.bank_outside (emitStack _) S T _ (by decide)

theorem emit_run (p : Bool) (S : Stack → List Bool) (words : Bank 2) :
    ∃ (t : ℕ) (words' : Bank 2), t≤2*(encode words).length+2 ∧
      run t (emitFrame p S (BitMachineBankSerialize.cfg (some (.emit 0)) none words [] [] [])) =
      emitFrame p S (BitMachineBankSerialize.cfg none none words' [] [] (encode words)) := by
  obtain ⟨t,T,ht,hr⟩ := BitMachineBankSerialize.serialize words [] []
  have hencode : BitMachineBankSerialize.encode (List.ofFn words)=encode words :=
    (BitMachineBankCodec.encode_eq_list words).symm
  rw [hencode,List.append_nil] at hr
  rw [hencode] at ht
  obtain ⟨u,hu,he⟩ := BitMachineStackEmbedding.outputs (emitStack p) S (.emit p) id id
    (by intro v; rfl) (if p then none else some .afterEmit)
    (BitMachineBankSerialize.program 2) program (by intro l; rfl)
    (BitMachineBankSerialize.cfg (some (.emit 0)) none words [] [] []) t
    (by change (BitMachineBankSerialize.run t _).l=none; rw [hr]; rfl)
  change run u (emitFrame p S _) = emitFrame p S (BitMachineBankSerialize.run t _) at he
  rw [hr] at he
  exact ⟨u,T,hu.trans ht,he⟩

theorem inner_ready (q a b : List Bool) :
    emitFrame false (loaded q a b)
      (BitMachineBankSerialize.cfg (some (.emit 0)) none (![q,b]) [] [] []) =
      ⟨some (.emit false (.emit 0)),none,loaded q a b⟩ := by
  unfold emitFrame BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg BitMachineInline.cfg
  congr 1
  apply BitMachineStackEmbedding.bank_eq_self
  intro k; cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

theorem loaded_to_inner (q a b : List Bool) :
    run 1 ⟨some (.afterParse true),some true,loaded q a b⟩ =
      emitFrame false (loaded q a b)
        (BitMachineBankSerialize.cfg (some (.emit 0)) none (![q,b]) [] [] []) := by
  rw [inner_ready]
  rfl

noncomputable def innerFinal (q a b : List Bool) (T : Bank 2) : Config :=
  emitFrame false (loaded q a b)
    (BitMachineBankSerialize.cfg none none T [] [] (encode ![q,b]))

theorem innerFinal_at (q a b : List Bool) (T : Bank 2) (k : Stack) :
    (innerFinal q a b T).stk k =
      if k=5 then T 0 else if k=4 then T 1 else if k=9 then [] else if k=8 then []
      else if k=7 then encode ![q,b] else loaded q a b k := by
  change BitMachineStackEmbedding.bank (emitStack false) (loaded q a b)
    (BitMachineBankSerialize.contents T [] [] (encode ![q,b])) k = _
  rw [emitBank_at]
  simp [BitMachineBankSerialize.contents]

theorem outer_ready (q a b : List Bool) (T : Bank 2) :
    emitFrame true (innerFinal q a b T).stk
      (BitMachineBankSerialize.cfg (some (.emit 0)) none (![encode ![q,b],a]) [] [] []) =
      ⟨some (.emit true (.emit 0)),none,(innerFinal q a b T).stk⟩ := by
  unfold emitFrame BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg BitMachineInline.cfg
  congr 1
  apply BitMachineStackEmbedding.bank_eq_self
  intro k; cases k with
  | inl k => fin_cases k <;> simp [emitStack,innerFinal_at,
      BitMachineBankSerialize.cfg,BitMachineBankSerialize.contents,loaded]
  | inr k => fin_cases k <;> simp [emitStack,innerFinal_at,
      BitMachineBankSerialize.cfg,BitMachineBankSerialize.contents,loaded]

theorem inner_to_outer (q a b : List Bool) (T : Bank 2) :
    run 1 (innerFinal q a b T) =
      emitFrame true (innerFinal q a b T).stk
        (BitMachineBankSerialize.cfg (some (.emit 0)) none (![encode ![q,b],a]) [] [] []) := by
  rw [outer_ready]
  unfold innerFinal emitFrame BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg BitMachineInline.cfg
  rfl

end CurrentAdditive.CylinderEvalReassociate

#print axioms CurrentAdditive.CylinderEvalReassociate.loaded_run
#print axioms CurrentAdditive.CylinderEvalReassociate.inner_to_outer
