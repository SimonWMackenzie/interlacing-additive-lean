import CurrentAdditive.CylinderEvalReassociateMachine

/-! The prepared three-field packet is physically parsed before the same
serializers produce Bank2(Bank2(q,tuples),features). -/
namespace CurrentAdditive.CylinderPreparedReassociate

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineBankCodec

abbrev Stack := CylinderEvalReassociate.Stack
inductive Label where
  | parse (l : ParserLabel 3)
  | main (l : CylinderEvalReassociate.Label)
  deriving DecidableEq,Fintype
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label (Option Bool)

def parseStack : BitMachineBankCodec.Stack 3 ↪ Stack where
  toFun := Sum.elim (fun k => ![5,6,4] k) (fun k => ![0,1,2] k)
  inj' := by decide

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .parse l => BitMachineStackEmbedding.stmt parseStack .parse id id
      (some (.main (.afterParse true))) (parser 3 l)
  | .main l => BitMachineInline.stmt .main id id none (CylinderEvalReassociate.program l)

def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

def input (q features tuples : List Bool) : List Bool := encode ![q,features,tuples]

def initial (q features tuples : List Bool) : Stack → List Bool :=
  fun k => if k=0 then input q features tuples else []

noncomputable def parseFrame (q features tuples : List Bool)
    (c : TM2.Cfg (fun _ : BitMachineBankCodec.Stack 3 => Bool) (ParserLabel 3) (Option Bool)) : Config :=
  BitMachineStackEmbedding.cfg parseStack (initial q features tuples) .parse id
    (some (.main (.afterParse true))) c

theorem parseBank_at (S : Stack → List Bool)
    (T : BitMachineBankCodec.Stack 3 → List Bool) (k : Stack) :
    BitMachineStackEmbedding.bank parseStack S T k =
      if k=5 then T (.inl 0) else if k=6 then T (.inl 1)
      else if k=4 then T (.inl 2) else if k=0 then T (.inr 0)
      else if k=1 then T (.inr 1) else if k=2 then T (.inr 2) else S k := by
  fin_cases k
  all_goals first
    | exact BitMachineStackEmbedding.bank_at parseStack S T (Sum.inl (0 : Fin 3))
    | exact BitMachineStackEmbedding.bank_at parseStack S T (Sum.inl (1 : Fin 3))
    | exact BitMachineStackEmbedding.bank_at parseStack S T (Sum.inl (2 : Fin 3))
    | exact BitMachineStackEmbedding.bank_at parseStack S T (Sum.inr (0 : Fin 3))
    | exact BitMachineStackEmbedding.bank_at parseStack S T (Sum.inr (1 : Fin 3))
    | exact BitMachineStackEmbedding.bank_at parseStack S T (Sum.inr (2 : Fin 3))
    | exact BitMachineStackEmbedding.bank_outside parseStack S T _ (by decide)

theorem parse_initial (q features tuples : List Bool) :
    parseFrame q features tuples
      (parserCfg (some (.scan 0)) none (fun _ => []) (input q features tuples) [] []) =
      rawInit (0 : Stack) (.parse (.scan 0) : Label) none (input q features tuples) := by
  unfold parseFrame BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg rawInit
  congr 1
  funext k
  rw [parseBank_at]
  fin_cases k <;> rfl

theorem parse_final (q features tuples : List Bool) :
    parseFrame q features tuples
      (parserCfg none (some true) (![q,features,tuples]) [] [] []) =
      ⟨some (.main (.afterParse true)),some true,CylinderEvalReassociate.loaded q features tuples⟩ := by
  unfold parseFrame BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg
  congr 1
  funext k
  rw [parseBank_at]
  fin_cases k <;> rfl

theorem parse_run (q features tuples : List Bool) :
    ∃ t≤7*((input q features tuples).length+1),
      run t (rawInit (0 : Stack) (.parse (.scan 0) : Label) none (input q features tuples)) =
      ⟨some (.main (.afterParse true)),some true,CylinderEvalReassociate.loaded q features tuples⟩ := by
  obtain ⟨t,ht,hr⟩ := parser_correct 3 (input q features tuples) []
  dsimp only [input] at hr
  rw [decode_encode] at hr
  change BitMachineBankCodec.parserRun (K:=3) t
    (parserCfg (some (.scan 0)) none (fun _ => []) (input q features tuples) [] []) =
    parserCfg none (some true) (![q,features,tuples]) [] [] [] at hr
  obtain ⟨u,hu,he⟩ := BitMachineStackEmbedding.outputs parseStack (initial q features tuples)
    .parse id id (by intro v; rfl) (some (.main (.afterParse true)))
    (parser 3) program (by intro l; rfl)
    (parserCfg (some (.scan 0)) none (fun _ => []) (input q features tuples) [] []) t
    (by change (BitMachineBankCodec.parserRun (K:=3) t _).l=none; rw [hr]; rfl)
  change run u (parseFrame q features tuples _) =
    parseFrame q features tuples (BitMachineBankCodec.parserRun (K:=3) t _) at he
  rw [hr,parse_initial,parse_final] at he
  exact ⟨u,hu.trans ht,he⟩

theorem input_length (q features tuples : List Bool) :
    (input q features tuples).length=2*q.length+2*features.length+2*tuples.length+3 := by
  simp [input,encode_length,Fin.sum_univ_succ]
  omega

theorem run_add {c c' : Config} {n : ℕ} (h : run n c=c') (m : ℕ) :
    run (n+m) c=run m c' := by
  rw [Nat.add_comm,run,Function.iterate_add_apply]
  exact congrArg (run m) h

theorem raw_run (q features tuples : List Bool) :
    ∃ (t : ℕ) (T U : Bank 2), t≤30*((input q features tuples).length+1) ∧
      run t (rawInit (0 : Stack) (.parse (.scan 0) : Label) none (input q features tuples)) =
        BitMachineInline.cfg Label.main id none (CylinderEvalReassociate.final q features tuples T U) := by
  obtain ⟨u,hu,hU⟩ := parse_run q features tuples
  obtain ⟨v,T,U,hv,hV⟩ := CylinderEvalReassociate.assembled_run q features tuples
  obtain ⟨w,hw,hW⟩ := BitMachineInline.outputs Label.main id id (by intro v; rfl)
    none CylinderEvalReassociate.program program (by intro l; rfl)
    (⟨some (.afterParse true),some true,CylinderEvalReassociate.loaded q features tuples⟩ : CylinderEvalReassociate.Config) v
    (by change (CylinderEvalReassociate.run v _).l=none; rw [hV]; exact CylinderEvalReassociate.final_halt _ _ _ _ _)
  change run w ⟨some (.main (.afterParse true)),some true,CylinderEvalReassociate.loaded q features tuples⟩ =
    BitMachineInline.cfg Label.main id none (CylinderEvalReassociate.run v _) at hW
  rw [hV] at hW
  refine ⟨u+w,T,U,?_,(run_add hU w).trans hW⟩
  rw [input_length] at hu ⊢
  rw [CylinderEvalReassociate.inner_length,CylinderEvalReassociate.output_length] at hv
  omega

noncomputable def machine : BitMachine.Machine :=
  ofFinite (0 : Stack) 10 (.parse (.scan 0) : Label) none program

theorem outputs (q features tuples : List Bool) :
    machine.OutputsWithin (input q features tuples) (CylinderEvalReassociate.output q features tuples)
      (30*((input q features tuples).length+1)) := by
  obtain ⟨t,T,U,ht,hr⟩ := raw_run q features tuples
  apply outputsWithin_of_raw_run (0 : Stack) 10 (.parse (.scan 0) : Label)
    none program (input q features tuples) (CylinderEvalReassociate.output q features tuples) t _ ht
  · change (run t _).l=none
    rw [hr]
    simp only [BitMachineInline.cfg,CylinderEvalReassociate.final_halt]
  · change (run t _).stk 10=CylinderEvalReassociate.output q features tuples
    rw [hr]
    exact CylinderEvalReassociate.final_output q features tuples T U

end CurrentAdditive.CylinderPreparedReassociate

#print axioms CurrentAdditive.CylinderPreparedReassociate.raw_run
#print axioms CurrentAdditive.CylinderPreparedReassociate.outputs
