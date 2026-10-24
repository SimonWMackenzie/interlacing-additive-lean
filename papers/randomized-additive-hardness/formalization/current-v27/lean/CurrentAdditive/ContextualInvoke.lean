import CurrentAdditive.ContextualInvokeBase

/-! The literal parser, invocation and serializer on one contextual packet.
Only the actual supplied execution of M on this request is used. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
namespace CurrentAdditive.ContextualInvoke
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open BitMachineBankCodec MinimumRatioContext

theorem parse_initial (M : BitMachine.Machine) (context request : List Bool) :
    parseFrame M (initialBank M context request)
      (parserCfg (some (.scan 0)) none (fun _ => []) (packet context request) [] []) =
      rawInit (low M 4) (.parse (.scan 0) : Label M) (packetControl M none) (packet context request) := by
  unfold parseFrame BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg BitMachineInline.cfg rawInit
  congr 1
  apply BitMachineStackEmbedding.bank_eq_self
  intro k; cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

theorem parse_final (M : BitMachine.Machine) (context request : List Bool) :
    parseFrame M (initialBank M context request)
      (parserCfg none (some true) (![context,request]) [] [] []) =
      ⟨some .afterParse,packetControl M (some true),loaded M context request⟩ := by
  unfold parseFrame BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg BitMachineInline.cfg
  congr 1
  apply embeddedBank_eq
  · intro k; cases k with
    | inl k => fin_cases k <;> rfl
    | inr k => fin_cases k <;> rfl
  · intro k hk
    by_cases h3 : k=low M 3
    · subst k; exact (hk ⟨Sum.inl 0,rfl⟩).elim
    by_cases h0 : k=low M 0
    · subst k; exact (hk ⟨Sum.inl 1,rfl⟩).elim
    by_cases h4 : k=low M 4
    · subst k; exact (hk ⟨Sum.inr 0,rfl⟩).elim
    simp [loaded,initialBank,h3,h0,h4]

theorem parse_run (M : BitMachine.Machine) (context request : List Bool) :
    ∃ t ≤ 5*((packet context request).length+1),
      run M t (rawInit (low M 4) (.parse (.scan 0) : Label M) (packetControl M none) (packet context request)) =
        ⟨some .afterParse,packetControl M (some true),loaded M context request⟩ := by
  obtain ⟨t,ht,hr⟩ := parser_correct 2 (encode (![context,request])) []
  rw [decode_encode] at hr
  change BitMachineBankCodec.parserRun t
    (parserCfg (some (.scan 0)) none (fun _ => []) (packet context request) [] []) =
    parserCfg none (some true) (![context,request]) [] [] [] at hr
  obtain ⟨u,hu,he⟩ := BitMachineStackEmbedding.outputs (parseStack M) (initialBank M context request)
    .parse (packetControl M) Prod.snd (by intro v; rfl) (some .afterParse)
    (parser 2) (program M) (by intro l; rfl)
    (parserCfg (some (.scan 0)) none (fun _ => []) (packet context request) [] []) t
    (by change (BitMachineBankCodec.parserRun t _).l=none; rw [hr]; rfl)
  change run M u (parseFrame M _ _) = parseFrame M _ (BitMachineBankCodec.parserRun t _) at he
  rw [hr,parse_initial,parse_final] at he
  exact ⟨u,hu.trans ht,he⟩

theorem machine_ne_low (M : BitMachine.Machine) (i : Fin M.stackCount) (k : Fin 32) :
    (slots M).machine i ≠ low M k := by
  intro h
  have hv := congrArg Fin.val h
  have hk := k.isLt
  change 32+i.val=k.val at hv
  omega

theorem invoke_run (M : BitMachine.Machine) (context request answer : List Bool)
    (T : Nat) (hM : M.OutputsWithin request answer T) :
    ∃ t ≤ MachineInvokeFull.uniformBound M request T,
      run M t ⟨some (.invoke (MachineInvokeFull.start (slots M))),liftControl M (localControl M),loaded M context request⟩ =
        ⟨some .afterInvoke,liftControl M (localControl M),invoked M context request answer⟩ := by
  let S := loaded M context request
  have hblank (i : Fin M.stackCount) : S ((slots M).machine i)=[] := by
    simp only [S,loaded,if_neg (machine_ne_low M i 3),if_neg (machine_ne_low M i 0)]
  obtain ⟨t,ht,hr⟩ := MachineInvokeFull.invoke_run_uniform (slots M) S request answer T
    (by rfl) (by rfl) (by rfl) hblank hM
  change ((advance (MachineInvokeFull.program (slots M)))^[t])
    ⟨some (MachineInvokeFull.start (slots M)),localControl M,S⟩ =
    ⟨none,localControl M,Function.update S (slots M).target answer⟩ at hr
  obtain ⟨u,hu,he⟩ := BitMachineInline.outputs .invoke (liftControl M) Prod.fst
    (by intro v; rfl) (some .afterInvoke)
    (MachineInvokeFull.program (slots M)) (program M) (by intro l; rfl)
    (⟨some (MachineInvokeFull.start (slots M)),localControl M,S⟩ :
      TM2.Cfg (fun _ : Stack M => Bool) _ _) t (by rw [hr])
  rw [hr] at he
  exact ⟨u,hu.trans ht,he⟩

theorem after_parse (M : BitMachine.Machine) (context request : List Bool) :
    run M 1 ⟨some .afterParse,packetControl M (some true),loaded M context request⟩ =
      ⟨some (.invoke (MachineInvokeFull.start (slots M))),liftControl M (localControl M),loaded M context request⟩ := rfl

theorem emit_initial (M : BitMachine.Machine) (context request answer : List Bool) :
    emitFrame M (invoked M context request answer)
      (BitMachineBankSerialize.cfg (some (.emit 0)) none (![context,answer]) [] [] []) =
      ⟨some (.emit (.emit 0)),packetControl M none,invoked M context request answer⟩ := by
  unfold emitFrame BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg BitMachineInline.cfg
  congr 1
  apply BitMachineStackEmbedding.bank_eq_self
  intro k; cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

theorem after_invoke (M : BitMachine.Machine) (context request answer : List Bool) :
    run M 1 ⟨some .afterInvoke,liftControl M (localControl M),invoked M context request answer⟩ =
      emitFrame M (invoked M context request answer)
        (BitMachineBankSerialize.cfg (some (.emit 0)) none (![context,answer]) [] [] []) := by
  rw [emit_initial]
  rfl

theorem emit_run (M : BitMachine.Machine) (S : Stack M → List Bool) (w : Bank 2) :
    ∃ (t : Nat) (w' : Bank 2), t ≤ 2*(encode w).length+2 ∧
      run M t (emitFrame M S (BitMachineBankSerialize.cfg (some (.emit 0)) none w [] [] [])) =
        emitFrame M S (BitMachineBankSerialize.cfg none none w' [] [] (encode w)) := by
  obtain ⟨t,w',ht,hr⟩ := BitMachineBankSerialize.serialize w [] []
  have henc : BitMachineBankSerialize.encode (List.ofFn w)=encode w := (encode_eq_list w).symm
  rw [henc,List.append_nil] at hr
  rw [henc] at ht
  obtain ⟨u,hu,he⟩ := BitMachineStackEmbedding.outputs (emitStack M) S .emit (packetControl M) Prod.snd
    (by intro v; rfl) none (BitMachineBankSerialize.program 2) (program M) (by intro l; rfl)
    (BitMachineBankSerialize.cfg (some (.emit 0)) none w [] [] []) t
    (by change (BitMachineBankSerialize.run t _).l=none; rw [hr]; rfl)
  change run M u (emitFrame M S _) = emitFrame M S (BitMachineBankSerialize.run t _) at he
  rw [hr] at he
  exact ⟨u,w',hu.trans ht,he⟩

noncomputable def final (M : BitMachine.Machine) (context request answer : List Bool) (w : Bank 2) : Config M :=
  emitFrame M (invoked M context request answer)
    (BitMachineBankSerialize.cfg none none w [] [] (output context answer))

def clock (M : BitMachine.Machine) (context request answer : List Bool) (T : Nat) : Nat :=
  5*((packet context request).length+1)+MachineInvokeFull.uniformBound M request T+
    2*(output context answer).length+4

theorem raw_run (M : BitMachine.Machine) (context request answer : List Bool)
    (T : Nat) (hM : M.OutputsWithin request answer T) :
    ∃ (t : Nat) (w : Bank 2), t ≤ clock M context request answer T ∧
      run M t (rawInit (low M 4) (.parse (.scan 0) : Label M) (packetControl M none) (packet context request)) =
        final M context request answer w := by
  obtain ⟨a,ha,hA⟩ := parse_run M context request
  obtain ⟨b,hb,hB⟩ := invoke_run M context request answer T hM
  obtain ⟨c,w,hc,hC⟩ := emit_run M (invoked M context request answer) (![context,answer])
  have h1 := (run_add M hA 1).trans (after_parse M context request)
  have h2 := (run_add M h1 b).trans hB
  have h3 := (run_add M h2 1).trans (after_invoke M context request answer)
  refine ⟨a+1+b+1+c,w,?_,(run_add M h3 c).trans hC⟩
  change c ≤ 2*(output context answer).length+2 at hc
  unfold clock
  omega

theorem final_halt (M : BitMachine.Machine) (context request answer : List Bool) (w : Bank 2) :
    (final M context request answer w).l=none := rfl

theorem final_output (M : BitMachine.Machine) (context request answer : List Bool) (w : Bank 2) :
    (final M context request answer w).stk (low M 6)=output context answer := by
  change BitMachineStackEmbedding.bank (emitStack M) (invoked M context request answer)
    (BitMachineBankSerialize.contents w [] [] (output context answer)) (emitStack M (.inr 2))=output context answer
  exact BitMachineStackEmbedding.bank_at _ _ _ _

noncomputable def machine (M : BitMachine.Machine) : BitMachine.Machine :=
  ofFinite (low M 4) (low M 6) (.parse (.scan 0) : Label M) (packetControl M none) (program M)

theorem outputs (M : BitMachine.Machine) (context request answer : List Bool)
    (T : Nat) (hM : M.OutputsWithin request answer T) :
    (machine M).OutputsWithin (packet context request) (output context answer) (clock M context request answer T) := by
  obtain ⟨t,w,ht,hr⟩ := raw_run M context request answer T hM
  apply outputsWithin_of_raw_run (low M 4) (low M 6) (.parse (.scan 0) : Label M)
    (packetControl M none) (program M) _ _ t _ ht
  · change (run M t _).l=none
    rw [hr]; exact final_halt M context request answer w
  · change (run M t _).stk (low M 6)=output context answer
    rw [hr]; exact final_output M context request answer w

#print axioms outputs
end CurrentAdditive.ContextualInvoke
