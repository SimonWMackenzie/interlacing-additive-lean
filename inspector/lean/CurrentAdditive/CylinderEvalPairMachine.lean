import CurrentAdditive.CylinderEvalPairLoader
import CurrentAdditive.CylinderTuplePairProgram
import CurrentAdditive.CylinderCoordinateAddress
import CurrentAdditive.IndexedV2Clock

/-! One actual descriptor-pair test. The input contains the literal tuple
and binary coordinate/symbol words. The binary coordinate is converted under
the supplied unary q cap before the checked physical tuple getter is called.
-/

namespace CurrentAdditive.CylinderEvalPairMachine

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineBankCodec

set_option maxHeartbeats 1000000

abbrev Stack := Fin 24
abbrev PairControl := CylinderTuplePairProgram.Control
abbrev Control := (Option Bool × ProtocolBoundedUnary.Control) × PairControl

inductive Admin where
  | afterLoad | afterUnary
  deriving DecidableEq,Fintype

abbrev Label := CylinderEvalPairLoader.Label ⊕
  (ProtocolBoundedUnary.Label ⊕ (CylinderTuplePairProgram.Label ⊕ Admin))
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def loaderStack : Fin 12 ↪ Stack := ⟨fun k => ⟨k.val,by omega⟩,by
  intro a b h; apply Fin.ext; simpa only using congrArg (fun k : Stack => k.val) h⟩

def unaryStack : Fin 4 ↪ Stack where
  toFun k := ![7,5,11,10] k
  inj' := by decide

def pairStack : Fin 15 ↪ Stack where
  toFun k := ![12,13,14,15,16,17,18,19,6,20,10,21,8,22,23] k
  inj' := by decide

def pairInit : PairControl :=
  CylinderTuplePairProgram.getterControl (CylinderContextScanStep.copyControl ((),none))

def loaderControl (v : Option Bool) : Control := ((v,(none,false)),pairInit)
def unaryControl (v : ProtocolBoundedUnary.Control) : Control := ((none,v),pairInit)
def pairControl (v : PairControl) : Control := ((none,(none,false)),v)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineStackEmbedding.stmt loaderStack Sum.inl loaderControl
      (fun v => v.1.1) (some (.inr (.inr (.inr .afterLoad))))
      (CylinderEvalPairLoader.program l)
  | .inr (.inl l) => BitMachineStackEmbedding.stmt unaryStack (fun l => .inr (.inl l))
      unaryControl (fun v => v.1.2) (some (.inr (.inr (.inr .afterUnary))))
      (ProtocolBoundedUnary.program l)
  | .inr (.inr (.inl l)) => BitMachineStackEmbedding.stmt pairStack
      (fun l => .inr (.inr (.inl l))) pairControl Prod.snd none
      (CylinderTuplePairProgram.program l)
  | .inr (.inr (.inr .afterLoad)) => .load (fun _ => unaryControl (none,false))
      (.goto (fun _ => .inr (.inl .zeroScan)))
  | .inr (.inr (.inr .afterUnary)) => .pop 10 (fun v _ => v)
      (.load (fun _ => pairControl pairInit)
        (.goto (fun _ => .inr (.inr (.inl (.inl (.inl .scan)))))))

def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

noncomputable def loaderFrame (foreign : Stack → List Bool)
    (c : CylinderEvalPairLoader.Config) : Config :=
  BitMachineStackEmbedding.cfg loaderStack foreign Sum.inl loaderControl
    (some (.inr (.inr (.inr .afterLoad)))) c

noncomputable def unaryFrame (foreign : Stack → List Bool)
    (c : TM2.Cfg (fun _ : Fin 4 => Bool) ProtocolBoundedUnary.Label
      ProtocolBoundedUnary.Control) : Config :=
  BitMachineStackEmbedding.cfg unaryStack foreign (fun l => .inr (.inl l))
    unaryControl (some (.inr (.inr (.inr .afterUnary)))) c

noncomputable def pairFrame (foreign : Stack → List Bool)
    (c : CylinderTuplePairProgram.Config) : Config :=
  BitMachineStackEmbedding.cfg pairStack foreign (fun l => .inr (.inr (.inl l)))
    pairControl none c

theorem pairFrame_halt (S : Stack → List Bool) (c : CylinderTuplePairProgram.Config)
    (hh : c.l=none) : (pairFrame S c).l=none := by
  simp only [pairFrame,BitMachineStackEmbedding.cfg,BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg,hh]

theorem pairFrame_output (S : Stack → List Bool) (c : CylinderTuplePairProgram.Config) :
    (pairFrame S c).stk 20=c.stk 9 := by
  change BitMachineStackEmbedding.bank pairStack S c.stk (pairStack 9)=c.stk 9
  exact BitMachineStackEmbedding.bank_at _ _ _ _

theorem loaderBank_at (foreign : Stack → List Bool) (localBank : Fin 12 → List Bool)
    (k : Stack) :
    BitMachineStackEmbedding.bank loaderStack foreign localBank k=
      if h : k.val<12 then localBank ⟨k.val,h⟩ else foreign k := by
  by_cases h : k.val<12
  · rw [dif_pos h]
    have he : k=loaderStack ⟨k.val,h⟩ := Fin.ext rfl
    calc
      _ = BitMachineStackEmbedding.bank loaderStack foreign localBank
          (loaderStack ⟨k.val,h⟩) := congrArg _ he
      _ = _ := BitMachineStackEmbedding.bank_at _ _ _ _
  · rw [dif_neg h]
    apply BitMachineStackEmbedding.bank_outside
    rintro ⟨a,ha⟩
    have hv : a.val=k.val := congrArg (fun k : Stack => k.val) ha
    have haBound := a.isLt
    omega

noncomputable def loadedBank (q tuple coordinate symbol : List Bool) : Stack → List Bool :=
  BitMachineStackEmbedding.bank loaderStack (fun _ => [])
    (CylinderEvalPairLoader.loaded q tuple coordinate symbol)

theorem loader_initial (q tuple coordinate symbol : List Bool) :
    loaderFrame (fun _ => [])
      ⟨some (.parse .outer (.scan 0)),none,
        CylinderEvalPairLoader.stage .outer q tuple coordinate symbol⟩ =
      rawInit (0 : Stack) (Sum.inl (.parse .outer (.scan 0)) : Label)
        (loaderControl none) (CylinderEvalPairLoader.input q tuple coordinate symbol) := by
  unfold loaderFrame BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg rawInit
  congr 1
  funext k
  rw [loaderBank_at]
  fin_cases k <;> rfl

theorem loader_run (q tuple coordinate symbol : List Bool) :
    ∃ t ≤ 18*((CylinderEvalPairLoader.input q tuple coordinate symbol).length+1),
      run t (rawInit (0 : Stack) (Sum.inl (.parse .outer (.scan 0)) : Label)
        (loaderControl none) (CylinderEvalPairLoader.input q tuple coordinate symbol)) =
      ⟨some (.inr (.inr (.inr .afterLoad))),loaderControl (some true),
        loadedBank q tuple coordinate symbol⟩ := by
  obtain ⟨t,ht,hr⟩ := CylinderEvalPairLoader.loaded_run q tuple coordinate symbol
  have hh : (CylinderEvalPairLoader.run t
      ⟨some (.parse .outer (.scan 0)),none,
        CylinderEvalPairLoader.stage .outer q tuple coordinate symbol⟩).l=none := by rw [hr]
  obtain ⟨u,hu,he⟩ := BitMachineStackEmbedding.outputs loaderStack (fun _ => [])
    Sum.inl loaderControl (fun v => v.1.1) (by intro v; rfl)
    (some (.inr (.inr (.inr .afterLoad)))) CylinderEvalPairLoader.program program
    (by intro l; rfl)
    (⟨some (.parse .outer (.scan 0)),none,
      CylinderEvalPairLoader.stage .outer q tuple coordinate symbol⟩ : CylinderEvalPairLoader.Config)
    t hh
  change run u (loaderFrame (fun _ => []) _) = loaderFrame (fun _ => [])
    (CylinderEvalPairLoader.run t _) at he
  rw [hr,loader_initial] at he
  exact ⟨u,hu.trans ht,he⟩

theorem unary_initial (q tuple coordinate symbol : List Bool) :
    unaryFrame (loadedBank q tuple coordinate symbol)
      (ProtocolBoundedUnary.cfg (some .zeroScan) (none,false) coordinate q [] []) =
      ⟨some (.inr (.inl .zeroScan)),unaryControl (none,false),
        loadedBank q tuple coordinate symbol⟩ := by
  unfold unaryFrame BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg
  congr 1
  apply BitMachineStackEmbedding.bank_eq_self
  intro k
  fin_cases k <;> simp [ProtocolBoundedUnary.cfg,ProtocolBoundedUnary.stackContents,
    unaryStack,loadedBank,loaderBank_at,CylinderEvalPairLoader.loaded]

theorem after_load (q tuple coordinate symbol : List Bool) :
    run 1 ⟨some (.inr (.inr (.inr .afterLoad))),loaderControl (some true),
      loadedBank q tuple coordinate symbol⟩ =
      unaryFrame (loadedBank q tuple coordinate symbol)
        (ProtocolBoundedUnary.cfg (some .zeroScan) (none,false) coordinate q [] []) := by
  rw [unary_initial]
  rfl

theorem unaryBank_at (S : Stack → List Bool) (T : Fin 4 → List Bool) (k : Stack) :
    BitMachineStackEmbedding.bank unaryStack S T k =
      if k=7 then T 0 else if k=5 then T 1 else if k=11 then T 2
      else if k=10 then T 3 else S k := by
  fin_cases k
  all_goals first
    | exact BitMachineStackEmbedding.bank_at unaryStack S T (0 : Fin 4)
    | exact BitMachineStackEmbedding.bank_at unaryStack S T (1 : Fin 4)
    | exact BitMachineStackEmbedding.bank_at unaryStack S T (2 : Fin 4)
    | exact BitMachineStackEmbedding.bank_at unaryStack S T (3 : Fin 4)
    | exact BitMachineStackEmbedding.bank_outside unaryStack S T _ (by decide)

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

theorem pair_initial_eq (tuple : List Bool) (i : ℕ) (symbol : List Bool) :
    CylinderTuplePairProgram.getterFrame (CylinderTuplePairProgram.pairForeign symbol [])
      (CylinderContextScanStep.initial tuple i) =
      CylinderTuplePairProgram.initial tuple i symbol := by
  unfold CylinderTuplePairProgram.getterFrame BitMachineStackEmbedding.cfg
    BitMachineStackEmbedding.stackCfg BitMachineInline.cfg
  congr 1
  apply embeddedBank_eq
  · intro k; fin_cases k <;> rfl
  · intro k hk; fin_cases k
    all_goals first
      | rfl
      | exact (hk ⟨(0 : Fin 12),rfl⟩).elim
      | exact (hk ⟨(1 : Fin 12),rfl⟩).elim
      | exact (hk ⟨(2 : Fin 12),rfl⟩).elim
      | exact (hk ⟨(3 : Fin 12),rfl⟩).elim
      | exact (hk ⟨(4 : Fin 12),rfl⟩).elim
      | exact (hk ⟨(5 : Fin 12),rfl⟩).elim
      | exact (hk ⟨(6 : Fin 12),rfl⟩).elim
      | exact (hk ⟨(7 : Fin 12),rfl⟩).elim
      | exact (hk ⟨(8 : Fin 12),rfl⟩).elim
      | exact (hk ⟨(10 : Fin 12),rfl⟩).elim

noncomputable def afterUnaryBank (q tuple coordinate symbol : List Bool)
    (T : Fin 4 → List Bool) (i : ℕ) : Stack → List Bool :=
  Function.update (BitMachineStackEmbedding.bank unaryStack
    (loadedBank q tuple coordinate symbol) T) 10 (List.replicate i true)

theorem pair_ready (q tuple coordinate symbol : List Bool)
    (T : Fin 4 → List Bool) (i : ℕ) :
    pairFrame (afterUnaryBank q tuple coordinate symbol T i)
      (CylinderTuplePairProgram.initial tuple i symbol) =
      ⟨some (.inr (.inr (.inl (.inl (.inl .scan))))),pairControl pairInit,
        afterUnaryBank q tuple coordinate symbol T i⟩ := by
  unfold pairFrame BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg
  congr 1
  apply BitMachineStackEmbedding.bank_eq_self
  intro k
  fin_cases k <;> simp [CylinderTuplePairProgram.initial,CylinderTuplePairProgram.initialBank,
    CylinderContextScanStep.initialBank,afterUnaryBank,pairStack,unaryBank_at,
    loadedBank,loaderBank_at,CylinderEvalPairLoader.loaded]

theorem unary_to_pair (q tuple coordinate symbol : List Bool) (i : ℕ)
    (c : TM2.Cfg (fun _ : Fin 4 => Bool) ProtocolBoundedUnary.Label ProtocolBoundedUnary.Control)
    (hh : c.l=none) (ho : c.stk 3=true::List.replicate i true) :
    run 1 (unaryFrame (loadedBank q tuple coordinate symbol) c) =
      pairFrame (afterUnaryBank q tuple coordinate symbol c.stk i)
        (CylinderTuplePairProgram.initial tuple i symbol) := by
  rw [pair_ready]
  unfold unaryFrame BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg
  simp only [hh]
  have h10 : BitMachineStackEmbedding.bank unaryStack
      (loadedBank q tuple coordinate symbol) c.stk 10=true::List.replicate i true := by
    change BitMachineStackEmbedding.bank unaryStack _ _ (unaryStack 3)=_
    rw [BitMachineStackEmbedding.bank_at,ho]
  simp only [run,Function.iterate_one,advance,TM2.step,program,TM2.stepAux,h10,
    List.head?_cons,List.tail_cons]
  rfl

theorem run_add {c c' : Config} {n : ℕ} (h : run n c=c') (m : ℕ) :
    run (n+m) c=run m c' := by
  rw [Nat.add_comm,run,Function.iterate_add_apply]
  exact congrArg (run m) h

def tupleWord {q : ℕ} (v : Fin q → ℕ) : List Bool :=
  SourceListEncoding.encode (List.ofFn (fun j : Fin q => (v j).bits))

def input {q : ℕ} (v : Fin q → ℕ) (i : Fin q) (y : ℕ) : List Bool :=
  CylinderEvalPairLoader.input (List.replicate q true) (tupleWord v) i.val.bits y.bits

def pairBound {q : ℕ} (v : Fin q → ℕ) (i : Fin q) (y : ℕ) : ℕ :=
  let xs := List.ofFn (fun j : Fin q => (v j).bits)
  2*i.val+5+(2*(tupleWord v).length+5+
    (4*xs.length.bits.length+6+
      GaussListContext.IndexedFieldProgram.fieldCost (xs.take i.val++[(v i).bits])))+
    1+(min (v i).bits.length y.bits.length+1)+1

def clock {q : ℕ} (v : Fin q → ℕ) (i : Fin q) (y : ℕ) : ℕ :=
  18*((input v i y).length+1)+1+(q+1)*(4*i.val.bits.length+5)+1+pairBound v i y

noncomputable def machine : BitMachine.Machine :=
  ofFinite (0 : Stack) 20 (.inl (.parse .outer (.scan 0)) : Label)
    (loaderControl none) program

theorem outputs {q : ℕ} (v : Fin q → ℕ) (i : Fin q) (y : ℕ) :
    machine.OutputsWithin (input v i y) [decide (v i=y)] (clock v i y) := by
  let qword := List.replicate q true
  let tuple := tupleWord v
  let S := loadedBank qword tuple i.val.bits y.bits
  obtain ⟨a,ha,hA⟩ := loader_run qword tuple i.val.bits y.bits
  have hAfter := (run_add hA 1).trans (after_load qword tuple i.val.bits y.bits)
  obtain ⟨b,c,hb,hB,hhalt,hout⟩ :=
    ProtocolBoundedUnary.bounded_run i.val.bits qword []
  have haddr : c.stk 3=true::List.replicate i.val true := by
    rw [hout]
    simp [ProtocolBoundedUnary.result,qword,EncodedCommunication.bitsValue_bits,
      Nat.min_eq_left i.isLt.le,i.isLt.le]
  obtain ⟨u,hu,hU⟩ := BitMachineStackEmbedding.outputs unaryStack S
    (fun l => .inr (.inl l)) unaryControl (fun v => v.1.2) (by intro v; rfl)
    (some (.inr (.inr (.inr .afterUnary)))) ProtocolBoundedUnary.program program
    (by intro l; rfl)
    (ProtocolBoundedUnary.cfg (some .zeroScan) (none,false) i.val.bits qword [] [])
    b (by change (ProtocolBoundedUnary.run b _).l=none; rw [hB]; exact hhalt)
  change run u (unaryFrame S _) = unaryFrame S (ProtocolBoundedUnary.run b _) at hU
  rw [hB] at hU
  have hAB := (run_add hAfter u).trans hU
  have hReady := (run_add hAB 1).trans
    (unary_to_pair qword tuple i.val.bits y.bits i.val c hhalt haddr)
  let T := afterUnaryBank qword tuple i.val.bits y.bits c.stk i.val
  obtain ⟨d,hd,hDhalt,hDout⟩ :=
    CylinderTuplePairProgram.actual_retained_tuple_pair (v,(0 : ℚ)) i y []
  dsimp only at hd hDhalt hDout
  rw [pair_initial_eq] at hDhalt hDout
  have hd' : d≤pairBound v i y := hd
  obtain ⟨w,hw,hW⟩ := BitMachineStackEmbedding.outputs pairStack T
    (fun l => .inr (.inr (.inl l))) pairControl Prod.snd (by intro v; rfl) none
    CylinderTuplePairProgram.program program (by intro l; rfl)
    (CylinderTuplePairProgram.initial tuple i.val y.bits) d hDhalt
  change run w (pairFrame T _) = pairFrame T (CylinderTuplePairProgram.run d _) at hW
  have htotal := (run_add hReady w).trans hW
  have hbit : ((v i).bits=y.bits) ↔ v i=y := by
    constructor
    · intro h
      have h' := congrArg EncodedCommunication.bitsValue h
      simpa using h'
    · exact congrArg Nat.bits
  have hDout' : (CylinderTuplePairProgram.run d
      (CylinderTuplePairProgram.initial tuple i.val y.bits)).stk 9=[decide (v i=y)] := by
    simpa [CylinderPairEvaluationBridge.pair_value_eq,hbit] using hDout
  have heinput : CylinderEvalPairLoader.input qword tuple i.val.bits y.bits=input v i y := rfl
  rw [heinput] at htotal ha
  apply outputsWithin_of_raw_run (0 : Stack) 20 (.inl (.parse .outer (.scan 0)) : Label)
    (loaderControl none) program (input v i y) [decide (v i=y)]
    (a+1+u+1+w) (clock v i y)
  · dsimp [clock]
    have hb' : b≤(q+1)*(4*i.val.bits.length+5) := by simpa only [qword,List.length_replicate] using hb
    omega
  · change (run (a+1+u+1+w) _).l=none
    rw [htotal]
    exact pairFrame_halt T _ hDhalt
  · change (run (a+1+u+1+w) _).stk 20=[decide (v i=y)]
    rw [htotal]
    exact (pairFrame_output T _).trans hDout'

end CurrentAdditive.CylinderEvalPairMachine

#print axioms CurrentAdditive.CylinderEvalPairMachine.loader_run
#print axioms CurrentAdditive.CylinderEvalPairMachine.unary_initial
#print axioms CurrentAdditive.CylinderEvalPairMachine.unary_to_pair
#print axioms CurrentAdditive.CylinderEvalPairMachine.outputs
