import CurrentAdditive.V22EdgeCountMachine
import CurrentAdditive.V22RepeatArithmetic
import CurrentAdditive.V22ParameterDivideFrame
import CurrentAdditive.GenericParameterPair
import CurrentAdditive.V22ExpressionClock

namespace V22PublicRepeat
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
open Turing EthInapproximability.CurrentPaper BitMachineEncoding BitMachineStackEmbedding
open V22UnaryExpression

def q0Expression : Expr := .unary .pow2 (.unary .clog
  (.binary .mul (.binary .mul (.const 4) .vertex) .iteration))
def q0Machine := q0Expression.machine
def q0Clock (s m : ℕ) := q0Expression.clock s m
theorem q0_outputs (s m : ℕ) : q0Machine.OutputsWithin
    (MatrixUnaryArithmetic.encodeInput s m) (List.replicate (V22RepeatArithmetic.q0 s m) true)
      (q0Clock s m) := q0Expression.outputs s m

abbrev EdgeWork := Fin V22EdgeCountMachine.machine.stackCount ⊕ Fin 3
abbrev PowWork := Fin q0Machine.stackCount ⊕ Fin 3
abbrev Work := EdgeWork ⊕ (Fin 6 ⊕ (PowWork ⊕ Fin 9))
abbrev Base (Raw : Type*) := Raw ⊕ Fin 4
abbrev Stack (Raw : Type*) := Raw ⊕ (Fin 4 ⊕ Work)
variable {Raw : Type*} [DecidableEq Raw]
local instance : DecidableEq (Stack Raw) := Classical.decEq _

def basePort : Base Raw ↪ Stack Raw where
  toFun | .inl j => .inl j | .inr j => .inr (.inl j)
  inj' := by intro a b h; cases a <;> cases b <;> simp_all
def liftWork {W : Type*} (e : W ↪ Work) : (Base Raw ⊕ W) ↪ Stack Raw where
  toFun | .inl b => basePort b | .inr w => .inr (.inr (e w))
  inj' := by
    intro a b h
    cases a with
    | inl a => cases b with
      | inl b => exact congrArg Sum.inl (basePort.injective h)
      | inr b => cases a <;> cases h
    | inr a => cases b with
      | inl b => cases b <;> cases h
      | inr b => exact congrArg Sum.inr (e.injective (Sum.inr.inj (Sum.inr.inj h)))
def edgeWork : EdgeWork ↪ Work := Function.Embedding.inl
def pairWork : Fin 6 ↪ Work := ⟨fun j => .inr (.inl j),by intro a b h; simpa using h⟩
def powWork : PowWork ↪ Work := ⟨fun j => .inr (.inr (.inl j)),by intro a b h; simpa using h⟩
def divWork : Fin 9 ↪ Work := ⟨fun j => .inr (.inr (.inr j)),by intro a b h; simpa using h⟩
def edgeSlots : CurrentAdditive.GenericParameterBranch.Stack V22EdgeCountMachine.machine (Base Raw) ↪ Stack Raw := liftWork edgeWork
def pairSlots : CurrentAdditive.GenericParameterPair.Stack (Base Raw) ↪ Stack Raw := liftWork pairWork
def powSlots : CurrentAdditive.GenericParameterBranch.Stack q0Machine (Base Raw) ↪ Stack Raw := liftWork powWork
def divSlots : V22ParameterDivide.Stack (Base Raw) ↪ Stack Raw := liftWork divWork
def edgePort : Base Raw := .inr 0
def pairPort : Base Raw := .inr 1
def q0Port : Base Raw := .inr 2
def repetitionPort : Base Raw := .inr 3
def initial (S : Raw → List Bool) : Stack Raw → List Bool := Sum.elim S (fun _ => [])
def projected (S : Stack Raw → List Bool) : Base Raw → List Bool := fun b => S (basePort b)

def afterEdge (S : Raw → List Bool) (graphPort : Raw) (g : EncodedGraph.Graph) : Stack Raw → List Bool :=
  bank edgeSlots (initial S)
    (CurrentAdditive.GenericParameterBranch.terminal V22EdgeCountMachine.machine (projected (initial S)) edgePort
      (EncodedGraph.encode g) (List.replicate g.edges.length true) (100*((EncodedGraph.encode g).length+1)^3))
def afterPair (S : Raw → List Bool) (graphPort : Raw) (g : EncodedGraph.Graph) (s : ℕ) : Stack Raw → List Bool :=
  bank pairSlots (afterEdge S graphPort g)
    (CurrentAdditive.GenericParameterPair.terminal (projected (afterEdge S graphPort g)) pairPort s g.edges.length)
def afterQ0 (S : Raw → List Bool) (graphPort : Raw) (g : EncodedGraph.Graph) (s : ℕ) : Stack Raw → List Bool :=
  bank powSlots (afterPair S graphPort g s)
    (CurrentAdditive.GenericParameterBranch.terminal q0Machine (projected (afterPair S graphPort g s)) q0Port
      (MatrixUnaryArithmetic.encodeInput s g.edges.length)
      (List.replicate (V22RepeatArithmetic.q0 s g.edges.length) true) (q0Clock s g.edges.length))
def final (S : Raw → List Bool) (graphPort : Raw) (g : EncodedGraph.Graph) (s q₂ : ℕ) : Stack Raw → List Bool :=
  bank divSlots (afterQ0 S graphPort g s)
    (V22ParameterDivide.terminal (projected (afterQ0 S graphPort g s)) repetitionPort
      q₂ (V22RepeatArithmetic.q0 s g.edges.length))

theorem lift_base {W : Type*} (e : W ↪ Work) (b : Base Raw) : liftWork e (.inl b)=basePort b := rfl
theorem bank_other_work {W : Type*} (e : W ↪ Work) (S : Stack Raw → List Bool)
    (T : Base Raw ⊕ W → List Bool) (w : Work) (hw : ¬∃j,e j=w) :
    bank (liftWork e) S T (.inr (.inr w))=S (.inr (.inr w)) := by
  classical
  apply bank_outside
  rintro ⟨j,hj⟩
  cases j with
  | inl j => cases j <;> cases hj
  | inr j => exact hw ⟨j,Sum.inr.inj (Sum.inr.inj hj)⟩

theorem branch_base (M : BitMachine.Machine)
    (e : (Fin M.stackCount ⊕ Fin 3) ↪ Work) (S : Stack Raw → List Bool)
    (target b : Base Raw) (bits result : List Bool) (T : ℕ) :
    bank (liftWork e) S (CurrentAdditive.GenericParameterBranch.terminal M (projected S) target bits result T)
      (basePort b)=if b=target then result else S (basePort b) := by
  change bank (liftWork e) S _ ((liftWork e) (.inl b))=_
  rw [bank_at]
  by_cases h : b=target
  · subst b; simp only [↓reduceIte,CurrentAdditive.GenericParameterBranch.terminal_target]
  · rw [if_neg h,CurrentAdditive.GenericParameterBranch.terminal_base_other M _ target bits result T b h]
    rfl

theorem edge_base (S : Raw → List Bool) (graphPort : Raw) (g : EncodedGraph.Graph) (b : Base Raw) :
    afterEdge S graphPort g (basePort b)=
      if b=edgePort then List.replicate g.edges.length true else initial S (basePort b) :=
  branch_base V22EdgeCountMachine.machine edgeWork (initial S) edgePort b _ _ _

theorem pair_base (S : Raw → List Bool) (graphPort : Raw) (g : EncodedGraph.Graph) (s : ℕ) (b : Base Raw) :
    afterPair S graphPort g s (basePort b)=
      if b=pairPort then MatrixUnaryArithmetic.encodeInput s g.edges.length else afterEdge S graphPort g (basePort b) := by
  change bank pairSlots _ _ (pairSlots (.inl b))=_
  rw [bank_at]
  by_cases h : b=pairPort
  · subst b; simp only [↓reduceIte,CurrentAdditive.GenericParameterPair.terminal_target]
  · rw [if_neg h,CurrentAdditive.GenericParameterPair.terminal_base_other _ pairPort b _ _ h]
    rfl

theorem q0_base (S : Raw → List Bool) (graphPort : Raw) (g : EncodedGraph.Graph) (s : ℕ) (b : Base Raw) :
    afterQ0 S graphPort g s (basePort b)=
      if b=q0Port then List.replicate (V22RepeatArithmetic.q0 s g.edges.length) true
      else afterPair S graphPort g s (basePort b) :=
  branch_base q0Machine powWork _ q0Port b _ _ _

theorem final_base (S : Raw → List Bool) (graphPort : Raw) (g : EncodedGraph.Graph) (s q₂ : ℕ) (b : Base Raw) :
    final S graphPort g s q₂ (basePort b)=
      if b=repetitionPort then List.replicate (V22RepeatArithmetic.repetitions q₂ s g.edges.length) true
      else afterQ0 S graphPort g s (basePort b) := by
  change bank divSlots _ _ (divSlots (.inl b))=_
  rw [bank_at]
  by_cases h : b=repetitionPort
  · subst b; simp only [↓reduceIte,V22ParameterDivide.terminal_target,V22RepeatArithmetic.repetitions]
  · rw [if_neg h,V22ParameterDivide.terminal_base_other _ repetitionPort b h]
    rfl

theorem raw_preserved (S : Raw → List Bool) (graphPort : Raw) (g : EncodedGraph.Graph) (s q₂ : ℕ) (j : Raw) :
    final S graphPort g s q₂ (.inl j)=S j := by
  change final S graphPort g s q₂ (basePort (.inl j))=_
  rw [final_base,q0_base,pair_base,edge_base]
  rfl

theorem repetition_exact (S : Raw → List Bool) (graphPort : Raw) (g : EncodedGraph.Graph) (s q₂ : ℕ) :
    final S graphPort g s q₂ (.inr (.inl 3))=
      List.replicate (V22RepeatArithmetic.repetitions q₂ s g.edges.length) true := by
  exact (final_base S graphPort g s q₂ repetitionPort).trans (if_pos rfl)
theorem edge_exact (S : Raw → List Bool) (graphPort : Raw) (g : EncodedGraph.Graph) (s q₂ : ℕ) :
    final S graphPort g s q₂ (.inr (.inl 0))=List.replicate g.edges.length true := by
  change final S graphPort g s q₂ (basePort edgePort)=_
  rw [final_base,q0_base,pair_base,edge_base]
  rfl

end
end V22PublicRepeat
