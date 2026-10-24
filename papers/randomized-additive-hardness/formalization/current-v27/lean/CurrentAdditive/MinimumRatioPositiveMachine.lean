import CurrentAdditive.CodeDPairProductTargetV2
import CurrentAdditive.CodeDZeroWordV2
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding
import Mathlib.Tactic

/-! Physical positivity test for the coefficient in a nested RawRat pair.
The numerator-zero test is the reviewed Code D controller. -/

namespace CurrentAdditive.MinimumRatioPositiveMachine

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open BitMachineEncoding
open CurrentAdditive.CodeDCodec

abbrev Stack := Fin 12

inductive Label where
  | outer (l : BitMachineBankCodec.ParserLabel 2)
  | inner (l : BitMachineBankCodec.ParserLabel 3)
  | zero (l : CodeDZeroWordV2.Label)
  | afterOuter | afterInner | afterSign | afterZero
  deriving DecidableEq, Fintype

structure Control where
  outer : Option Bool
  inner : Option Bool
  zero : CodeDZeroWordV2.Control
  peeked : Option Bool
  deriving DecidableEq, Fintype

def initial : Control := ⟨none,none,CodeDZeroWordV2.initial,none⟩

def outerSlot : BitMachineBankCodec.Stack 2 ↪ Stack where
  toFun
    | .inl i => (![0,1] : Fin 2 → Stack) i
    | .inr j => (![2,3,4] : Fin 3 → Stack) j
  inj' := by
    intro a b h
    cases a with
    | inl a =>
        cases b with
        | inl b => fin_cases a <;> fin_cases b <;> simp_all
        | inr b => fin_cases a <;> fin_cases b <;> simp_all
    | inr a =>
        cases b with
        | inl b => fin_cases a <;> fin_cases b <;> simp_all
        | inr b => fin_cases a <;> fin_cases b <;> simp_all

def innerSlot : BitMachineBankCodec.Stack 3 ↪ Stack where
  toFun
    | .inl i => (![5,6,7] : Fin 3 → Stack) i
    | .inr j => (![1,8,9] : Fin 3 → Stack) j
  inj' := by
    intro a b h
    cases a with
    | inl a =>
        cases b with
        | inl b => fin_cases a <;> fin_cases b <;> simp_all
        | inr b => fin_cases a <;> fin_cases b <;> simp_all
    | inr a =>
        cases b with
        | inl b => fin_cases a <;> fin_cases b <;> simp_all
        | inr b => fin_cases a <;> fin_cases b <;> simp_all

def zeroSlot : Fin 2 ↪ Stack where
  toFun := ![6,10]
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .outer l => BitMachineStackEmbedding.stmt outerSlot Label.outer
      (fun b => {initial with outer := b}) Control.outer (some .afterOuter)
      (BitMachineBankCodec.parser 2 l)
  | .inner l => BitMachineStackEmbedding.stmt innerSlot Label.inner
      (fun b => {initial with outer := some true, inner := b})
      Control.inner (some .afterInner)
      (BitMachineBankCodec.parser 3 l)
  | .zero l => BitMachineStackEmbedding.stmt zeroSlot Label.zero
      (fun b => {initial with outer := some true, inner := some true, zero := b})
      Control.zero (some .afterZero)
      (CodeDZeroWordV2.program l)
  | .afterOuter => branch (fun v => v.outer == some true)
      (goto (fun _ => .inner (.scan 0))) halt
  | .afterInner => branch (fun v => v.inner == some true)
      (peek 5 (fun v b => {v with peeked := b})
        (goto (fun _ => .afterSign))) halt
  | .afterSign => branch (fun v => v.peeked.isNone)
      (goto (fun _ => .zero .scan)) halt
  | .afterZero => peek 10 (fun v b => {v with peeked := b})
      (branch (fun v => v.peeked == some false)
        (push 11 (fun _ => true) halt) halt)

noncomputable def machine : BitMachine.Machine :=
  ofFinite (2 : Stack) 11 (.outer (.scan 0)) initial program

def result (input : List Bool) : List Bool :=
  match BitMachineBankCodec.decode 2 input with
  | none => []
  | some B =>
      match BitMachineBankCodec.decode 3 (B 1) with
      | none => []
      | some C => if C 0 = [] && (C 1).any id then [true] else []

end CurrentAdditive.MinimumRatioPositiveMachine
