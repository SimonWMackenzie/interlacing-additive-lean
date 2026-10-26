import CurrentAdditive.GaussUnaryDoubleCopy
import CurrentAdditive.GaussPackedParse64
import CurrentAdditive.GaussOneFetchProgram64
import CurrentAdditive.GaussPreparedColumnDecision
import CurrentAdditive.GaussRationalNegateCanonical
import CurrentAdditive.GaussZeroOneCoefficient
import CurrentAdditive.GaussCertificateVectorABI

/-! One fixed finite controller for parsing a Bank3 coefficient request,
copying both unary indices, comparing them, and selecting the matrix getter
or a literal zero/negative-one word. A following physical negate stage yields
the requested coefficient. -/

namespace CurrentAdditive.GaussCoefficientProgram

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

namespace Parse
export CurrentAdditive.GaussPackedParse64 (Stack Label Control program)
end Parse
namespace Copy
export CurrentAdditive.GaussUnaryDoubleCopy
  (Stack Label Control program cfg run run_unary)
end Copy
namespace Compare
export CurrentAdditive.GaussPreparedColumnDecision
  (Bank Label Control program initial local_run)
end Compare
namespace Getter
export CurrentAdditive.GaussOneFetchProgram64
  (Stack Label Control program initial preparationClock canonical_one_fetch)
end Getter

abbrev Stack := Fin 64 ⊕ (Fin 6 ⊕ Fin 1)

def parseSlots : Parse.Stack ↪ Stack where
  toFun := Sum.inl
  inj' := by intro a b h; exact Sum.inl.inj h

def copyJSlot : Copy.Stack → Stack :=
  ![(.inl 15), (.inr (.inl 0)), (.inr (.inl 3)), (.inr (.inr 0))]

def copyFSlot : Copy.Stack → Stack :=
  ![(.inl 16), (.inr (.inl 1)), (.inr (.inl 4)), (.inr (.inr 0))]

def copyJSlots : Copy.Stack ↪ Stack :=
  ⟨copyJSlot, by intro a b h; fin_cases a <;> fin_cases b <;>
    simp_all [copyJSlot]⟩

def copyFSlots : Copy.Stack ↪ Stack :=
  ⟨copyFSlot, by intro a b h; fin_cases a <;> fin_cases b <;>
    simp_all [copyFSlot]⟩

def compareSlots : Fin 6 ↪ Stack where
  toFun := fun i => .inr (.inl i)
  inj' := by intro a b h; exact Sum.inl.inj (Sum.inr.inj h)

def getterSlots : Getter.Stack ↪ Stack := parseSlots

inductive Label where
  | parse (l : Parse.Label)
  | bridgeParse
  | copyJ (l : Copy.Label)
  | copyF (l : Copy.Label)
  | bridgeF
  | compare (l : Compare.Label)
  | decide
  | nonless
  | bridgeGetter
  | writeNegOne
  | writeZero
  | getter (l : Getter.Label)
  deriving Fintype

abbrev Control :=
  (Parse.Control × Copy.Control × Compare.Control × Getter.Control) × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def compareInitial : Compare.Control := ((none, none), (none, none))
def getterInitial : Getter.Control :=
  (Getter.initial (fun _ => [])).var

def parseEmbed (s : Parse.Control) : Control :=
  ((s, none, compareInitial, getterInitial), none)
def copyEmbed (s : Copy.Control) : Control :=
  ((none, s, compareInitial, getterInitial), none)
def compareEmbed (s : Compare.Control) : Control :=
  ((none, none, s, getterInitial), none)
def getterEmbed (s : Getter.Control) : Control :=
  ((none, none, compareInitial, s), none)

def zeroWord : List Bool := CurrentAdditive.GaussZeroOneCoefficient.zeroWord
def negOneWord : List Bool :=
  CurrentAdditive.GaussCertificateVectorABI.coefficientPacket (-1)

def writeWord : List Bool → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | [] => halt
  | b :: bs => push (.inl 38) (fun _ => b) (writeWord bs)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .parse l => BitMachineStackEmbedding.stmt parseSlots Label.parse parseEmbed
      (fun s => s.1.1) (some .bridgeParse) (Parse.program l)
  | .bridgeParse => load (fun _ => copyEmbed none)
      (goto (fun _ => .copyJ .scan))
  | .copyJ l => BitMachineStackEmbedding.stmt copyJSlots Label.copyJ copyEmbed
      (fun s => s.1.2.1) (some (.copyF .scan)) (Copy.program l)
  | .copyF l => BitMachineStackEmbedding.stmt copyFSlots Label.copyF copyEmbed
      (fun s => s.1.2.1) (some .bridgeF)
      (Copy.program l)
  | .bridgeF => load (fun _ => compareEmbed compareInitial)
      (goto (fun _ => .compare
        (EthInapproximability.CurrentPaper.BitMachineRawSequence.leftLabel
          EthInapproximability.CurrentPaper.EntryUnaryCompare.CL.loop)))
  | .compare l => BitMachineStackEmbedding.stmt compareSlots Label.compare
      compareEmbed (fun s => s.1.2.2.1) (some .decide) (Compare.program l)
  | .decide => peek (.inr (.inl 2)) (fun s b => (s.1, b))
      (branch (fun s => s.2 == some true)
        (goto (fun _ => .bridgeGetter))
        (goto (fun _ => .nonless)))
  | .bridgeGetter => load (fun _ => getterEmbed getterInitial)
      (goto (fun _ => .getter
          (EthInapproximability.CurrentPaper.BitMachineRawSequence.leftLabel
            (EthInapproximability.CurrentPaper.BitMachineRawSequence.leftLabel
              (EthInapproximability.CurrentPaper.BitMachineRawSequence.leftLabel
                (.clear 0))))))
  | .nonless => peek (.inr (.inl 5)) (fun s b => (s.1, b))
      (branch (fun s => s.2 == some true)
        (goto (fun _ => .writeNegOne))
        (goto (fun _ => .writeZero)))
  | .writeNegOne => writeWord negOneWord.reverse
  | .writeZero => writeWord zeroWord.reverse
  | .getter l => BitMachineStackEmbedding.stmt getterSlots Label.getter
      getterEmbed (fun s => s.1.2.2.2) none (Getter.program l)

noncomputable def initialStack (word : List Bool) : Stack → List Bool :=
  Sum.elim
    (CurrentAdditive.GaussPackedParse64.frame (fun _ => [])
      (BitMachineBankCodec.parserCfg (K := 3) (some (.scan 0)) none
        (fun _ => []) word [] [])).stk
    (fun _ => [])

noncomputable def initial (word : List Bool) : Config :=
  ⟨some (.parse (.inl (.scan 0))), parseEmbed none, initialStack word⟩

def run (t : Nat) (q : Config) : Config := ((advance program)^[t]) q

theorem run_add (t u : Nat) (q : Config) :
    run (t+u) q = run u (run t q) := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply]

end CurrentAdditive.GaussCoefficientProgram
