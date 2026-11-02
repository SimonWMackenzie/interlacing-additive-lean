import EthInapproximability.CurrentPaper.QProductJoined
import EthInapproximability.CurrentPaper.QPower
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-! The checked product is copied into the checked logarithm controller,
then its exponent feeds the unary-power controller at writer cell 56. -/

namespace EthInapproximability.CurrentPaper.QSuffixJoin

open Turing BitMachineEncoding
noncomputable section

namespace Raw
abbrev program := @BitMachineRawSequence.program
abbrev runs := @BitMachineRawSequence.runs
abbrev leftLabel := @BitMachineRawSequence.leftLabel
end Raw

def PC := Raw.program QLog.copyProgram QLog.logProgram
  (.inl BitMachineCopy.Label.scan)
  (none : Option Bool) (ETHParameterScaleMachineLogCopy.copyControl none)
def program := Raw.program PC QPower.program (.inr false)
  ((none,ETHParameterScaleMachineLogCopy.copyControl none) :
    Option Bool × ETHParameterScaleMachineLogCopy.Control)
  (((false,false),none) : MatrixUnaryPower.Control)

def initial :=
  (((none,ETHParameterScaleMachineLogCopy.copyControl none),
    ((false,false),none)) :
    (Option Bool × ETHParameterScaleMachineLogCopy.Control) ×
      MatrixUnaryPower.Control)

def cost (n : ℕ) : ℕ :=
  (2*n+2) +
  (2*n+2 + (UnaryBinaryEncoding.coefficient+6)*(n+1)^2) +
  (4*2^Nat.clog 2 n + 5*Nat.clog 2 n + 7) + 2

theorem run (S : QProduct.Stack → List Bool) (n : ℕ)
    (hn : S (QProduct.temp 5) = List.replicate n true)
    (hlog : ∀ k : QLog.Local, S (QLog.logSlots k) = [])
    (h6 : S (QProduct.temp 6) = [])
    (h7 : S (QProduct.temp 7) = [])
    (h8 : S (QProduct.temp 8) = [])
    (hq : S QProduct.q = []) :
    ∃ t ≤ cost n,
      ∃ F : QProduct.Stack → List Bool,
        ((advance program)^[t])
          (⟨some (Raw.leftLabel
              (Raw.leftLabel BitMachineCopy.Label.scan)),initial,S⟩ :
            TM2.Cfg (fun _ : QProduct.Stack => Bool) _ _) =
          ⟨none,initial,F⟩ ∧
        F QProduct.q = List.replicate (2^Nat.clog 2 n) true ∧
        (∀ j : GraphCountBridge.Stack,
          j ≠ (.inr (56 : Fin 64)) → F (.inl j) = S (.inl j)) := by
  have hs : S QLog.source = [] := hlog (.inl 0)
  have hc := QLog.copy_run S n hn hs h6
  obtain ⟨tl,htl,vl,L,hl,hanswer,hframe,htemp⟩ := QLog.log_run S n hlog
  obtain ⟨tc,htc,hcl⟩ := Raw.runs QLog.copyProgram QLog.logProgram
    BitMachineCopy.Label.scan (.inl BitMachineCopy.Label.scan)
    (none : Option Bool) none
    (ETHParameterScaleMachineLogCopy.copyControl none) vl
    S (QLog.copied S n) L (2*n+2) tl hc hl
  have hqL : L QProduct.q = [] := by
    simpa [QProduct.q] using (hframe (.inr (56 : Fin 64))).trans hq
  have h7L : L (QProduct.temp 7) = [] := (htemp 7).trans h7
  have h8L : L (QProduct.temp 8) = [] := (htemp 8).trans h8
  obtain ⟨tp,htp,hpow⟩ := QPower.power_run L n hanswer hqL h7L h8L
  obtain ⟨t,ht,hr⟩ := Raw.runs PC QPower.program
    (Raw.leftLabel BitMachineCopy.Label.scan) (.inr false)
    (none,ETHParameterScaleMachineLogCopy.copyControl none)
    (none,vl)
    (((false,false),none) : MatrixUnaryPower.Control)
    (((false,false),none) : MatrixUnaryPower.Control)
    S L (Function.update L QProduct.q
      (List.replicate (2^Nat.clog 2 n) true))
    tc tp (by simpa only [PC] using hcl) hpow
  refine ⟨t,?_,_,by simpa only [program,initial] using hr,?_,?_⟩
  · dsimp [cost]; omega
  · simp
  · intro j hj
    have hne : (.inl j : QProduct.Stack) ≠ QProduct.q := by
      intro he; exact hj (Sum.inl_injective he)
    simp only [Function.update_of_ne hne]
    exact hframe j

#print axioms run

end
end EthInapproximability.CurrentPaper.QSuffixJoin
