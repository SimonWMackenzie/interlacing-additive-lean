import CurrentAdditive.MinimumRatioPairAndLess

/-! The local decision controller reads the three one-bit tests, preserves the
old best when the candidate loses or ties, and otherwise physically clears the
old packet and copies the new canonical quotient into bank 9. -/

namespace CurrentAdditive.MinimumRatioBestUpdate

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioCallbackLayout

inductive Label where
  | positive | best | less | clear | copy (l : BitMachineCopy.Label) | finish
  deriving DecidableEq, Fintype

abbrev Control := ((Option Bool × Option Bool × Option Bool) × Option Bool)

def initial : Control := ((none, none, none), none)

noncomputable def copySlots : Fin 3 ↪ Stack where
  toFun i := low (![16,9,21] i)
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [low]

noncomputable def program : Label →
    TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .positive =>
      .pop (low 15) (fun v b => ((b, v.1.2.1, v.1.2.2), v.2))
        (.goto (fun _ => .best))
  | .best =>
      .pop (low 9) (fun v b => ((v.1.1, b, v.1.2.2), v.2))
        (.branch (fun v => v.1.2.1.isSome)
          (.push (low 9) (fun v => v.1.2.1.getD false)
            (.goto (fun _ => .less)))
          (.goto (fun _ => .less)))
  | .less =>
      .pop (low 18) (fun v b => ((v.1.1, v.1.2.1, b), v.2))
        (.branch (fun v => v.1.1.isSome &&
          (!v.1.2.1.isSome || v.1.2.2.isSome))
          (.goto (fun _ => .clear))
          .halt)
  | .clear =>
      .pop (low 9) (fun v b => (v.1,b))
        (.branch (fun v => v.2.isSome)
          (.goto (fun _ => .clear))
          (.load (fun _ => initial) (.goto (fun _ => .copy .scan))))
  | .copy l =>
      BitMachineStackEmbedding.stmt copySlots Label.copy
        (fun b => ((none,none,none), b)) Prod.snd
        (some .finish) (BitMachineCopy.program l)
  | .finish =>
      .push (low 9) (fun _ => true) .halt

end CurrentAdditive.MinimumRatioBestUpdate
