import CurrentAdditive.RawRatPacketWrapper
import Mathlib.Tactic

set_option maxRecDepth 4096

namespace CurrentAdditive.RawRatPacketValidate

open EthInapproximability.CurrentPaper
open Turing Turing.TM2.Stmt BitMachineEncoding
open CurrentAdditive.RawRatPacketWrapper

variable {L V : Type*}
  (P : L → TM2.Stmt (fun _ : Fin 13 => Bool) L V)
  (start : L) (initial : V)

theorem sign_nil (S : Bank) (v : Control V) (h : S 0 = []) :
    advance (program P start initial)
      (cfg (some (.inr (.inr (.inr .signFirst)))) v S [] [] []) =
    cfg (some (.inr (.inl start))) (initial,none) S [] [] [] := by
  simp [advance, program, TM2.step, TM2.stepAux, cfg, contents, h]

theorem sign_true_first (S : Bank) (v : Control V) (h : S 0 = [true]) :
    advance (program P start initial)
      (cfg (some (.inr (.inr (.inr .signFirst)))) v S [] [] []) =
    cfg (some (.inr (.inr (.inr .signTail)))) (v.1,some true) S [] [] [] := by
  simp [advance, program, TM2.step, TM2.stepAux, cfg, contents, h]

theorem sign_true_head (S : Bank) (v : Control V) (w : List Bool)
    (h : S 0 = true :: w) :
    advance (program P start initial)
      (cfg (some (.inr (.inr (.inr .signFirst)))) v S [] [] []) =
    cfg (some (.inr (.inr (.inr .signTail)))) (v.1,some true) S [] [] [] := by
  simp [advance, program, TM2.step, TM2.stepAux, cfg, contents, h]

theorem sign_false_reject (S : Bank) (v : Control V) (w : List Bool)
    (h : S 0 = false :: w) :
    (advance (program P start initial)
      (cfg (some (.inr (.inr (.inr .signFirst)))) v S [] [] [])).l = none ∧
    (advance (program P start initial)
      (cfg (some (.inr (.inr (.inr .signFirst)))) v S [] [] [])).stk (.inr 2) = [] := by
  simp [advance, program, TM2.step, TM2.stepAux, cfg, contents, h]

theorem sign_long_reject (S : Bank) (v : Control V) (b : Bool) (w : List Bool)
    (h : S 0 = true :: b :: w) :
    (advance (program P start initial)
      (cfg (some (.inr (.inr (.inr .signTail)))) v S [] [] [])).l = none ∧
    (advance (program P start initial)
      (cfg (some (.inr (.inr (.inr .signTail)))) v S [] [] [])).stk (.inr 2) = [] := by
  simp only [advance, program, TM2.step, TM2.stepAux, cfg, contents,
    Sum.elim_inl, h, List.tail_cons, Function.update_self,
    List.head?_cons, Option.isNone_some, cond_false,
    Option.getD_some]
  simp [Function.update]

theorem sign_true_tail (S : Bank) (v : Control V) (h : S 0 = [true]) :
    advance (program P start initial)
      (cfg (some (.inr (.inr (.inr .signTail)))) v S [] [] []) =
    cfg (some (.inr (.inl start))) (initial,none) S [] [] [] := by
  simp only [advance, program, TM2.step, TM2.stepAux, cfg, contents,
    Sum.elim_inl, h, List.head?_cons, List.tail_cons,
    Function.update_self, List.head?_nil, Option.isNone_none,
    Option.isSome_some, Option.getD_some, cond_true]
  congr 1
  change Function.update
      (Function.update (contents S [] [] []) (.inl 0) [])
      (.inl 0) [true] = contents S [] [] []
  rw [Function.update_idem]
  apply Function.update_eq_self_iff.mpr
  simpa [contents] using h.symm

theorem sign_valid (r : CurrentAdditive.CodeDCodec.RawRat) :
    ∃ t ≤ 2,
      run P start initial t
        (cfg (some (.inr (.inr (.inr .signFirst))))
          (initial,some true)
          (inputBank (CurrentAdditive.CodeDCodec.rawRatBank r)) [] [] []) =
      cfg (some (.inr (.inl start))) (initial,none)
        (inputBank (CurrentAdditive.CodeDCodec.rawRatBank r)) [] [] [] := by
  let S := inputBank (CurrentAdditive.CodeDCodec.rawRatBank r)
  cases hs : r.negative with
  | false =>
      have hS : S 0 = [] := by simp [S, inputBank, CurrentAdditive.CodeDCodec.rawRatBank, hs]
      refine ⟨1, by omega, ?_⟩
      simpa only [run, Function.iterate_one] using
        sign_nil P start initial S (initial,some true) hS
  | true =>
      have hS : S 0 = [true] := by
        simp [S, inputBank, CurrentAdditive.CodeDCodec.rawRatBank, hs]
      refine ⟨2, by omega, ?_⟩
      rw [show 2 = 1+1 from rfl, run_add]
      have hfirst : run P start initial 1
          (cfg (some (.inr (.inr (.inr .signFirst)))) (initial,some true) S [] [] []) =
          cfg (some (.inr (.inr (.inr .signTail)))) (initial,some true) S [] [] [] := by
        simpa only [run, Function.iterate_one] using
          sign_true_first P start initial S (initial,some true) hS
      rw [hfirst]
      simpa only [run, Function.iterate_one] using
        sign_true_tail P start initial S (initial,some true) hS

theorem framing_reject (input : List Bool)
    (hd : BitMachineBankCodec.decode 3 input = none) :
    ∃ t ≤ 7*(input.length+1)+1,
      let c := run P start initial t
        (cfg (some (.inl (.scan 0))) (initial,none)
          (fun _ => []) input [] [])
      c.l = none ∧ c.stk (.inr 2) = [] := by
  obtain ⟨t,ht,hp⟩ := BitMachineBankCodec.parser_correct 3 input []
  rw [hd] at hp
  change (BitMachineBankCodec.parserRun t _).l = none ∧
    (BitMachineBankCodec.parserRun t _).var = some false ∧
    (BitMachineBankCodec.parserRun t _).stk (.inr 2) = [] at hp
  let c := BitMachineBankCodec.parserRun t
    (BitMachineBankCodec.parserCfg (K := 3) (some (.scan 0)) none
      (fun _ => []) input [] [])
  change c.l = none ∧ c.var = some false ∧ c.stk (.inr 2) = [] at hp
  obtain ⟨u,hu,hr⟩ := BitMachineStackEmbedding.outputs parseSlot
    (fun _ : Stack => []) Sum.inl (fun b => (initial,b)) Prod.snd
    (fun _ => rfl) (some (.inr (.inr (.inr .parsed))))
    (BitMachineBankCodec.parser 3) (program P start initial) (fun _ => rfl)
    (BitMachineBankCodec.parserCfg (K := 3) (some (.scan 0)) none
      (fun _ => []) input [] []) t hp.1
  refine ⟨u+1, by omega, ?_⟩
  dsimp only
  change run P start initial u _ = _ at hr
  rw [RawRatPacketWrapper.parse_start (L := L) initial input] at hr
  rw [run_add, hr]
  have hf : advance (program P start initial)
      (BitMachineStackEmbedding.cfg parseSlot (fun _ : Stack => []) Sum.inl
        (fun b => (initial,b)) (some (.inr (.inr (.inr .parsed)))) c) =
      (⟨none, (initial,some false),
        BitMachineStackEmbedding.bank parseSlot (fun _ : Stack => []) c.stk⟩ :
        TM2.Cfg (fun _ : Stack => Bool) (Label L) (Control V)) := by
    simp only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg, hp.1, hp.2.1, advance, TM2.step,
      program, TM2.stepAux, Option.getD_some, cond_false]
  simp only [run, Function.iterate_one]
  have hk : parseSlot (.inr (2 : Fin 3)) = (.inr 2 : Stack) := rfl
  have hout : (advance (program P start initial)
      (BitMachineStackEmbedding.cfg parseSlot (fun _ : Stack => []) Sum.inl
        (fun b => (initial,b)) (some (.inr (.inr (.inr .parsed)))) c)).stk
      (.inr 2) = [] := by
    rw [hf]
    change BitMachineStackEmbedding.bank parseSlot (fun _ : Stack => []) c.stk
      (.inr 2) = []
    rw [← hk, BitMachineStackEmbedding.bank_at]
    exact hp.2.2
  have hlabel : (advance (program P start initial)
      (BitMachineStackEmbedding.cfg parseSlot (fun _ : Stack => []) Sum.inl
        (fun b => (initial,b)) (some (.inr (.inr (.inr .parsed)))) c)).l = none := by
    rw [hf]
  exact ⟨by simpa only [c, BitMachineBankCodec.parserRun] using hlabel,
    by simpa only [c, BitMachineBankCodec.parserRun] using hout⟩

end CurrentAdditive.RawRatPacketValidate
