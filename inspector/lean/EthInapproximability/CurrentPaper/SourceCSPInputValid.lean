import EthInapproximability.CurrentPaper.SourceCSPHeaderValidFlag
import EthInapproximability.CurrentPaper.SourceCSPInputFrame

/-!
# Raw-input length and all-input fixed-header flag in one physical bank

The source-preserving input-length counter runs first. The arbitrary-input
header validator then runs on exactly that preserved source, while the unary
input-length cap and unused guard work cells stay on foreign stacks.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPInputValid

open Turing BitMachineEncoding BitMachineStackEmbedding

abbrev Stack := SourceCSPInputFrame.Stack
abbrev HeaderLabel (a q : Nat) := BitMachineRawSequence.Label
  (SourceCSPHeaderValidFlag.ParseLabel a q) Unit
abbrev HeaderControl := SourceCSPHeaderValidFlag.ParseControl ×
  SourceCSPHeaderValidFlag.Control

def headerProgram (a q : Nat) (l : HeaderLabel a q) :
    TM2.Stmt (fun _ : Stack => Bool) (HeaderLabel a q) HeaderControl :=
  stmt SourceCSPInputFrame.headerEmbedding id id id none
    (SourceCSPHeaderValidFlag.program a q l)

theorem header_framed (a q : Nat) (input : List Bool) :
    ∃ t v S wa wq,
      t ≤ 4 * (2 * input.length + 4) + 3 +
        (a.bits.length + 1) + (q.bits.length + 1) + 4 ∧
      ((advance (headerProgram a q))^[t])
        (⟨some (.inl (.inl (.inl (.start 0)))),
          ((((none, none), none), none), (none, none, none)),
          SourceCSPInputFrame.afterLength input⟩ :
          TM2.Cfg (fun _ : Stack => Bool) (HeaderLabel a q) HeaderControl) =
        ⟨none, v, S⟩ ∧
      S (.inl SourceCSPHeaderValidFlag.flagSlot) =
        [SourceCSPHeaderValidFlag.parserGood input &&
          decide (wq = q.bits) && decide (wa = a.bits)] ∧
      S (.inr 2) = List.replicate input.length true ∧
      (∀ k : Fin 7, 3 ≤ k.val → S (.inr k) = []) := by
  obtain ⟨th, Sh, vh, wa, wq, hth, hrh, hflag⟩ :=
    SourceCSPHeaderValidFlag.all_input a q input
  let before := SourceCSPInputFrame.afterLength input
  let localCfg : TM2.Cfg (fun _ : SourceCSPHeaderCheck.Stack => Bool)
      (HeaderLabel a q) HeaderControl :=
    ⟨some (.inl (.inl (.inl (.start 0)))),
      ((((none, none), none), none), (none, none, none)),
      SourceCSPHeaderCheck.parserInitial input⟩
  have hhalt : (((advance (SourceCSPHeaderValidFlag.program a q))^[th])
      localCfg).l = none := by
    rw [show ((advance (SourceCSPHeaderValidFlag.program a q))^[th])
      localCfg = ⟨none, ((((none, none), none), none), vh), Sh⟩ from by
      simpa only [localCfg] using hrh]
  obtain ⟨t, ht, hr⟩ := outputs SourceCSPInputFrame.headerEmbedding before
    id id id (fun _ => rfl) none
    (SourceCSPHeaderValidFlag.program a q) (headerProgram a q)
    (fun _ => rfl) localCfg th hhalt
  have hstart : cfg SourceCSPInputFrame.headerEmbedding before id id none localCfg =
      (⟨some (.inl (.inl (.inl (.start 0)))),
        ((((none, none), none), none), (none, none, none)), before⟩ :
        TM2.Cfg (fun _ : Stack => Bool) (HeaderLabel a q) HeaderControl) := by
    simp only [cfg, stackCfg, BitMachineInline.cfg, localCfg, id_eq]
    congr 1
    apply bank_eq_self
    intro k
    exact congrFun (SourceCSPInputFrame.after_length_header input) k |>.symm
  have hlocal : ((advance (SourceCSPHeaderValidFlag.program a q))^[th])
      localCfg = ⟨none, ((((none, none), none), none), vh), Sh⟩ := by
    simpa only [localCfg] using hrh
  rw [hstart, hlocal] at hr
  let S : Stack → List Bool :=
    bank SourceCSPInputFrame.headerEmbedding before Sh
  refine ⟨t, ((((none, none), none), none), vh), S,
    wa, wq, ht.trans hth, ?_, ?_, ?_, ?_⟩
  · simpa only [headerProgram, S, cfg, stackCfg,
      BitMachineInline.cfg, id_eq, Option.map_none] using hr
  · change bank SourceCSPInputFrame.headerEmbedding _ _
      (SourceCSPInputFrame.headerEmbedding SourceCSPHeaderValidFlag.flagSlot) = _
    rw [bank_at]
    exact hflag
  · change bank SourceCSPInputFrame.headerEmbedding before Sh (.inr 2) = _
    rw [bank_outside]
    · exact SourceCSPInputFrame.after_length_cap input
    · rintro ⟨k, hk⟩
      cases hk
  · intro k hk
    change bank SourceCSPInputFrame.headerEmbedding before Sh (.inr k) = []
    rw [bank_outside]
    · exact SourceCSPInputFrame.after_length_unused input k hk
    · rintro ⟨j, hj⟩
      cases hj

def inputProgram (a q : Nat) :=
  BitMachineRawSequence.program SourceCSPInputFrame.lengthProgram
    (headerProgram a q) (.inl (.inl (.inl (.start 0))))
    ((none, none) : Option Bool × Option Bool)
    (((((none, none), none), none), (none, none, none)) : HeaderControl)

/-- Arbitrary bit input is physically counted, then parsed and checked for
the fixed `a,q` fields, without losing its unary raw-length budget. -/
theorem all_input (a q : Nat) (input : List Bool) :
    ∃ t S v wa wq,
      t ≤ 3 * input.length + 4 + 4 * (2 * input.length + 4) + 3 +
        (a.bits.length + 1) + (q.bits.length + 1) + 5 ∧
      ((advance (inputProgram a q))^[t])
        (⟨some (.inl (.inl BitMachineCopy.Label.scan)),
          ((none, none),
            ((((none, none), none), none), (none, none, none))),
          SourceCSPInputFrame.initial input⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (BitMachineRawSequence.Label
              (BitMachineRawSequence.Label BitMachineCopy.Label
                SourceInputLengthUnary.CountLabel)
              (HeaderLabel a q))
            ((Option Bool × Option Bool) × HeaderControl)) =
        ⟨none, ((none, none), v), S⟩ ∧
      S (.inl SourceCSPHeaderValidFlag.flagSlot) =
        [SourceCSPHeaderValidFlag.parserGood input &&
          decide (wq = q.bits) && decide (wa = a.bits)] ∧
      S (.inr 2) = List.replicate input.length true ∧
      (∀ k : Fin 7, 3 ≤ k.val → S (.inr k) = []) := by
  obtain ⟨tl, htl, hrl⟩ := SourceCSPInputFrame.length_framed input
  obtain ⟨th, vh, Sh, wa, wq, hth, hrh, hflag, hcap, hunused⟩ :=
    header_framed a q input
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    SourceCSPInputFrame.lengthProgram (headerProgram a q)
    (.inl BitMachineCopy.Label.scan :
      BitMachineRawSequence.Label BitMachineCopy.Label
        SourceInputLengthUnary.CountLabel)
    (.inl (.inl (.inl (.start 0))) : HeaderLabel a q)
    ((none, none) : Option Bool × Option Bool) (none, none)
    (((((none, none), none), none), (none, none, none)) : HeaderControl) vh
    (SourceCSPInputFrame.initial input)
    (SourceCSPInputFrame.afterLength input) Sh tl th hrl hrh
  refine ⟨t, Sh, vh, wa, wq, by omega, ?_, hflag, hcap, hunused⟩
  simpa only [inputProgram] using hr

end EthInapproximability.CurrentPaper.SourceCSPInputValid
