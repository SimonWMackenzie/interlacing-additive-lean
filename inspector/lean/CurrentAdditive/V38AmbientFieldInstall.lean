import CurrentAdditive.V38FieldPadBankRun
import CurrentAdditive.CanonicalAmbientSource
import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps

/-! The selected producer runs in the inherited renderer namespace. The
genuine field output is consumed by zero-padding, then a literal preserving
copy installs the padded bank in that same field-output cell. -/

noncomputable section

namespace CurrentAdditive.V38AmbientFieldInstall

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open CurrentAdditive.SmallBias CurrentAdditive.V38Machine CurrentAdditive.V38Clock
open CurrentAdditive.FieldSearchCompletion
open CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

def producerSlot (t : ℕ) : V38FieldPad.Stack → Cell t 16
  | .inl k => fieldCombinedEmbed t 16 k
  | .inr false => .copyScratch 1
  | .inr true => .copyScratch 2

def producerEmbed (t : ℕ) : V38FieldPad.Stack ↪ Cell t 16 :=
  ⟨producerSlot t, by
    intro a b h
    cases a with
    | inl a =>
        cases b with
        | inl b => exact congrArg Sum.inl ((fieldCombinedEmbed t 16).injective h)
        | inr b => cases a <;> cases b <;> simp [producerSlot, fieldCombinedEmbed] at h
    | inr a =>
        cases b with
        | inl b => cases b <;> cases a <;> simp [producerSlot, fieldCombinedEmbed] at h
        | inr b => cases a <;> cases b <;> simp_all [producerSlot]⟩

def fieldBankCell (t : ℕ) : Cell t 16 :=
  producerEmbed t (.inl V38FieldPad.fieldOutput)

def installPlace (t : ℕ) : Fin 3 ↪ Cell t 16 :=
  ⟨![.copyScratch 2, fieldBankCell t, .copyScratch 0], by
    intro a b h
    fin_cases a <;> fin_cases b <;>
      simp_all [fieldBankCell, producerEmbed, producerSlot,
        V38FieldPad.fieldOutput, FieldUnaryUnifiedMachine.fieldSlots, fieldCombinedEmbed]⟩

def producerProgram (t : ℕ) := fun l => stackStmt (producerEmbed t)
  (V38FieldPad.program (2 ^ t * 2 ^ t) (by positivity) l)

def installProgram (t : ℕ) :=
  BitMachineRawSequence.program (producerProgram t)
    (MatrixStage4ScalarPreparationOps.copyProgram (installPlace t))
    .scan (FieldUnaryUnifiedMachine.prepEmbed none, none) none

def sourceControl : V38FieldPad.Control := (FieldUnaryUnifiedMachine.prepEmbed none, none)

abbrev InstallLabel (t : ℕ) :=
  BitMachineRawSequence.Label (V38FieldPad.Label (2 ^ t * 2 ^ t)) BitMachineCopy.Label
abbrev InstallControl := V38FieldPad.Control × Option Bool

def initialConfig (t : ℕ) (S : Cell t 16 → List Bool) :=
  (⟨some (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (FieldUnaryUnifiedMachine.Label.prep .scanD))),
    (sourceControl, none), S⟩ :
      TM2.Cfg (fun _ : Cell t 16 => Bool) (InstallLabel t) InstallControl)

theorem producer_foreign_scratch (t : ℕ) :
    ¬ ∃ i : V38FieldPad.Stack, producerEmbed t i = .copyScratch 0 := by
  rintro ⟨i, hi⟩
  cases i with
  | inl i => cases i <;> simp [producerEmbed, producerSlot, fieldCombinedEmbed] at hi
  | inr i => cases i <;> simp [producerEmbed, producerSlot] at hi

/-- One literal ambient program both produces and installs the exact padded
bank. Public-input setup and renderer execution remain separate stages. -/
theorem physical_install (b t : ℕ) (ht : 4 ≤ t)
    (S : Cell t 16 → List Bool)
    (hlocal : ∀ i : V38FieldPad.Stack,
      S (producerEmbed t i) = (V38FieldPad.publicStart b t).stk i)
    (hscratch : S (.copyScratch 0) = []) :
    ∃ modulus,
      FiniteFieldConstructor.TrialSearch.firstPassing (v38FieldDegree b t) = some modulus ∧
      ∃ producerSteps ≤ 100 * (v38FieldTarget b t) ^ 5,
      ∃ total ≤ 108 * (v38FieldTarget b t) ^ 5,
        let produced := V38FieldPad.run (2 ^ t * 2 ^ t) (by positivity)
          producerSteps (V38FieldPad.publicStart b t)
        ((advance (installProgram t))^[total]) (initialConfig t S) =
          ⟨none, (sourceControl, none),
            Function.update (bank (producerEmbed t) S produced.stk)
              (fieldBankCell t) (paddedBits b t (v38FieldDegree b t) modulus)⟩ := by
  obtain ⟨c, hc, hfirst, steps, hsteps, hhalt, hout, hconsumed, hwork⟩ :=
    V38FieldPad.physical_field_pad_bank (2 ^ t * 2 ^ t)
      (v38FieldDegree b t) (v38PositionCount b t)
      (by positivity) (v38FieldDegree_pos b t ht)
  let modulus := FiniteFieldConstructor.TrialSearch.monicBits (v38FieldDegree b t) c
  let produced := V38FieldPad.run (2 ^ t * 2 ^ t) (by positivity) steps
    (V38FieldPad.publicStart b t)
  let T := bank (producerEmbed t) S produced.stk
  have hclock : steps ≤ 100 * (v38FieldTarget b t) ^ 5 :=
    hsteps.trans (V38FieldPad.public_wholeBudget b t ht)
  have hout' : produced.stk (.inr true) = paddedBits b t (v38FieldDegree b t) modulus :=
    hout.trans (V38ZeroPad.actual_padded_identity b t _ _)
  have hc' : produced.stk (.inl V38FieldPad.fieldOutput) = [] := hconsumed
  have hcfg : produced = ⟨none, produced.var, produced.stk⟩ := by
    have hp : produced.l = none := hhalt
    rcases produced with ⟨l, v, R⟩
    change l = none at hp
    subst l
    rfl
  have hstart : stackCfg (producerEmbed t) S (V38FieldPad.publicStart b t) =
      (⟨some (BitMachineRawSequence.leftLabel (FieldUnaryUnifiedMachine.Label.prep .scanD)),
        sourceControl, S⟩ : TM2.Cfg (fun _ : Cell t 16 => Bool)
          (V38FieldPad.Label (2 ^ t * 2 ^ t)) V38FieldPad.Control) := by
    have hb := bank_eq_self (producerEmbed t) S (V38FieldPad.publicStart b t).stk
      (by intro i; exact (hlocal i).symm)
    change (⟨_, _, bank (producerEmbed t) S (V38FieldPad.publicStart b t).stk⟩ :
      TM2.Cfg (fun _ : Cell t 16 => Bool) _ _) = _
    rw [hb]
    rfl
  have hprod : ((advance (producerProgram t))^[steps])
      (⟨some (BitMachineRawSequence.leftLabel (FieldUnaryUnifiedMachine.Label.prep .scanD)),
        sourceControl, S⟩ : TM2.Cfg (fun _ : Cell t 16 => Bool)
          (V38FieldPad.Label (2 ^ t * 2 ^ t)) V38FieldPad.Control) =
      ⟨none, produced.var, T⟩ := by
    have hr := BitMachineStackRun.run (producerEmbed t) S
      (V38FieldPad.program (2 ^ t * 2 ^ t) (by positivity))
      (V38FieldPad.publicStart b t) steps
    rw [hstart] at hr
    change _ = stackCfg (producerEmbed t) S produced at hr
    rw [hcfg] at hr
    exact hr
  have hsource : T (installPlace t 0) = paddedBits b t (v38FieldDegree b t) modulus := by
    change bank (producerEmbed t) S produced.stk (producerEmbed t (.inr true)) = _
    rw [bank_at]
    exact hout'
  have htarget : T (installPlace t 1) = [] := by
    change bank (producerEmbed t) S produced.stk
      (producerEmbed t (.inl V38FieldPad.fieldOutput)) = []
    rw [bank_at]
    exact hc'
  have htemp : T (installPlace t 2) = [] := by
    change bank (producerEmbed t) S produced.stk (.copyScratch 0) = []
    rw [bank_outside _ _ _ _ (producer_foreign_scratch t), hscratch]
  have hcopy := MatrixStage4ScalarPreparationOps.copy_run (installPlace t) T htemp
  rw [hsource, htarget, List.append_nil] at hcopy
  obtain ⟨total, htotal, hrun⟩ := BitMachineRawSequence.runs (producerProgram t)
    (MatrixStage4ScalarPreparationOps.copyProgram (installPlace t))
    (BitMachineRawSequence.leftLabel (FieldUnaryUnifiedMachine.Label.prep .scanD))
    .scan sourceControl produced.var none none S T
    (Function.update T (installPlace t 1) (paddedBits b t (v38FieldDegree b t) modulus))
    steps (2 * (paddedBits b t (v38FieldDegree b t) modulus).length + 2) hprod hcopy
  refine ⟨modulus, hfirst, steps, hclock, total, ?_, hrun⟩
  have hlength := V38FieldPad.padded_output_length_le b t modulus
  have hX : 1 ≤ v38FieldTarget b t := by
    have h := v38FieldTarget_gt_one b t ht
    omega
  have hpow : (v38FieldTarget b t) ^ 3 ≤ (v38FieldTarget b t) ^ 5 :=
    Nat.pow_le_pow_right hX (by decide)
  have hpos : 1 ≤ (v38FieldTarget b t) ^ 5 := Nat.one_le_pow _ _ hX
  omega

#print axioms physical_install

end CurrentAdditive.V38AmbientFieldInstall
