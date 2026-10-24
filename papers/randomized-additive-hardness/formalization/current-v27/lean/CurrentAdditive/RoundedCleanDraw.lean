import CurrentAdditive.RoundedTicketUnaryBridge
import EthInapproximability.CurrentPaper.BitMachineClearBank
import EthInapproximability.CurrentPaper.BitMachineStackGrowth

/-! A repeatable physical rounded draw. The finite controller is fixed. Every
scratch cell is explicitly popped before return; the whole final bank, the
unused suffix, and an input-only clock are specified. No source interpreter,
complete recursive label, or complete table is claimed by this module. -/

namespace EthInapproximability.CurrentPaper.RoundedCleanDraw

open Turing Turing.TM2.Stmt BitMachineEncoding
open scoped BigOperators
noncomputable section

abbrev Stack := RoundedTicketUnary.Stack
abbrev TicketControl := RoundedTicketUnary.Control
abbrev Control := TicketControl × Option Bool

def tape : Stack := .inl (.inr 1)
def output : Stack := .inr 2

abbrev ClearSlot := {k : Stack // k ≠ tape ∧ k ≠ output}
abbrev clearCount : ℕ := Fintype.card ClearSlot

def clearSlot (i : Fin clearCount) : Stack :=
  ((Fintype.equivFin ClearSlot).symm i).val

theorem clearSlot_injective : Function.Injective clearSlot := by
  intro i j h
  exact (Fintype.equivFin ClearSlot).symm.injective (Subtype.val_injective h)

theorem clearSlot_ne_tape (i : Fin clearCount) : clearSlot i ≠ tape :=
  ((Fintype.equivFin ClearSlot).symm i).property.1

theorem clearSlot_ne_output (i : Fin clearCount) : clearSlot i ≠ output :=
  ((Fintype.equivFin ClearSlot).symm i).property.2

theorem exists_clearSlot (k : Stack) :
    (∃ i, clearSlot i = k) ↔ k ≠ tape ∧ k ≠ output := by
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨clearSlot_ne_tape i, clearSlot_ne_output i⟩
  · intro hk
    refine ⟨(Fintype.equivFin ClearSlot) ⟨k, hk⟩, ?_⟩
    simp [clearSlot]

inductive Label where
  | ticket (l : RoundedTicketUnary.Label)
  | clear (i : Fin (clearCount + 1))
  | stop
  deriving DecidableEq, Fintype

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def initial : Control := (RoundedTicketUnary.initial, none)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .ticket l => BitMachineInline.stmt Label.ticket (fun v => (v, none))
      Prod.fst (some (.clear 0)) (RoundedTicketUnary.program l)
  | .clear i =>
      if h : i.val < clearCount then
        BitMachineClearBank.clearStep (clearSlot ⟨i.val, h⟩)
          (.clear i) (.clear ⟨i.val + 1, by omega⟩)
      else BitMachineClearBank.finishStep (fun _ => RoundedTicketUnary.initial) .stop
  | .stop => halt

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

def start (source word suffix : List Bool) (a : ℕ) : Config :=
  BitMachineInline.cfg Label.ticket (fun v => (v, none)) (some (.clear 0))
    (RoundedTicketUnary.start source word suffix a)

def cleanBank (suffix result : List Bool) : Stack → List Bool :=
  fun k => if k = tape then suffix else if k = output then result else []

def cleanClock (S : Stack → List Bool) : ℕ :=
  (∑ i : Fin clearCount, (S (clearSlot i)).length) + clearCount + 2

theorem cleared_eq_cleanBank (S : Stack → List Bool) :
    BitMachineClearBank.cleared clearSlot S = cleanBank (S tape) (S output) := by
  funext k
  by_cases ht : k = tape
  · subst k
    simp [BitMachineClearBank.cleared, exists_clearSlot, cleanBank]
  · by_cases ho : k = output
    · subst k
      simp [BitMachineClearBank.cleared, exists_clearSlot, cleanBank, output, tape]
    · simp [BitMachineClearBank.cleared, exists_clearSlot, cleanBank, ht, ho]

private theorem clear_program (i : Fin clearCount) :
    program (.clear i.castSucc) =
      BitMachineClearBank.clearStep (clearSlot i) (.clear i.castSucc) (.clear i.succ) := by
  simp only [program]
  split_ifs with h
  · rfl
  · exact (h i.isLt).elim

theorem clean_run (v : TicketControl) (S : Stack → List Bool) :
    run (cleanClock S) ⟨some (.clear 0), (v, none), S⟩ =
      ⟨none, initial, cleanBank (S tape) (S output)⟩ := by
  have hr := BitMachineClearBank.clear_bank_run program
    (fun _ => RoundedTicketUnary.initial) .stop clearCount clearSlot
    clearSlot_injective Label.clear clear_program
    (by simp [program]) v S
  change run ((∑ i : Fin clearCount, (S (clearSlot i)).length) + clearCount + 1)
    ⟨some (.clear 0), (v, none), S⟩ =
    ⟨some .stop, initial, BitMachineClearBank.cleared clearSlot S⟩ at hr
  rw [show cleanClock S =
    ((∑ i : Fin clearCount, (S (clearSlot i)).length) + clearCount + 1) + 1 by
      simp [cleanClock], run, Function.iterate_succ_apply']
  change advance program (run _ _) = _
  rw [hr]
  simp [advance, TM2.step, program, cleared_eq_cleanBank]

def drawClock (source word : List Bool) : ℕ :=
  100 * (source.length + word.length + 2) ^ 2 +
    (EncodedCommunication.bitsValue source + 1) *
      (4 * (source.length + 2 * word.length) + 5) + 1

/-- This is a constant of the literal fixed rounded/unary instruction table,
independent of source words, alphabet sizes, widths and unused tape. -/
def pushConstant : ℕ := BitMachineStackGrowth.perStep RoundedTicketUnary.program

def clock (source word : List Bool) : ℕ :=
  let T := drawClock source word
  T + clearCount * (source.length + word.length +
    EncodedCommunication.bitsValue source + 1 + pushConstant * T) + clearCount + 2

theorem start_private_length (source word suffix : List Bool) (a : ℕ)
    (k : Stack) (hk : k ≠ tape) :
    ((RoundedTicketUnary.start source word suffix a).stk k).length ≤
      source.length + word.length + a + 1 := by
  rcases k with (((i | i) | i) | i)
  · fin_cases i <;>
      simp [RoundedTicketUnary.start, RoundedTicketUnary.cfg,
        RoundedTicketUnary.bank, RoundedMachine.cfg, RoundedMachine.bank,
        RoundedMachine.mulStart, BitMachineBinaryMultiply.cfg,
        BitMachineBinaryMultiply.rightBank, BitMachineBinaryAddAny.bank,
        BitMachineBinaryAdd.bank]
  · fin_cases i <;>
      simp [RoundedTicketUnary.start, RoundedTicketUnary.cfg,
        RoundedTicketUnary.bank, RoundedMachine.cfg, RoundedMachine.bank,
        RoundedMachine.mulStart, BitMachineBinaryMultiply.cfg,
        BitMachineBinaryMultiply.rightBank] <;> omega
  · fin_cases i
    all_goals simp [RoundedTicketUnary.start, RoundedTicketUnary.cfg,
      RoundedTicketUnary.bank, RoundedMachine.cfg, RoundedMachine.bank,
      RoundedMachine.rightBank] at *
    all_goals try omega
    exact (hk rfl).elim
  · fin_cases i <;>
      simp [RoundedTicketUnary.start, RoundedTicketUnary.cfg,
        RoundedTicketUnary.bank, RoundedTicketUnary.rightBank] <;> omega

theorem cleanClock_le_of_run (source word suffix : List Bool)
    (t : ℕ) (c : RoundedTicketUnary.Config)
    (hr : RoundedTicketUnary.run t
      (RoundedTicketUnary.start source word suffix (EncodedCommunication.bitsValue source)) = c) :
    cleanClock c.stk ≤ clearCount *
      (source.length + word.length + EncodedCommunication.bitsValue source + 1 +
        pushConstant * t) + clearCount + 2 := by
  have hcell (i : Fin clearCount) :
      (c.stk (clearSlot i)).length ≤
        source.length + word.length + EncodedCommunication.bitsValue source + 1 +
          pushConstant * t := by
    have h := BitMachineStackGrowth.run_growth RoundedTicketUnary.program
      (RoundedTicketUnary.start source word suffix (EncodedCommunication.bitsValue source))
      t (clearSlot i)
    change ((RoundedTicketUnary.run t _).stk _).length ≤ _ at h
    rw [hr] at h
    exact h.trans (Nat.add_le_add_right
      (start_private_length source word suffix _ _ (clearSlot_ne_tape i)) _)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hcell i)
  simpa [cleanClock, Finset.sum_const, Fintype.card_fin, smul_eq_mul] using
    Nat.add_le_add_right (Nat.add_le_add_right hs clearCount) 2

/-- One fixed physical program gives the exact unary result and arbitrary
unused suffix, then empties every other stack. The bound charges the actual
computation, every discarded bit, empty-stack tests and control reset. -/
theorem physical_clean (source word suffix : List Bool)
    (ha : 0 < EncodedCommunication.bitsValue source) :
    ∃ t ≤ clock source word,
      run t (start source word suffix (EncodedCommunication.bitsValue source)) =
        ⟨none, initial, cleanBank suffix
          (List.replicate (EncodedCommunication.bitsValue
            (RoundedMachine.outputWord source word)) true ++ [false])⟩ := by
  obtain ⟨t, c, ht, hr, hl, ho, hs⟩ :=
    RoundedTicketUnary.physical_unary_polynomial_clock source word suffix ha
  have hh : (((advance RoundedTicketUnary.program)^[t])
      (RoundedTicketUnary.start source word suffix (EncodedCommunication.bitsValue source))).l = none := by
    change (RoundedTicketUnary.run t _).l = none
    rw [hr]
    exact hl
  obtain ⟨u, hu, hur⟩ := BitMachineInline.outputs Label.ticket
    (fun v => (v, none)) Prod.fst (by intro v; rfl) (some (.clear 0))
    RoundedTicketUnary.program program (by intro l; rfl)
    (RoundedTicketUnary.start source word suffix (EncodedCommunication.bitsValue source)) t hh
  change run u (start source word suffix _) =
    BitMachineInline.cfg Label.ticket (fun v => (v, none)) (some (.clear 0))
      (RoundedTicketUnary.run t _) at hur
  rw [hr] at hur
  have hur' : run u (start source word suffix (EncodedCommunication.bitsValue source)) =
      ⟨some (.clear 0), (c.var, none), c.stk⟩ := by
    simpa [BitMachineInline.cfg, hl] using hur
  refine ⟨u + cleanClock c.stk, ?_, ?_⟩
  · have hc := cleanClock_le_of_run source word suffix t c hr
    have ht' : t ≤ drawClock source word := ht
    have hp := Nat.mul_le_mul_left pushConstant ht'
    have hq := Nat.mul_le_mul_left clearCount
      (Nat.add_le_add_left hp
        (source.length + word.length + EncodedCommunication.bitsValue source + 1))
    dsimp only [clock]
    omega
  · rw [run, Nat.add_comm u _, Function.iterate_add_apply]
    change run (cleanClock c.stk) (run u _) = _
    rw [hur', clean_run]
    change (⟨none, initial, cleanBank
      (c.stk (.inl (.inr 1))) (c.stk (.inr 2))⟩ : Config) = _
    rw [ho, hs]

theorem physical_finCodec (a b : ℕ) (ha : 0 < a)
    (bits : Fin b → Bool) (suffix : List Bool) :
    ∃ t ≤ clock a.bits (Paper2.CappedTicketMachine.ticketWord bits),
      run t (start a.bits (Paper2.CappedTicketMachine.ticketWord bits) suffix a) =
        ⟨none, initial, cleanBank suffix
          ((Paper2.RecursiveLabelCodecScratch.finCodec a).encode
            (CurrentAdditive.RoundedDraw.draw a (2 ^ b) ha (by positivity)
              (Paper2.CappedSampler.bitsTicketEquiv b bits)))⟩ := by
  obtain ⟨t, ht, hr⟩ := physical_clean a.bits
    (Paper2.CappedTicketMachine.ticketWord bits) suffix
    (by simpa [EncodedCommunication.bitsValue_bits] using ha)
  refine ⟨t, ht, ?_⟩
  simpa only [EncodedCommunication.bitsValue_bits,
    RoundedMachine.output_matches_draw a b ha bits] using hr

#print axioms clean_run
#print axioms cleanClock_le_of_run
#print axioms physical_clean
#print axioms physical_finCodec

end
end EthInapproximability.CurrentPaper.RoundedCleanDraw
