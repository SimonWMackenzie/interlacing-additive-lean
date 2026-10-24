import EthInapproximability.CurrentPaper.EntryClockPoly3TF

/-!
# Lane owner:b-entry-clock-3, segment 1 (close): the level-0 writer-22 clock with NO free `T`

`T22_0_le`: the literal clock `T22_0` of the admitted `EntryPrepFamily.level0_writer22`
(`SeedTable.bound … + (prepBound G n c (labBound G n c (TF G n c)) + (tailBound + clearBound + 1)
+ 1) + 1`) is `≤ (n + |enc G| + 1)^C + 2^(C p)` for ONE absolute `C`, under the naming premise
only. Proof: the admitted `EntryClockPoly.writer22_clock_le` at `T := TF G n c` plus `TF_le`.

`level0_writer22_poly`: the admitted consumer `OuterLevel0Full.Writer22Spec` for owner-8's fixed
program (literally the program, start label and start control of `EntryPrepFamily.level0_writer22`)
with the polynomial clock, from the admitted `EntryClockPoly.level0_writer22_clock_poly`, the
admitted `EntryPrepFamily.family4` and `TF_le`. No premise besides the naming premise.
-/

namespace EthInapproximability.CurrentPaper.EntryClockPoly3

set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000
set_option maxRecDepth 16384

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Ready OuterLevel0Prep
open EntryPrepBudget EntryTailEmbed EntryTailClear EntryPrepCopy EntryPrepVec EntryPrepFamily

/-- Two polynomial clocks merge into one. -/
theorem merge2 (X p A B : ℕ) (hX : 2 ≤ X) (hp : 1 ≤ p) :
    X ^ A + 2 ^ (A * p) + (X ^ B + 2 ^ (B * p)) ≤
      X ^ (max A B + 1) + 2 ^ ((max A B + 1) * p) := by
  have hX1 : 1 ≤ X := by omega
  have a1 : X ^ A ≤ X ^ max A B := Nat.pow_le_pow_right hX1 (le_max_left _ _)
  have a2 : X ^ B ≤ X ^ max A B := Nat.pow_le_pow_right hX1 (le_max_right _ _)
  have b1 : 2 ^ (A * p) ≤ 2 ^ (max A B * p) :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (le_max_left _ _))
  have b2 : 2 ^ (B * p) ≤ 2 ^ (max A B * p) :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (le_max_right _ _))
  have eX : X ^ (max A B + 1) = X ^ max A B * X := pow_succ _ _
  have e2 : 2 ^ ((max A B + 1) * p) = 2 ^ (max A B * p) * 2 ^ p := by
    rw [show (max A B + 1) * p = max A B * p + p by ring, pow_add]
  have h2p : 2 ≤ 2 ^ p := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) hp
  have c1 : 2 * X ^ max A B ≤ X ^ max A B * X := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hX
  have c2 : 2 * 2 ^ (max A B * p) ≤ 2 ^ (max A B * p) * 2 ^ p := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ h2p
  rw [eX, e2]
  omega

/-- The naming premise gives `p ≥ 1` (the admitted `oneLevelBound = 128 T^4`, `T ≥ 128`). -/
theorem naming_pos {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EndpointGraph V E) (n c p : ℕ)
    (hname : EffectiveIteration.oneLevelBound (EntryClockPoly.P0 G n c) ≤ p) : 1 ≤ p := by
  have h128 := (EffectiveIteration.parameter_size_bounds (EntryClockPoly.P0 G n c)).1
  rw [EffectiveIteration.oneLevelBound, ← EffectiveIteration.nextScale_identity] at hname
  have : 1 ≤ Parameters.balanceOrder (EntryClockPoly.P0 G n c) ^ 4 := Nat.one_le_pow _ _ (by omega)
  omega

/-- **Segment 1.** The literal clock of the admitted `EntryPrepFamily.level0_writer22` is
polynomial: ONE absolute `C`, no free `T`, only the naming premise. -/
theorem T22_0_le : ∃ C : ℕ, ∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EndpointGraph V E) (n c p : ℕ),
    EffectiveIteration.oneLevelBound (EntryClockPoly.P0 G n c) ≤ p →
    SeedTable.bound (IndexSeed.width (EffectiveIteration.sourceDepth n)) +
        (prepBound G n c (labBound G n c (TF G n c)) + (tailBound G n c + clearBound G n c + 1) + 1) + 1 ≤
      (n + EntryClockPoly.ellG G + 1) ^ C + 2 ^ (C * p) := by
  obtain ⟨C1, h1⟩ := EntryClockPoly.writer22_clock_le
  obtain ⟨C2, h2⟩ := TF_le
  refine ⟨max C1 C2 + 1, fun {V E} _ _ _ _ G n c p hname => ?_⟩
  have hw := h1 G n c p (TF G n c) hname
  have ht := h2 G n c p hname
  have hell : ell3 G = EntryClockPoly.ellG G := rfl
  rw [hell] at ht
  have hX : 2 ≤ n + EntryClockPoly.ellG G + 1 := by
    have := card_le_ell3 G; rw [hell] at this; omega
  have hm := merge2 (n + EntryClockPoly.ellG G + 1) p C1 C2 hX (naming_pos G n c p hname)
  omega

variable (Mm : BitMachine.Machine)

/-- **Segment 1, consumer form.** The admitted `OuterLevel0Full.Writer22Spec` for owner-8's fixed
program with ONE polynomial clock; the only premise is the naming premise. -/
theorem level0_writer22_poly : ∃ C : ℕ, ∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : EndpointGraph V E) (n c p : ℕ),
    EffectiveIteration.oneLevelBound (EntryClockPoly.P0 G n c) ≤ p →
    OuterLevel0Full.Writer22Spec Mm
      (BitMachineRawSequence.program EntrySeedSpec.seedProgram
        (BitMachineRawSequence.program
          (prepProg4 progF
            (BitMachineRawSequence.leftLabel (MultiMove.startLabel (jobsA.map CopyFill.toJob)))
            (MultiMove.initial, ((), (MultiMove.initial, (EntryFamilyLevel.initialControl,
              (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool)))))))))
          tailClear
          (BitMachineRawSequence.leftLabel RawTableTail.startLabel)
          (prepInit ((MultiMove.initial, false),
            (MultiMove.initial, ((), (MultiMove.initial, (EntryFamilyLevel.initialControl,
              (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool))))))))))
          (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool))))
        (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel (MultiMove.startLabel (copyJobs.map CopyFill.toJob)))))
        ((none : Option Bool), (none : Option Bool))
        (prepInit ((MultiMove.initial, false),
            (MultiMove.initial, ((), (MultiMove.initial, (EntryFamilyLevel.initialControl,
              (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool))))))))),
          (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool)))))
      (BitMachineRawSequence.leftLabel SeedTable.startLabel)
      (((none : Option Bool), (none : Option Bool)),
        (prepInit ((MultiMove.initial, false),
            (MultiMove.initial, ((), (MultiMove.initial, (EntryFamilyLevel.initialControl,
              (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool))))))))),
          (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool)))))
      ((n + EntryClockPoly.ellG G + 1) ^ C + 2 ^ (C * p)) G n c := by
  obtain ⟨C0, h0⟩ := TF_le
  obtain ⟨C, hC⟩ := EntryClockPoly.level0_writer22_clock_poly Mm C0
  exact ⟨C, fun {V E} _ _ _ _ G n c p hname =>
    hC G n c p progF _ _ (TF G n c) hname (h0 G n c p hname) (family4 Mm G n c)⟩

#print axioms merge2
#print axioms T22_0_le
#print axioms level0_writer22_poly

end EthInapproximability.CurrentPaper.EntryClockPoly3
