import CurrentAdditive.RawRatPairClear

/-! Full pair assembly followed by physical scratch restoration. -/

namespace CurrentAdditive.MinimumRatioContext.RawRatPairFull

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open MachineInvokeCore RawRatPairLift RawRatPairClear BitMachineStackEmbedding

def program (N : ℕ) :=
  BitMachineRawSequence.program (RawRatPairLift.program N)
    (RawRatPairClear.program N)
    (MachineInvokeClear.clearLabel 4 0)
    RawRatPairLift.control ((), none)

abbrev Label := BitMachineRawSequence.Label RawRatPairLift.Label RawRatPairClear.Label
abbrev Control := RawRatPairLift.Control × RawRatPairClear.Control

def start : Label :=
  BitMachineRawSequence.leftLabel RawRatPairLift.start

def control : Control := (RawRatPairLift.control, ((), none))

theorem scratch_ne_endpoint {N : ℕ} (i : Fin 4) (j : Fin 7)
    (hj : j.val = 0 ∨ j.val = 1 ∨ j.val = 6) :
    scratch i ≠ localSlot N j := by
  intro h
  have he : (⟨i.val + 2, by omega⟩ : Fin 7) = j :=
    (localSlot N).injective h
  have hv := congrArg Fin.val he
  simp at hv
  rcases hj with h0 | h1 | h6 <;> omega

theorem completed_16 {N : ℕ} (S : StackN N → List Bool)
    (x y : List Bool) (R : BitMachineBankSerialize.Bank 2) :
    bank (embed N) S
      (RawRatPairAssembler.completedBank x y (Fin.elim0) R) 16 = x := by
  change bank (embed N) S _ (embed N (.inl 0)) = x
  rw [bank_at]
  exact RawRatPairAssembler.completed_sourceX x y
    (Fin.elim0 : Fin 0 → List Bool) R

theorem completed_20 {N : ℕ} (S : StackN N → List Bool)
    (x y : List Bool) (R : BitMachineBankSerialize.Bank 2) :
    bank (embed N) S
      (RawRatPairAssembler.completedBank x y (Fin.elim0) R) 20 = y := by
  change bank (embed N) S _ (embed N (.inl 1)) = y
  rw [bank_at]
  exact RawRatPairAssembler.completed_sourceY x y
    (Fin.elim0 : Fin 0 → List Bool) R

theorem completed_26 {N : ℕ} (S : StackN N → List Bool)
    (x y : List Bool) (R : BitMachineBankSerialize.Bank 2) :
    bank (embed N) S
      (RawRatPairAssembler.completedBank x y (Fin.elim0) R) 26 =
      RawRatPairAssembler.pairWord x y := by
  change bank (embed N) S _ (embed N (.inl 6)) = _
  rw [bank_at]
  exact RawRatPairAssembler.completed_output x y
    (Fin.elim0 : Fin 0 → List Bool) R

theorem completed_cleanup {N : ℕ} (S : StackN N → List Bool)
    (x y : List Bool)
    (hx : S 16 = x) (hy : S 20 = y)
    (h22 : S 22 = []) (h23 : S 23 = [])
    (h24 : S 24 = []) (h25 : S 25 = [])
    (R : BitMachineBankSerialize.Bank 2) :
    BitMachineClearBank.cleared scratch
      (bank (embed N) S
        (RawRatPairAssembler.completedBank x y (Fin.elim0) R)) =
      Function.update S 26 (RawRatPairAssembler.pairWord x y) := by
  let B := bank (embed N) S
    (RawRatPairAssembler.completedBank x y (Fin.elim0) R)
  funext k
  by_cases hc : ∃ i : Fin 4, scratch i = k
  · obtain ⟨i, he⟩ := hc
    subst k
    rw [BitMachineClearBank.cleared_bank]
    have hne : scratch i ≠ (26 : StackN N) := by
      change scratch i ≠ localSlot N 6
      exact scratch_ne_endpoint i 6 (Or.inr (Or.inr rfl))
    have hs : S (scratch i) = [] := by
      fin_cases i
      · simpa [scratch, localSlot] using h22
      · simpa [scratch, localSlot] using h23
      · simpa [scratch, localSlot] using h24
      · simpa [scratch, localSlot] using h25
    simp [hne, hs]
  · rw [BitMachineClearBank.cleared_foreign scratch B k
      (by intro i; exact fun h => hc ⟨i, h⟩)]
    by_cases ho : k = 26
    · subst k
      simpa only [B, Function.update_self] using completed_26 S x y R
    · by_cases hi : ∃ i : Fin 7, localSlot N i = k
      · obtain ⟨i, he⟩ := hi
        fin_cases i
        · subst k
          change B 16 = Function.update S 26
            (RawRatPairAssembler.pairWord x y) 16
          have hne : (16 : StackN N) ≠ 26 := by
            simpa [localSlot] using ho
          rw [Function.update_of_ne hne, hx]
          exact completed_16 S x y R
        · subst k
          change B 20 = Function.update S 26
            (RawRatPairAssembler.pairWord x y) 20
          have hne : (20 : StackN N) ≠ 26 := by
            simpa [localSlot] using ho
          rw [Function.update_of_ne hne, hy]
          exact completed_20 S x y R
        · exact (hc ⟨0, by simpa [scratch] using he⟩).elim
        · exact (hc ⟨1, by simpa [scratch] using he⟩).elim
        · exact (hc ⟨2, by simpa [scratch] using he⟩).elim
        · exact (hc ⟨3, by simpa [scratch] using he⟩).elim
        · exact (ho (by simpa [localSlot] using he.symm)).elim
      · have hforeign : ¬ ∃ j : RawRatPairAssembler.Stack 0,
            embed N j = k := by
          rintro ⟨j, hj⟩
          cases j with
          | inl j => exact hi ⟨j, hj⟩
          | inr j => exact Fin.elim0 j
        dsimp only [B]
        rw [bank_outside (embed N) S _ k hforeign]
        simp [ho]

theorem scratch_initial {N : ℕ} (S : StackN N → List Bool)
    (h22 : S 22 = []) (h23 : S 23 = [])
    (h24 : S 24 = []) (h25 : S 25 = [])
    (i : Fin 4) : S (scratch i) = [] := by
  fin_cases i
  · simpa [scratch, localSlot] using h22
  · simpa [scratch, localSlot] using h23
  · simpa [scratch, localSlot] using h24
  · simpa [scratch, localSlot] using h25

def linearBound (N : ℕ) (x y : List Bool) : ℕ :=
  (1 + 4 * BitMachineStackGrowth.perStep (RawRatPairLift.program N)) *
    (6 * (x.length + y.length + 2)) + 7

/-- Literal assembly, then literal clearing of all four temporary cells. -/
theorem run_linear {N : ℕ} (S : StackN N → List Bool)
    (x y : List Bool)
    (hx : S 16 = x) (hy : S 20 = y)
    (h22 : S 22 = []) (h23 : S 23 = [])
    (h24 : S 24 = []) (h25 : S 25 = [])
    (h26 : S 26 = []) :
    ∃ u ≤ linearBound N x y,
      ((advance (program N))^[u])
        (⟨some start, control, S⟩ :
          TM2.Cfg (fun _ : StackN N => Bool) _ _) =
        ⟨none, control,
          Function.update S 26 (RawRatPairAssembler.pairWord x y)⟩ := by
  obtain ⟨t, ht, R, hrun⟩ := RawRatPairLift.embedded_run S x y
    hx hy h22 h23 h24 h25 h26
  let B := bank (embed N) S
    (RawRatPairAssembler.completedBank x y (Fin.elim0) R)
  let P := BitMachineStackGrowth.perStep (RawRatPairLift.program N)
  have hlen (i : Fin 4) : (B (scratch i)).length ≤ P * t := by
    have hg := BitMachineStackGrowth.run_growth
      (RawRatPairLift.program N)
      (⟨some RawRatPairLift.start, RawRatPairLift.control, S⟩ :
        TM2.Cfg (fun _ : StackN N => Bool) _ _) t (scratch i)
    rw [hrun] at hg
    have h0 := scratch_initial S h22 h23 h24 h25 i
    simpa only [B, P, h0, List.length_nil, Nat.zero_add] using hg
  have hsum : (∑ i : Fin 4, (B (scratch i)).length) ≤ 4 * (P * t) := by
    have hh := Finset.sum_le_sum (s := Finset.univ)
      (fun i (_ : i ∈ Finset.univ) => hlen i)
    simpa using hh
  have htime : RawRatPairClear.time B ≤ 4 * P * t + 6 := by
    unfold RawRatPairClear.time
    nlinarith [hsum]
  have hclear := RawRatPairClear.run B
  rw [completed_cleanup S x y hx hy h22 h23 h24 h25 R] at hclear
  obtain ⟨u, hu, hfull⟩ := BitMachineRawSequence.runs
    (RawRatPairLift.program N) (RawRatPairClear.program N)
    RawRatPairLift.start (MachineInvokeClear.clearLabel 4 0)
    RawRatPairLift.control RawRatPairLift.control
    ((), none) ((), none)
    S B (Function.update S 26 (RawRatPairAssembler.pairWord x y))
    t (RawRatPairClear.time B)
    (by simpa only [B] using hrun)
    (by simpa only [B] using hclear)
  have hstep :
      u ≤ (1 + 4 * P) * t + 7 := by
    calc
      u ≤ t + RawRatPairClear.time B + 1 := hu
      _ ≤ t + (4 * P * t + 6) + 1 := by omega
      _ = (1 + 4 * P) * t + 7 := by ring
  have hmul : (1 + 4 * P) * t ≤
      (1 + 4 * P) * (6 * (x.length + y.length + 2)) :=
    Nat.mul_le_mul_left _ ht
  refine ⟨u, ?_, ?_⟩
  · unfold linearBound
    exact hstep.trans (Nat.add_le_add_right hmul 7)
  · simpa only [program, start, control] using hfull

theorem run_pairBytes {N : ℕ} (S : StackN N → List Bool)
    (x y : CodeDCodec.RawRat)
    (hx : S 16 = CodeDCodec.encodeRawRat x)
    (hy : S 20 = CodeDCodec.encodeRawRat y)
    (h22 : S 22 = []) (h23 : S 23 = [])
    (h24 : S 24 = []) (h25 : S 25 = [])
    (h26 : S 26 = []) :
    ∃ u ≤ linearBound N (CodeDCodec.encodeRawRat x)
        (CodeDCodec.encodeRawRat y),
      ((advance (program N))^[u])
        (⟨some start, control, S⟩ :
          TM2.Cfg (fun _ : StackN N => Bool) _ _) =
        ⟨none, control,
          Function.update S 26 (CodeDPairProductTargetV2.pairBytes x y)⟩ := by
  simpa only [RawRatPairAssembler.pairWord_exact] using
    run_linear S (CodeDCodec.encodeRawRat x) (CodeDCodec.encodeRawRat y)
      hx hy h22 h23 h24 h25 h26

#print axioms completed_cleanup
#print axioms run_linear
#print axioms run_pairBytes

end CurrentAdditive.MinimumRatioContext.RawRatPairFull
