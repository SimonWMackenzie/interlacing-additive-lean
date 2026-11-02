import EthInapproximability.CurrentPaper.SamplerMachineAccumulate

/-!
Physical leading-term cancellation for one GF(2) long-division step.
The accumulator and shifted monic divisor are high-bit-first Boolean words
of equal width. The existing four-stack conditional-XOR machine consumes
their leading accumulator bit as its Boolean control, restores the divisor,
and leaves a zero leading coefficient. Removing that known zero and arranging
the next shifted divisor belong to the surrounding trial controller.
-/

namespace CurrentAdditive.FieldMachineHelper.DivisionBitStep

open EthInapproximability.CurrentPaper.SamplerMachineAccumulate

theorem addScaled_monic_head (top : Bool) (accTail divisorTail : List Bool) :
    addScaled top (top :: accTail) (true :: divisorTail) =
      false :: addScaled top accTail divisorTail := by
  cases top <;> simp [addScaled]

theorem run_cancel_leading_bit (top : Bool)
    (accTail divisorTail : List Bool)
    (hlen : accTail.length = divisorTail.length) :
    run (2 * (accTail.length + 1) + 2)
      (cfg (some .scan) (top, none, none)
        (top :: accTail) (true :: divisorTail) [] []) =
    cfg none (top, none, none)
      (false :: addScaled top accTail divisorTail)
      (true :: divisorTail) [] [] := by
  simpa [addScaled_monic_head] using
    run_correct top none none (top :: accTail) (true :: divisorTail)
      (by simpa using hlen)

theorem cancel_tail_eq_zipWith (top : Bool)
    (accTail divisorTail : List Bool) :
    addScaled top accTail divisorTail =
      List.zipWith (fun x y => x ^^ (top && y)) accTail divisorTail := rfl

/-- The high-bit-first view of a natural-number polynomial encoding. -/
def bitsBE (width value : ℕ) : List Bool :=
  ((List.range width).map value.testBit).reverse

theorem bitsBE_succ (width value : ℕ) :
    bitsBE (width + 1) value = value.testBit width :: bitsBE width value := by
  simp [bitsBE, List.range_succ, List.map_append, List.reverse_append]

theorem bitsBE_length (width value : ℕ) :
    (bitsBE width value).length = width := by
  simp [bitsBE]

theorem bitsBE_xor (width a b : ℕ) :
    bitsBE width (Nat.xor a b) =
      List.zipWith Bool.xor (bitsBE width a) (bitsBE width b) := by
  induction width with
  | zero => simp [bitsBE]
  | succ width ih =>
    simpa [bitsBE_succ, ih, Nat.testBit_xor]

private theorem zipWith_left_of_equal_length (a b : List Bool)
    (h : a.length = b.length) :
    List.zipWith (fun x _ => x) a b = a := by
  induction a generalizing b with
  | nil => simp
  | cons x xs ih =>
    cases b with
    | nil => simp at h
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp [ih ys h]

theorem cancel_tail_nat_step (width acc shiftedDivisor : ℕ) :
    addScaled (acc.testBit width)
      (bitsBE width acc) (bitsBE width shiftedDivisor) =
    bitsBE width
      (if acc.testBit width then Nat.xor acc shiftedDivisor else acc) := by
  cases htop : acc.testBit width
  · simp [addScaled, zipWith_left_of_equal_length, bitsBE_length]
  · simp only [ite_true]
    rw [bitsBE_xor]
    simp [addScaled]

theorem run_cancel_nat_step (width acc shiftedDivisor : ℕ)
    (hmonic : shiftedDivisor.testBit width = true) :
    run (2 * (width + 1) + 2)
      (cfg (some .scan) (acc.testBit width, none, none)
        (bitsBE (width + 1) acc)
        (bitsBE (width + 1) shiftedDivisor) [] []) =
    cfg none (acc.testBit width, none, none)
      (bitsBE (width + 1)
        (if acc.testBit width then Nat.xor acc shiftedDivisor else acc))
      (bitsBE (width + 1) shiftedDivisor) [] [] := by
  rw [bitsBE_succ width acc, bitsBE_succ width shiftedDivisor, hmonic]
  have hrun := run_cancel_leading_bit (acc.testBit width)
    (bitsBE width acc) (bitsBE width shiftedDivisor)
    (by simp [bitsBE_length])
  rw [bitsBE_length] at hrun
  rw [hrun]
  cases htop : acc.testBit width
  · simp only [htop, Bool.false_eq_true, ite_false, bitsBE_succ]
    simp [addScaled, zipWith_left_of_equal_length, bitsBE_length]
  · simp only [ite_true, bitsBE_succ]
    rw [bitsBE_xor]
    simp [htop, hmonic, addScaled]

#print axioms run_cancel_leading_bit
#print axioms run_cancel_nat_step

end CurrentAdditive.FieldMachineHelper.DivisionBitStep
