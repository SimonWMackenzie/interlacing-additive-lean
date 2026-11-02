import Paper2.CappedSamplerCouplingAdaptive

/-!
# Literal Boolean lists for the bounded adaptive sampler

Frozen v12 Appendix D, the bounded-random-tape implementation. Each draw
gets `R` consecutive attempts of `B` bits. The conversions below are
computational finite-tuple operations, not chosen enumerations. The uniform
law on lists of the announced length transports exactly to the existing
independent fair-bit law, including empty tapes and empty bit blocks.
No machine-time bound for these list operations is asserted here.
-/

namespace Paper2.RecursiveSamplingTape

open CappedSampler

/-- Number of bits, in draw/attempt/bit order. -/
def bitCount (B R N : ℕ) : ℕ := N * (R * B)

theorem bitCount_eq_allocated (B R N : ℕ) :
    bitCount B R N = Adaptive.allocatedBits B R N := by
  simp only [bitCount, Adaptive.allocatedBits, Nat.mul_comm R B]

/-- Unpack the recursive attempt product in its original order. -/
def attemptsEquiv (B : ℕ) : (R : ℕ) → BitTape B R ≃ (Fin R → Fin B → Bool)
  | 0 => (show Unit ≃ (Fin 0 → Fin B → Bool) from Equiv.ofUnique _ _)
  | R + 1 => ((Equiv.refl (Fin B → Bool)).prodCongr (attemptsEquiv B R)).trans
      (Fin.consEquiv (fun _ : Fin (R + 1) => Fin B → Bool))

/-- Unpack the recursive draw product in its original order. -/
def drawsEquiv (B R : ℕ) : (N : ℕ) → Adaptive.Tape B R N ≃ (Fin N → BitTape B R)
  | 0 => (show Unit ≃ (Fin 0 → BitTape B R) from Equiv.ofUnique _ _)
  | N + 1 => ((Equiv.refl (BitTape B R)).prodCongr (drawsEquiv B R N)).trans
      (Fin.consEquiv (fun _ : Fin (N + 1) => BitTape B R))

def arrayEquiv (B R N : ℕ) :
    Adaptive.Tape B R N ≃ (Fin N → Fin R → Fin B → Bool) :=
  (drawsEquiv B R N).trans (Equiv.piCongrRight fun _ => attemptsEquiv B R)

/-- Canonical row-major position; quotient and remainder give the inverse. -/
def positionEquiv (B R N : ℕ) :
    (Fin N × Fin R × Fin B) ≃ Fin (bitCount B R N) :=
  ((Equiv.refl (Fin N)).prodCongr finProdFinEquiv).trans finProdFinEquiv

@[simp] theorem positionEquiv_val (B R N : ℕ)
    (i : Fin N) (j : Fin R) (k : Fin B) :
    (positionEquiv B R N (i, j, k)).val = (i.val * R + j.val) * B + k.val := by
  change k.val + B * j.val + (R * B) * i.val = _
  ring

def flatEquiv (B R N : ℕ) :
    Adaptive.Tape B R N ≃ (Fin (bitCount B R N) → Bool) :=
  (arrayEquiv B R N).trans
    ((Equiv.piCongrRight fun _ : Fin N => (Equiv.curry (Fin R) (Fin B) Bool).symm).trans
      (((Equiv.curry (Fin N) (Fin R × Fin B) Bool).symm).trans
        (Equiv.arrowCongr (positionEquiv B R N) (Equiv.refl Bool))))

/-- The actual input is a Boolean list with the public length. -/
abbrev SerializedTape (B R N : ℕ) :=
  {bits : List Bool // bits.length = bitCount B R N}

def serializedTapeEquiv (B R N : ℕ) :
    SerializedTape B R N ≃ Adaptive.Tape B R N :=
  (Equiv.vectorEquivFin Bool (bitCount B R N)).trans (flatEquiv B R N).symm

def readTape (B R N : ℕ) (bits : SerializedTape B R N) : Adaptive.Tape B R N :=
  serializedTapeEquiv B R N bits

def writeTape (B R N : ℕ) (tape : Adaptive.Tape B R N) : SerializedTape B R N :=
  (serializedTapeEquiv B R N).symm tape

@[simp] theorem readTape_writeTape (B R N : ℕ) (tape : Adaptive.Tape B R N) :
    readTape B R N (writeTape B R N tape) = tape :=
  (serializedTapeEquiv B R N).apply_symm_apply tape

@[simp] theorem writeTape_readTape (B R N : ℕ) (bits : SerializedTape B R N) :
    writeTape B R N (readTape B R N bits) = bits :=
  (serializedTapeEquiv B R N).symm_apply_apply bits

@[simp] theorem writeTape_length (B R N : ℕ) (tape : Adaptive.Tape B R N) :
    (writeTape B R N tape).val.length = bitCount B R N :=
  (writeTape B R N tape).property

/-- The list entry at the explicit offset is the same bit that the
existing adaptive algorithm receives at that draw and attempt. -/
theorem readTape_bit (B R N : ℕ) (bits : SerializedTape B R N)
    (i : Fin N) (j : Fin R) (k : Fin B) :
    arrayEquiv B R N (readTape B R N bits) i j k =
      List.Vector.get bits (positionEquiv B R N (i, j, k)) := by
  change (arrayEquiv B R N) ((arrayEquiv B R N).symm
    (fun i j k => List.Vector.get bits (positionEquiv B R N (i, j, k)))) i j k = _
  rw [Equiv.apply_symm_apply]

/-- The actual iterated product law gives every complete tape the same
fair-bit weight; no conditioning on sampler success is involved. -/
theorem adaptiveLaw_weight (B R N : ℕ) (tape : Adaptive.Tape B R N) :
    (Adaptive.law B R N).weight tape = (1 / 2 : ℝ) ^ bitCount B R N := by
  induction N with
  | zero => simp [Adaptive.law, bitCount]
  | succ N ih =>
      change (bitTapeLaw B R).weight tape.1 * (Adaptive.law B R N).weight tape.2 = _
      rw [bitTapeLaw_weight, ih]
      have hb : ((2 ^ B : ℝ)⁻¹) ^ R = (1 / 2 : ℝ) ^ (R * B) := by
        rw [Nat.mul_comm R B, pow_mul]
        simp
      rw [hb]
      simp only [bitCount, Nat.succ_mul, pow_add]
      ring

/-- The enumeration exists only for finite probability analysis; neither
conversion enumerates a function space or invokes this instance. -/
noncomputable instance serializedTapeFintype (B R N : ℕ) :
    Fintype (SerializedTape B R N) :=
  Fintype.ofEquiv (Fin (bitCount B R N) → Bool)
    (Equiv.vectorEquivFin Bool (bitCount B R N)).symm

theorem serializedTape_card (B R N : ℕ) :
    Fintype.card (SerializedTape B R N) = 2 ^ bitCount B R N := by
  exact (Fintype.card_congr
    (Equiv.vectorEquivFin Bool (bitCount B R N))).trans (by simp)

/-- Uniform independent fair bits as literal lists of exactly the public length. -/
noncomputable def serializedTapeLaw (B R N : ℕ) : FiniteLaw (SerializedTape B R N) where
  weight _ := (1 / 2 : ℝ) ^ bitCount B R N
  nonneg _ := by positivity
  total := by
    simp [serializedTape_card]

theorem serializedTapeLaw_prob (B R N : ℕ) (E : Adaptive.Tape B R N → Prop) :
    (serializedTapeLaw B R N).prob (fun bits => E (readTape B R N bits)) =
      (Adaptive.law B R N).prob E := by
  classical
  unfold FiniteLaw.prob
  simp_rw [adaptiveLaw_weight]
  exact (serializedTapeEquiv B R N).sum_comp
    (fun tape => if E tape then (1 / 2 : ℝ) ^ bitCount B R N else 0)

end Paper2.RecursiveSamplingTape

#print axioms Paper2.RecursiveSamplingTape.readTape_writeTape
#print axioms Paper2.RecursiveSamplingTape.writeTape_readTape
#print axioms Paper2.RecursiveSamplingTape.readTape_bit
#print axioms Paper2.RecursiveSamplingTape.serializedTapeLaw_prob
