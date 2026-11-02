import Paper2.RecursiveSamplingLaws
import Paper2.LookupSeed

/-!
# Elementary generators for the Boolean lookup seed

Frozen v12, Appendix A `cl:seed` and Appendix D `app:implementation`.
The row generator asks for `p` individual uniform bits, not one uniform
choice from a carrier of size `2^p`. The column generator asks for one
uniform coordinate. Both generate exactly the existing lookup-seed laws.
These ideal finite-choice programs carry no additional machine-time claim.
-/

namespace Paper2.RecursiveSamplingSeed

open RecursiveSamplingProgram RecursiveSamplingLaws

/-- The explicit correspondence between one binary choice and one Boolean bit. -/
def bitEquiv : Fin 2 ≃ Bool where
  toFun i := decide (i.val = 1)
  invFun b := if b then 1 else 0
  left_inv i := by fin_cases i <;> rfl
  right_inv b := by cases b <;> rfl

@[simp] theorem bitEquiv_zero : bitEquiv 0 = false := rfl
@[simp] theorem bitEquiv_one : bitEquiv 1 = true := rfl

/-- One elementary alphabet-two draw. -/
def bit : Program Bool := Program.map bitEquiv (Program.uniform 2 (by decide))

/-- One fresh elementary draw for each bit of the actual seed row. -/
def seedRow (p : ℕ) : Program (Fin p → Bool) := iid bit p

/-- One elementary draw for the actual seed column. -/
def seedColumn (p : ℕ) (hp : 0 < p) : Program (Fin p) := Program.uniform p hp

theorem generates_bit : Generates bit (PositiveRationalLaw.uniform Bool).toFiniteLaw :=
  generates_uniform_equiv 2 bitEquiv

theorem generates_seedRow (p : ℕ) :
    Generates (seedRow p) (LookupSeed.rowLaw p).toFiniteLaw := by
  have h := generates_rational_iid generates_bit p
  rw [uniform_iid] at h
  exact h

theorem generates_seedColumn (p : ℕ) (hp : 0 < p) :
    Generates (seedColumn p hp) (LookupSeed.columnLaw p hp).toFiniteLaw := by
  letI : NeZero p := ⟨hp.ne'⟩
  exact generates_uniform p

@[simp] theorem maxDraws_bit : bit.maxDraws = 1 := by simp [bit]
@[simp] theorem maxAlphabet_bit : bit.maxAlphabet = 2 := by simp [bit]

theorem maxDraws_seedRow_le (p : ℕ) : (seedRow p).maxDraws ≤ p := by
  simpa only [seedRow, maxDraws_bit, Nat.mul_one] using maxDraws_iid_le bit p

@[simp] theorem maxDraws_seedColumn (p : ℕ) (hp : 0 < p) :
    (seedColumn p hp).maxDraws = 1 := by simp [seedColumn]

theorem maxAlphabet_seedRow_le (p : ℕ) : (seedRow p).maxAlphabet ≤ 2 := by
  simpa only [seedRow, maxAlphabet_bit] using maxAlphabet_iid_le bit p

@[simp] theorem maxAlphabet_seedColumn (p : ℕ) (hp : 0 < p) :
    (seedColumn p hp).maxAlphabet = p := by simp [seedColumn]

theorem seedRow_eventProb (p : ℕ) (E : Set (Fin p → Bool)) :
    (seedRow p).eventProb E = (LookupSeed.rowLaw p).toFiniteLaw.prob (· ∈ E) :=
  generates_eventProb (generates_seedRow p) E

theorem seedColumn_eventProb (p : ℕ) (hp : 0 < p) (E : Set (Fin p)) :
    (seedColumn p hp).eventProb E = (LookupSeed.columnLaw p hp).toFiniteLaw.prob (· ∈ E) :=
  generates_eventProb (generates_seedColumn p hp) E

end Paper2.RecursiveSamplingSeed

#print axioms Paper2.RecursiveSamplingSeed.generates_seedRow
#print axioms Paper2.RecursiveSamplingSeed.generates_seedColumn
#print axioms Paper2.RecursiveSamplingSeed.maxDraws_seedRow_le
#print axioms Paper2.RecursiveSamplingSeed.maxAlphabet_seedRow_le
