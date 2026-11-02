import Paper2.AFrontTransducer
import EthInapproximability.CurrentPaper.BinarySuccessorMachine
import EthInapproximability.CurrentPaper.SourceFieldWriter
import EthInapproximability.CurrentPaper.ComplexityReductionClosure

/-!
# Fixed-gap binary threshold header

For a fixed positive gap `k`, this is a physical polynomial-time map from
the canonical LSB-first bits of `B` to `natField (2*B+k)`.  It uses `k/2`
iterations of the verified finite-stack binary successor, a one-pass prepend
transducer for the parity bit, and the verified self-delimiting field writer.
The machine depends on fixed `k`, not on `B` or on the input matrix.
-/

namespace Paper2.FixedGapHeader

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open AFront.Transducer

def addBits (c : ℕ) (q : List Bool) : List Bool :=
  (BinarySuccessorMachine.successor^[c]) q

theorem addBits_nat (c B : ℕ) : addBits c B.bits = (B + c).bits := by
  induction c with
  | zero => rfl
  | succ c ih =>
      rw [addBits, Function.iterate_succ_apply', ← addBits, ih,
        BinarySuccessorMachine.successor_bits]
      congr 1

theorem addBits_polytime (c : ℕ) : BitMachine.Polytime (addBits c) := by
  induction c with
  | zero => simpa [addBits] using
      ComplexityReductionClosure.polytime_id
  | succ c ih =>
      have heq : addBits (c + 1) =
          BinarySuccessorMachine.successor ∘ addBits c := by
        funext q
        simp [addBits, Function.iterate_succ_apply', Function.comp_def]
      rw [heq]
      exact BitMachineComposition.polytime_comp ih
        BinarySuccessorMachine.successor_polytime

inductive Phase
  | start | body
  deriving DecidableEq, Fintype

def prependSpec (b : Bool) : Spec Phase where
  step _ _ _ := .body
  emit s x := match s with
    | .start => [b, x]
    | .body => [x]
  op _ _ := .keep
  fin s := match s with
    | .start => [b]
    | .body => []
  incBy := 0
  bound := 2
  emit_le s x := by cases s <;> simp
  fin_le s := by cases s <;> simp

def prepend (b : Bool) (q : List Bool) : List Bool :=
  (prependSpec b).out .start 0 q

theorem prepend_eq (b : Bool) (q : List Bool) : prepend b q = b :: q := by
  cases q with
  | nil => rfl
  | cons x xs =>
      rw [prepend, Spec.out_cons]
      have hbody : (prependSpec b).out .body 0 xs = xs := by
        induction xs with
        | nil => rfl
        | cons y ys ih =>
            rw [Spec.out_cons]
            simpa [prependSpec, Spec.next] using congrArg (List.cons y) ih
      simpa [prependSpec, Spec.next, hbody]

noncomputable def prependMachine (b : Bool) : BitMachine.Machine :=
  AFront.Transducer.machine (prependSpec b) Phase.start

theorem prepend_outputs (b : Bool) (q : List Bool) :
    (prependMachine b).OutputsWithin q (prepend b q) (4 * (q.length + 1)) :=
  AFront.Transducer.machine_outputs_linear (prependSpec b) Phase.start q

theorem prepend_polytime (b : Bool) : BitMachine.Polytime (prepend b) := by
  exact ⟨prependMachine b, 4, 1, by simpa only [pow_one] using prepend_outputs b⟩

def parity (k : ℕ) : Bool := decide (k % 2 = 1)

def bitsHeader (k : ℕ) (q : List Bool) : List Bool :=
  field (prepend (parity k) (addBits (k / 2) q))

theorem bitsHeader_polytime (k : ℕ) : BitMachine.Polytime (bitsHeader k) := by
  unfold bitsHeader
  have h1 := BitMachineComposition.polytime_comp
    (addBits_polytime (k / 2)) (prepend_polytime (parity k))
  have h2 := BitMachineComposition.polytime_comp h1 SourceFieldWriter.field_polytime
  simpa [Function.comp_def] using h2

theorem parity_toNat (k : ℕ) : (parity k).toNat = k % 2 := by
  have hk : k % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases h : k % 2 = 1
  · simp [parity, h]
  · have h0 : k % 2 = 0 := by omega
    simp [parity, h, h0]

theorem bitsHeader_nat (k B : ℕ) (hk : 0 < k) :
    bitsHeader k B.bits = natField (2 * B + k) := by
  let b := parity k
  let C := B + k / 2
  have hzero : C = 0 → b = true := by
    intro hc
    have hmod := Nat.mod_add_div k 2
    have hpar : b.toNat = k % 2 := parity_toNat k
    cases hb : b with
    | false =>
        simp [hb] at hpar
        omega
    | true => rfl
  have hnum : Nat.bit b C = 2 * B + k := by
    have hmod := Nat.mod_add_div k 2
    have hpar : b.toNat = k % 2 := parity_toNat k
    simp only [Nat.bit_val]
    omega
  simp only [bitsHeader, addBits_nat, prepend_eq, natField]
  rw [← Nat.bits_append_bit C b hzero, hnum]

#print axioms addBits_polytime
#print axioms prepend_polytime
#print axioms bitsHeader_nat
#print axioms bitsHeader_polytime

end Paper2.FixedGapHeader
