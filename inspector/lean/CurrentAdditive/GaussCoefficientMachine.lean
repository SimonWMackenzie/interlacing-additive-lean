import CurrentAdditive.GaussCoefficientPhases
import CurrentAdditive.GaussCertificateWorkList
import CurrentAdditive.GaussZeroOneABIBridge

/-! Ordinary packed-input interface for the charged coefficient controller. -/

namespace CurrentAdditive.GaussCoefficientProgram

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding

def source : Stack := .inl 61
def output : Stack := .inl 38
def start : Label := .parse (.inl (.scan 0))
def control : Control := parseEmbed none

noncomputable def branchMachine : BitMachine.Machine :=
  BitMachineEncoding.ofFinite source output start control program

theorem parser_initial_stack (word : List Bool) :
    (CurrentAdditive.GaussPackedParse64.frame (fun _ => [])
      (BitMachineBankCodec.parserCfg (K := 3) (some (.scan 0)) none
        (fun _ => []) word [] [])).stk =
      fun k : Fin 64 => if k = 61 then word else [] := by
  unfold CurrentAdditive.GaussPackedParse64.frame
  simp only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg]
  let S : Fin 64 → List Bool := fun k => if k = 61 then word else []
  have hlocal : ∀ q : BitMachineBankCodec.Stack 3,
      (BitMachineBankCodec.parserCfg (K := 3) (some (.scan 0)) none
        (fun _ => []) word [] []).stk q =
        S (CurrentAdditive.GaussPackedParse64.locate q) := by
    intro q
    cases q with
    | inl q => fin_cases q <;> simp [S,
        CurrentAdditive.GaussPackedParse64.locate,
        BitMachineBankCodec.parserCfg, BitMachineBankCodec.contents]
    | inr q => fin_cases q <;> simp [S,
        CurrentAdditive.GaussPackedParse64.locate,
        BitMachineBankCodec.parserCfg, BitMachineBankCodec.contents]
  have hb := BitMachineStackEmbedding.bank_eq_self
    CurrentAdditive.GaussPackedParse64.locate S
    (BitMachineBankCodec.parserCfg (K := 3) (some (.scan 0)) none
      (fun _ => []) word [] []).stk hlocal
  have hf : BitMachineStackEmbedding.bank
      CurrentAdditive.GaussPackedParse64.locate
      (fun _ : Fin 64 => [])
      (BitMachineBankCodec.parserCfg (K := 3) (some (.scan 0)) none
        (fun _ => []) word [] []).stk =
      BitMachineStackEmbedding.bank
      CurrentAdditive.GaussPackedParse64.locate S
      (BitMachineBankCodec.parserCfg (K := 3) (some (.scan 0)) none
        (fun _ => []) word [] []).stk := by
    funext k
    classical
    by_cases hk : ∃ q, CurrentAdditive.GaussPackedParse64.locate q = k
    · simp [BitMachineStackEmbedding.bank, hk]
    · have hne : k ≠ (61 : Fin 64) := by
        intro he
        apply hk
        refine ⟨.inr 0, ?_⟩
        change (61 : Fin 64) = k
        exact he.symm
      simp [BitMachineStackEmbedding.bank, hk, S, hne]
  rw [hf]
  exact hb

theorem initial_stack (word : List Bool) :
    initialStack word = fun k : Stack => if k = source then word else [] := by
  funext k
  cases k with
  | inl i =>
      simp [initialStack, source, parser_initial_stack]
  | inr i =>
      rfl

theorem raw_initial (word : List Bool) :
    rawInit source start control word = initial word := by
  simp [rawInit, initial, start, control, initial_stack]

noncomputable def branchClock {m k : Nat} (B : Fin m → Fin k → ℚ)
    (f j : Fin k) : Nat :=
  let bank := CurrentAdditive.GaussCertificateWorkList.workBank B f j
  7 * ((CurrentAdditive.GaussCertificateWorkList.workPacket B f j).length + 1) +
    1 + (2*j.val+2) + (2*f.val+2) + 1 +
    (2 * (max j.val f.val + 2) + 1) + 3 +
    Getter.preparationClock
      (fun i => comparedStack bank j.val f.val (.inl i)) j.val f.val +
    140 * ((CurrentAdditive.GaussPhysical.encodeTypedMatrix B).length + 1)^3 + 1

theorem branch_outputs {m k : Nat} (B : Fin m → Fin k → ℚ)
    (f j : Fin k) (hf : f.val ≤ m) :
    branchMachine.OutputsWithin
      (CurrentAdditive.GaussCertificateWorkList.workPacket B f j)
      (CurrentAdditive.GaussCertificateVectorABI.coefficientPacket
        (-(CurrentAdditive.GaussFirstFreeCandidate.directCandidate B f hf j)))
      (branchClock B f j) := by
  by_cases hlt : j.val < f.val
  · obtain ⟨t, ht, hh, ho⟩ := typed_getter_output B j f hf hlt
    have hbound : t ≤ branchClock B f j := by
      simp only [branchClock,
        CurrentAdditive.GaussCertificateWorkList.workPacket,
        CurrentAdditive.GaussCertificateWorkList.workBank] at ht ⊢
      omega
    apply BitMachineEncoding.outputsWithin_of_raw_run
      source output start control program
      (CurrentAdditive.GaussCertificateWorkList.workPacket B f j)
      (CurrentAdditive.GaussCertificateVectorABI.coefficientPacket
        (-(CurrentAdditive.GaussFirstFreeCandidate.directCandidate B f hf j)))
      t _ hbound
    · simpa [raw_initial, run,
        CurrentAdditive.GaussCertificateWorkList.workPacket,
        CurrentAdditive.GaussCertificateWorkList.workBank] using hh
    · rw [raw_initial]
      simpa [run, CurrentAdditive.GaussCertificateWorkList.workPacket,
        CurrentAdditive.GaussCertificateWorkList.workBank,
        CurrentAdditive.GaussFirstFreeCandidate.directCandidate,
        hlt, CurrentAdditive.GaussCertificateVectorABI.coefficientPacket] using ho
  · obtain ⟨t, ht, hh, ho⟩ := nonless_output
      (CurrentAdditive.GaussCertificateWorkList.workBank B f j)
      j.val f.val (by rfl) (by rfl) hlt
    have hbound : t ≤ branchClock B f j := by
      simp only [branchClock,
        CurrentAdditive.GaussCertificateWorkList.workPacket] at ht ⊢
      omega
    apply BitMachineEncoding.outputsWithin_of_raw_run
      source output start control program
      (CurrentAdditive.GaussCertificateWorkList.workPacket B f j)
      (CurrentAdditive.GaussCertificateVectorABI.coefficientPacket
        (-(CurrentAdditive.GaussFirstFreeCandidate.directCandidate B f hf j)))
      t _ hbound
    · simpa [raw_initial, run,
        CurrentAdditive.GaussCertificateWorkList.workPacket]
        using hh
    · rw [raw_initial]
      change (run t (initial
        (CurrentAdditive.GaussCertificateWorkList.workPacket B f j))).stk
          (.inl 38) = _
      unfold CurrentAdditive.GaussCertificateWorkList.workPacket
      rw [ho]
      by_cases heq : j = f
      · simp [CurrentAdditive.GaussFirstFreeCandidate.directCandidate,
          heq, negOneWord]
      · have hneval : j.val ≠ f.val := by
          intro h
          exact heq (Fin.ext h)
        simp [CurrentAdditive.GaussFirstFreeCandidate.directCandidate,
          hlt, heq, hneval, zeroWord,
          CurrentAdditive.GaussZeroOneABIBridge.zeroWord_eq]

#print axioms branch_outputs

noncomputable def coefficientMachine : BitMachine.Machine :=
  BitMachineComposition.composition branchMachine
    CurrentAdditive.GaussCertificateNegate.machine

noncomputable def coefficientClock {m k : Nat} (B : Fin m → Fin k → ℚ)
    (f j : Fin k) (hf : f.val ≤ m) : Nat :=
  let q := CurrentAdditive.GaussFirstFreeCandidate.directCandidate B f hf j
  let middle := CurrentAdditive.GaussCertificateVectorABI.coefficientPacket (-q)
  branchClock B f j + 2 * middle.length + 2 +
    (7 * (middle.length + 1) + 2 + 2 * (middle.length + 2) + 4)

theorem coefficient_outputs {m k : Nat} (B : Fin m → Fin k → ℚ)
    (f j : Fin k) (hf : f.val ≤ m) :
    coefficientMachine.OutputsWithin
      (CurrentAdditive.GaussCertificateWorkList.workPacket B f j)
      (CurrentAdditive.GaussCertificateVectorABI.coefficientPacket
        (CurrentAdditive.GaussFirstFreeCandidate.directCandidate B f hf j))
      (coefficientClock B f j hf) := by
  let q := CurrentAdditive.GaussFirstFreeCandidate.directCandidate B f hf j
  have ha := branch_outputs B f j hf
  have hb := CurrentAdditive.GaussRationalNegateCanonical.outputs_canonical (-q)
  simpa [coefficientMachine, coefficientClock, q,
    CurrentAdditive.GaussCertificateVectorABI.coefficientPacket] using
    (BitMachineComposition.composition_outputsWithin
      branchMachine CurrentAdditive.GaussCertificateNegate.machine ha hb)

#print axioms coefficient_outputs

theorem middle_length_le_input {m k : Nat} (B : Fin m → Fin k → ℚ)
    (f j : Fin k) (hf : f.val ≤ m) :
    (CurrentAdditive.GaussCertificateVectorABI.coefficientPacket
      (-(CurrentAdditive.GaussFirstFreeCandidate.directCandidate B f hf j))).length ≤
      (CurrentAdditive.GaussCertificateWorkList.workPacket B f j).length + 9 := by
  have hmatrix := BitMachineBankCodec.word_length_le_encode
    (CurrentAdditive.GaussCertificateWorkList.workBank B f j) (0 : Fin 3)
  have hmatrix' : (CurrentAdditive.GaussPhysical.encodeTypedMatrix B).length ≤
      (CurrentAdditive.GaussCertificateWorkList.workPacket B f j).length := by
    simpa [CurrentAdditive.GaussCertificateWorkList.workPacket,
      CurrentAdditive.GaussCertificateWorkList.workBank] using hmatrix
  by_cases hlt : j.val < f.val
  · let i : Fin m := ⟨j.val, by omega⟩
    have hc := CurrentAdditive.GaussCoefficientTyped.cellWord_length_le_matrix
      B i f
    simpa [CurrentAdditive.GaussFirstFreeCandidate.directCandidate,
      hlt, CurrentAdditive.GaussCertificateVectorABI.coefficientPacket]
      using (show
        (CurrentAdditive.CodeDCodec.encodeRawRat
          (CurrentAdditive.GaussPhysical.rawOfRat (B i f))).length ≤
          (CurrentAdditive.GaussCertificateWorkList.workPacket B f j).length + 9
        by omega)
  · by_cases heq : j = f
    · subst j
      have hq :
          -(CurrentAdditive.GaussFirstFreeCandidate.directCandidate B f hf f) =
            (-1 : ℚ) := by
        simp [CurrentAdditive.GaussFirstFreeCandidate.directCandidate]
      rw [hq]
      have hconst :
          (CurrentAdditive.GaussCertificateVectorABI.coefficientPacket (-1)).length ≤
            9 := by
        exact CurrentAdditive.GaussPhysical.rawOfRat_code_length (-1) 1
          (by norm_num) (by norm_num)
      omega
    · have hq :
          -(CurrentAdditive.GaussFirstFreeCandidate.directCandidate B f hf j) =
            (0 : ℚ) := by
        simp [CurrentAdditive.GaussFirstFreeCandidate.directCandidate,
          hlt, heq]
      rw [hq]
      have hconst :
          (CurrentAdditive.GaussCertificateVectorABI.coefficientPacket 0).length ≤
            9 := by
        exact CurrentAdditive.GaussPhysical.rawOfRat_code_length 0 1
          (by norm_num) (by norm_num)
      omega


theorem coefficientClock_le_poly {m k : Nat} (B : Fin m → Fin k → ℚ)
    (f j : Fin k) (hf : f.val ≤ m) :
    coefficientClock B f j hf ≤
      ((CurrentAdditive.GaussCertificateWorkList.workPacket B f j).length + 2)^12 := by
  let n := (CurrentAdditive.GaussCertificateWorkList.workPacket B f j).length
  let matrixLength := (CurrentAdditive.GaussPhysical.encodeTypedMatrix B).length
  let middleLength :=
    (CurrentAdditive.GaussCertificateVectorABI.coefficientPacket
      (-(CurrentAdditive.GaussFirstFreeCandidate.directCandidate B f hf j))).length
  have hm := BitMachineBankCodec.word_length_le_encode
    (CurrentAdditive.GaussCertificateWorkList.workBank B f j) (0 : Fin 3)
  have hj := BitMachineBankCodec.word_length_le_encode
    (CurrentAdditive.GaussCertificateWorkList.workBank B f j) (1 : Fin 3)
  have hfv := BitMachineBankCodec.word_length_le_encode
    (CurrentAdditive.GaussCertificateWorkList.workBank B f j) (2 : Fin 3)
  have hlength : matrixLength ≤ n ∧ j.val ≤ n ∧ f.val ≤ n := by
    simpa [matrixLength, n,
      CurrentAdditive.GaussCertificateWorkList.workPacket,
      CurrentAdditive.GaussCertificateWorkList.workBank] using
        And.intro hm (And.intro hj hfv)
  have hmiddle : middleLength ≤ n + 9 := by
    simpa [middleLength, n] using middle_length_le_input B f j hf
  have hpre := compared_preparation_clock
    (CurrentAdditive.GaussCertificateWorkList.workBank B f j)
      j.val f.val
  have hcube : (matrixLength + 1)^3 ≤ (n+1)^3 :=
    Nat.pow_le_pow_left (by omega) 3
  have hlin : n+1 ≤ (n+1)^3 := by
    have h1 : 1 ≤ n+1 := by omega
    nlinarith [sq_nonneg (n : ℤ)]
  have hcoeff : coefficientClock B f j hf ≤ 400*(n+1)^3 := by
    unfold coefficientClock branchClock
    dsimp only
    rw [hpre]
    dsimp [n, matrixLength, middleLength] at *
    omega
  have hbudget : 400*(n+1)^3 ≤ (n+2)^12 := by
    have h9 : 400 ≤ (n+2)^9 := by
      calc 400 ≤ 512 := by omega
        _ = 2^9 := by norm_num
        _ ≤ (n+2)^9 := Nat.pow_le_pow_left (by omega) 9
    have h3 : (n+1)^3 ≤ (n+2)^3 :=
      Nat.pow_le_pow_left (by omega) 3
    have hmul := Nat.mul_le_mul h9 h3
    calc
      400*(n+1)^3 ≤ (n+2)^9 * (n+2)^3 := hmul
      _ = (n+2)^12 := by ring
  exact hcoeff.trans hbudget

end CurrentAdditive.GaussCoefficientProgram
