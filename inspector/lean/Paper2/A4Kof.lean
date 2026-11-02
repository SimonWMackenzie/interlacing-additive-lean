import Paper2.A4FrontUniform
import Paper2.A4KofLoops
import Paper2.A4DivFloor
import EthInapproximability.CurrentPaper.ExactParameterMachineSquare
import EthInapproximability.CurrentPaper.SourceOriginalVariableCapture

/-!
# Unit 4 (Paper A), N-4 (1b): the growing-`k` front — `kOf N` computed physically

Owner lane `owner:a-unit4-shell-4` (private, 26 September 2026).

T24's gap is `k = kOf N = ⌊N / ⌈log₂ N⌉²⌋` (`Asymptotics.kOf`, admitted `A4Asymptotics`), with
`N = Φ.val.variables`. This module builds ONE fixed machine `KMachine` that computes the unary
`1^(kOf N)` from the literal word `encode f`, with the admitted unary arithmetic:

1. `SourceOriginalVariableCapture.machine`: `encode f ↦ 1^N` (admitted, `canonical_outputs`);
2. `KofLoops.WrapDup.machine`: `1^N ↦ field (1^N) ++ field (1^N) ++ [false ×4]`;
3. `PairMap.machine LogSq` where `LogSq = composition ExactParameterMachineLog.machine
   ExactParameterMachineSquare.squareMachine` (admitted; `1^N ↦ 1^(⌈log₂N⌉) ↦ 1^(⌈log₂N⌉²)`),
   applied to the first field, the rest kept;
4. `KofLoops.Swap.machine`: the word is now exactly the admitted six-bank packet
   `ExactParameterMachineSecondOrder.packedInput N (⌈log₂N⌉²)`;
5. `DivFloor.machine` (admitted `MatrixUnaryDivision.program` in the admitted
   `BitMachineBankWrapper`, then the admitted `BankFieldProjection.machine 4`): `1^(N / ⌈log₂N⌉²)`.

Then `KFront`: `pair (encode f) tb ↦ pair (encode f) (pair (1^(kOf N)) tb)` (DupField, PairMap of
`KMachine`, Swap), and the T24 front `composition KFront FU` with the `k`-uniform front `FU` of
`R4FrontUniform`. Every handoff is charged by `composition_outputsWithin`; every clock is
explicit or polynomial in the input length. **No ledger row is closed.**
-/

namespace Paper2.Unit4Shell.KofFront

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2.Unit4Shell.Poly
open Paper2.Unit4Shell.T10Finite
open Paper2.Unit4Shell.KofLoops

/-- `1^N ↦ 1^(⌈log₂N⌉²)`. -/
noncomputable def logSq : BitMachine.Machine :=
  BitMachineComposition.composition ExactParameterMachineLog.machine
    ExactParameterMachineSquare.squareMachine

/-- THE fixed machine `encode f ↦ 1^(kOf f.variables)`. -/
noncomputable def KMachine : BitMachine.Machine :=
  BitMachineComposition.composition SourceOriginalVariableCapture.machine
    (BitMachineComposition.composition WrapDup.machine
      (BitMachineComposition.composition (PairMap.machine logSq)
        (BitMachineComposition.composition Swap.machine DivFloor.machine)))

/-- The explicit constant of the `KMachine` clock. -/
noncomputable def BK : ℕ := UnaryBinaryEncoding.coefficient + 2000

theorem clog_le_self (N : ℕ) : Nat.clog 2 N ≤ N :=
  Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le

theorem logSq_outputs (N : ℕ) :
    logSq.OutputsWithin (List.replicate N true) (List.replicate (Nat.clog 2 N ^ 2) true)
      ((UnaryBinaryEncoding.coefficient + 6) * (N + 1) ^ 2 + 2 * Nat.clog 2 N + 2 +
        (2 * Nat.clog 2 N + 2 + 2 * (2 * Nat.clog 2 N + 1) + 2 +
          2 * (2 * Nat.clog 2 N + 2) ^ 2)) := by
  have h := BitMachineComposition.composition_outputsWithin ExactParameterMachineLog.machine
    ExactParameterMachineSquare.squareMachine (ExactParameterMachineLog.outputs N)
    (ExactParameterMachineSquare.square_outputs (Nat.clog 2 N))
  simpa only [logSq, List.length_replicate] using h

/-- **`kOf N` computed physically.** For every CNF `f` (valid or not), the fixed machine
`KMachine` prints exactly `1^(kOf f.variables)` from `encode f` within `BK·(N+1)²`. -/
theorem KMachine_outputs (f : EncodedCNF.Formula) :
    KMachine.OutputsWithin (EncodedCNF.encode f)
      (List.replicate (Asymptotics.kOf f.variables) true) (BK * (f.variables + 1) ^ 2) := by
  set N := f.variables with hNdef
  set C := Nat.clog 2 N with hCdef
  set Q := C ^ 2 with hQdef
  set F4 : List Bool := [false, false, false, false] with hF4
  have h1 := SourceOriginalVariableCapture.canonical_outputs f
  have h2 := WrapDup.machine_outputs N
  have hout : WrapDup.out N = EncodedComplexity.pair (List.replicate N true)
      (EncodedComplexity.pair (List.replicate N true) F4) := by
    simp [WrapDup.out, EncodedComplexity.pair, hF4]
  rw [hout] at h2
  have h3 := PairMap.machine_outputs (M := logSq) (List.replicate N true)
    (List.replicate Q true) (EncodedComplexity.pair (List.replicate N true) F4) _
    (logSq_outputs N)
  have h4 := Swap.machine_outputs (List.replicate Q true) (List.replicate N true) F4
  rw [← DivFloor.packedInput_eq N Q] at h4
  have h5 := DivFloor.outputs N Q
  have hk : N / Q = Asymptotics.kOf N := rfl
  rw [hk] at h5
  have hC := BitMachineComposition.composition_outputsWithin _ _ h1
    (BitMachineComposition.composition_outputsWithin _ _ h2
      (BitMachineComposition.composition_outputsWithin _ _ h3
        (BitMachineComposition.composition_outputsWithin _ _ h4 h5)))
  apply BitMachine.outputsWithin_mono _ hC
  have hin := DivFloor.packedInput_length N Q
  rw [hin]
  simp only [List.length_replicate, EncodedComplexity.pair_length, hF4, List.length_cons,
    List.length_nil]
  have hCN : C ≤ N := clog_le_self N
  have hQN : Q ≤ (N + 1) ^ 2 := by
    rw [hQdef]; exact Nat.pow_le_pow_left (by omega) 2
  have h22 : (2 * C + 2) ^ 2 ≤ 4 * (N + 1) ^ 2 := by
    have : 2 * C + 2 ≤ 2 * (N + 1) := by omega
    calc (2 * C + 2) ^ 2 ≤ (2 * (N + 1)) ^ 2 := Nat.pow_le_pow_left this 2
      _ = 4 * (N + 1) ^ 2 := by ring
  have hN1 : N + 1 ≤ (N + 1) ^ 2 := by nlinarith
  unfold BK
  nlinarith

/-- THE fixed front machine `pair (encode f) tb ↦ pair (encode f) (pair (1^(kOf N)) tb)`. -/
noncomputable def KFront : BitMachine.Machine :=
  BitMachineComposition.composition DupField.machine
    (BitMachineComposition.composition (PairMap.machine KMachine) Swap.machine)

theorem KFront_outputs (f : EncodedCNF.Formula) (tb : List Bool) :
    KFront.OutputsWithin (EncodedComplexity.pair (EncodedCNF.encode f) tb)
      (EncodedComplexity.pair (EncodedCNF.encode f)
        (EncodedComplexity.pair (List.replicate (Asymptotics.kOf f.variables) true) tb))
      ((BK + 100) * ((EncodedComplexity.pair (EncodedCNF.encode f) tb).length + 1) ^ 2) := by
  set E := EncodedCNF.encode f with hE
  set N := f.variables with hNdef
  set k := Asymptotics.kOf N with hkdef
  have h6 := DupField.machine_outputs E tb
  have h7 := PairMap.machine_outputs (M := KMachine) E (List.replicate k true)
    (EncodedComplexity.pair E tb) _ (KMachine_outputs f)
  have h8 := Swap.machine_outputs (List.replicate k true) E tb
  have hC := BitMachineComposition.composition_outputsWithin _ _ h6
    (BitMachineComposition.composition_outputsWithin _ _ h7 h8)
  apply BitMachine.outputsWithin_mono _ hC
  have hNE : N ≤ E.length := SourceOriginalVariableCapture.original_n_le_input f
  have hkN : k ≤ N := Nat.div_le_self _ _
  simp only [List.length_replicate, EncodedComplexity.pair_length]
  set X := 2 * E.length + 1 + tb.length with hX
  have hNX : N + 1 ≤ X + 1 := by omega
  have hpow : (N + 1) ^ 2 ≤ (X + 1) ^ 2 := Nat.pow_le_pow_left hNX 2
  have hBK : BK * (N + 1) ^ 2 ≤ BK * (X + 1) ^ 2 := Nat.mul_le_mul_left _ hpow
  have hX1 : X + 1 ≤ (X + 1) ^ 2 := by nlinarith
  nlinarith

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- **Raw-suffix T24 front.** ONE fixed machine; for every valid `Φ` and every raw suffix `tb`:
`pair (encode Φ) tb ↦ encode ![encode (t10Graph D B Φ), 1^(kOf N), tb]`, `N = Φ.val.variables`,
within `CF·(|input|+1)^EF`. Does not close a ledger row. -/
theorem front_T24_raw :
    ∃ (MF : BitMachine.Machine) (CF EF : ℕ), ∀ (Φ : ValidFormula) (tb : List Bool),
      MF.OutputsWithin (EncodedComplexity.pair (EncodedCNF.encode Φ.val) tb)
        (BitMachineBankCodec.encode ![EncodedGraph.encode (t10Graph D B Φ),
          List.replicate (Asymptotics.kOf Φ.val.variables) true, tb])
        (CF * ((EncodedComplexity.pair (EncodedCNF.encode Φ.val) tb).length + 1) ^ EF) := by
  obtain ⟨MU, CU, EU, hMU⟩ := FrontUniform.front_uniform_raw D B
  let mid : ValidFormula × List Bool → List Bool := fun p =>
    EncodedComplexity.pair (EncodedCNF.encode p.1.val)
      (EncodedComplexity.pair (List.replicate (Asymptotics.kOf p.1.val.variables) true) p.2)
  let total : ValidFormula × List Bool → ℕ := fun p =>
    (BK + 100) * (T10Front.X p + 1) ^ 2 + 2 * (mid p).length + 2 +
      CU * ((mid p).length + 1) ^ EU
  have hmid : PolyIn T10Front.X (fun p => (mid p).length) := by
    refine mono (fun p => ?_) (mul (const 3) self)
    have hNE := SourceOriginalVariableCapture.original_n_le_input p.1.val
    have hkN : Asymptotics.kOf p.1.val.variables ≤ p.1.val.variables := Nat.div_le_self _ _
    simp only [mid, T10Front.X, EncodedComplexity.pair_length, List.length_replicate]
    omega
  have htotal : PolyIn T10Front.X total :=
    add (add (add (mul (const _) (pow (add self (const 1)) 2)) (mul (const 2) hmid)) (const 2))
      (mul (const _) (pow (add hmid (const 1)) EU))
  obtain ⟨CF, EF, hCF⟩ := htotal
  refine ⟨BitMachineComposition.composition KFront MU, CF, EF, fun Φ tb => ?_⟩
  have h1 := KFront_outputs Φ.val tb
  have h2 := hMU (Asymptotics.kOf Φ.val.variables) Φ tb
  have hC := BitMachineComposition.composition_outputsWithin _ _ h1 h2
  apply BitMachine.outputsWithin_mono _ hC
  exact hCF (Φ, tb)

/-- NEW interface: the T24 (growing-`k`) front at `k = kOf N`, on the selected tapes. -/
def H_T10FrontT24 : Prop :=
  ∃ (MF : BitMachine.Machine) (CF EF : ℕ), ∀ (Φ : ValidFormula)
    (t : (TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
      (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
      B.degreeBound (sourceGap D B) (Asymptotics.kOf Φ.val.variables)).Tape),
    MF.OutputsWithin
      (EncodedComplexity.pair (EncodedCNF.encode Φ.val)
        ((TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
          (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
          B.degreeBound (sourceGap D B) (Asymptotics.kOf Φ.val.variables)).tapeBits t))
      (BitMachineBankCodec.encode ![EncodedGraph.encode (t10Graph D B Φ),
        List.replicate (Asymptotics.kOf Φ.val.variables) true,
        (TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
          (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
          B.degreeBound (sourceGap D B) (Asymptotics.kOf Φ.val.variables)).tapeBits t])
      (CF * ((EncodedComplexity.pair (EncodedCNF.encode Φ.val)
        ((TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
          (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
          B.degreeBound (sourceGap D B) (Asymptotics.kOf Φ.val.variables)).tapeBits t)).length
          + 1) ^ EF)

theorem H_T10FrontT24_holds : H_T10FrontT24 D B := by
  obtain ⟨MF, CF, EF, h⟩ := front_T24_raw D B
  exact ⟨MF, CF, EF, fun Φ t => h Φ _⟩

/-- **T24 reduction machine (HYP on H-A3 only).** ONE fixed machine: on `pair (encode Φ)
(tapeBits t)` for every valid `Φ` with `1 ≤ kOf N` and every tape of the selected law at
`k = kOf N`, it prints exactly `outputBits … (kOf N) t` within
`(C0 + CA·CS^(EA·(kOf N+1)))·(|input|+1)^(E0 + ES·(EA·(kOf N+1)))`; all constants absolute. The
gap `kOf N` is COMPUTED by the machine (`KMachine`), not supplied. Does not close a ledger row
(T24, T23). -/
theorem T24_machine (hA3 : Shells.H_A3 B.degreeBound (sourceGap D B)) :
    ∃ (M : BitMachine.Machine) (C0 CA CS E0 ES EA : ℕ), ∀ (Φ : ValidFormula),
      1 ≤ Asymptotics.kOf Φ.val.variables →
      ∀ (t : (TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
        (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
        B.degreeBound (sourceGap D B) (Asymptotics.kOf Φ.val.variables)).Tape),
      M.OutputsWithin
        (EncodedComplexity.pair (EncodedCNF.encode Φ.val)
          ((TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
            (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
            B.degreeBound (sourceGap D B) (Asymptotics.kOf Φ.val.variables)).tapeBits t))
        (EncodedSelectedOutput.outputBits (t10_vertices_pos D B Φ)
          (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
          B.degreeBound (sourceGap D B) (Asymptotics.kOf Φ.val.variables) t)
        ((C0 + CA * CS ^ (EA * (Asymptotics.kOf Φ.val.variables + 1))) *
          ((EncodedComplexity.pair (EncodedCNF.encode Φ.val)
            ((TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
              (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
              B.degreeBound (sourceGap D B)
                (Asymptotics.kOf Φ.val.variables)).tapeBits t)).length + 1) ^
            (E0 + ES * (EA * (Asymptotics.kOf Φ.val.variables + 1)))) := by
  obtain ⟨MA, CA, EA, hMA⟩ := hA3
  obtain ⟨MF, CF, EF, hMF⟩ := H_T10FrontT24_holds D B
  obtain ⟨CS, ES, hS⟩ := T10Size.H_T10Size_holds D B
  refine ⟨BitMachineComposition.composition MF MA, CF + 2 * (1 + CF * MF.pushBound) + 2,
    CA, CS, EF + 1, ES, EA, fun Φ hk t => ?_⟩
  obtain ⟨hm, _, hinc, hdeg, _, _, _⟩ := t10_source D B Φ
  have hF := hMF Φ t
  have hA := hMA (t10Graph D B Φ) (t10Graph_valid D B Φ) (t10_vertices_pos D B Φ)
    (Asymptotics.kOf Φ.val.variables) hk hinc hdeg t
  have hC := BitMachineComposition.composition_outputsWithin MF MA hF hA
  apply BitMachine.outputsWithin_mono _ hC
  have hb := FrontUniform.budgetU _ _ _ _ CF EF MF.pushBound CA CS ES EA
    (Asymptotics.kOf Φ.val.variables)
    (by simp only [EncodedComplexity.pair_length]; omega)
    (BitMachine.output_length_bound MF hF) (hS Φ)
  have he : EF + ES * (EA * (Asymptotics.kOf Φ.val.variables + 1)) + 1 =
      EF + 1 + ES * (EA * (Asymptotics.kOf Φ.val.variables + 1)) := by ring
  rw [he] at hb
  exact hb

#print axioms clog_le_self
#print axioms logSq_outputs
#print axioms KMachine_outputs
#print axioms KFront_outputs
#print axioms front_T24_raw
#print axioms H_T10FrontT24_holds
#print axioms T24_machine

end Paper2.Unit4Shell.KofFront
