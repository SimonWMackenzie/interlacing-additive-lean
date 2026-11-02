import EthInapproximability.CurrentPaper.SourceGenericPolyEnvelope
import EthInapproximability.CurrentPaper.SourceGenericSourcePipeline

/-!
# The summed source clock `2^(eta n) * (|input|+1)^O(1)` (unit 1, segment 4)

Paper B, locked v8 Section 6 (`thm:paper-sparse-gap-source`) and Appendix B;
CP-SOURCE-EFFECTIVE.

The composed pipeline `SourcePipeline.machine S D B` (one fixed program, fixed by
the cited records; the converter at fixed `(a,q) = (D.alphabet, D.arity)`) runs on
the original CNF bits within `C * ceil(2^(eta*n)) * (|input|+1)^E` steps, where
`n` is the ORIGINAL variable count, for constants `C, E` fixed by `(S, D, B)` before
the formula. The number of branches enters only as the outer factor
`ceil(2^(eta*n))` (from the cited `S.count`), its binary digits only through the
cap `W c n = c*n+1` with `c = ceil eta`; every per-branch cost is a fixed polynomial
envelope in `n <= |input|`. The cited machines' polynomial clocks (`S.runtime`,
`D.polytime`, `B.polytime`) enter through the admitted stage cost lemmas; the
converter's clock `convC * (|constraintBits|+1)^27` is composed with the Dinur
output-length envelope, so the whole clock is in the original formula length.
-/

namespace EthInapproximability.CurrentPaper.SourceGenericComposite.PipelineClock

open EncodedETHSource EncodedCommunication PolyEnvelope

variable {η : ℚ} (S : Sparsification η) (D : DinurReduction)
  (B : BOTReduction (EncodedETHSourceComposition.booleanOccurrence D))

/-! ## Branch count and its digits -/

theorem count_le_ceil (f : ValidFormula) :
    (S.branches f).length ≤ ⌈(2 : ℝ) ^ ((η : ℝ) * f.val.variables)⌉₊ := by
  have h := (S.count f).trans (Nat.le_ceil ((2 : ℝ) ^ ((η : ℝ) * f.val.variables)))
  exact_mod_cast h

theorem one_le_ceil (f : ValidFormula) :
    1 ≤ ⌈(2 : ℝ) ^ ((η : ℝ) * f.val.variables)⌉₊ :=
  Nat.one_le_ceil_iff.mpr (Real.rpow_pos_of_pos (by norm_num) _)

theorem count_le_pow (f : ValidFormula) :
    (S.branches f).length ≤ 2 ^ (⌈η⌉₊ * f.val.variables) := by
  have hη : (η : ℝ) ≤ ((⌈η⌉₊ : ℕ) : ℝ) := by
    have := Nat.le_ceil η
    exact_mod_cast this
  have hexp : (η : ℝ) * f.val.variables ≤ ((⌈η⌉₊ : ℕ) : ℝ) * f.val.variables :=
    mul_le_mul_of_nonneg_right hη (Nat.cast_nonneg _)
  have hmono := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp
  have hcast : (2 : ℝ) ^ (((⌈η⌉₊ : ℕ) : ℝ) * f.val.variables) =
      ((2 ^ (⌈η⌉₊ * f.val.variables) : ℕ) : ℝ) := by
    rw [← Nat.cast_mul, Real.rpow_natCast]
    push_cast
    ring
  have h := (S.count f).trans (hmono.trans hcast.le)
  exact_mod_cast h

theorem digits_le (f : ValidFormula) :
    (S.branches f).length.bits.length ≤ W ⌈η⌉₊ f.val.variables := by
  rw [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  have h := count_le_pow S f
  have : 2 ^ (⌈η⌉₊ * f.val.variables) < 2 ^ (⌈η⌉₊ * f.val.variables + 1) :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  unfold W
  omega

theorem natField_length (b : ℕ) : (natField b).length = 2 * b.bits.length + 1 := by
  simp only [natField, field_length]

/-! ## Per-stage bounds with the branch count factored out -/

theorem sparse_le (f : ValidFormula) :
    SourceOriginalSparsificationMachine.totalTime S f ≤
      ⌈(2 : ℝ) ^ ((η : ℝ) * f.val.variables)⌉₊ * (2 * f.val.variables + 4) +
        S.timeConstant * ⌈(2 : ℝ) ^ ((η : ℝ) * f.val.variables)⌉₊ *
          ((EncodedCNF.encode f.val).length + 1) ^ S.timeExponent := by
  have hK := one_le_ceil (η := η) f
  unfold SourceOriginalSparsificationMachine.totalTime
  rw [SourceOriginalSparsificationMachine.sparseTime_encode]
  have h := Nat.le_mul_of_pos_left (2 * f.val.variables + 4) hK
  omega

theorem packet_item_mono (n w w' L : ℕ) (h : w ≤ w') :
    SourceOriginalListPacketizer.itemEnvelope n w L ≤
      SourceOriginalListPacketizer.itemEnvelope n w' L := by
  unfold SourceOriginalListPacketizer.itemEnvelope
  omega

noncomputable def gP (n : ℕ) : ℕ :=
  (5 * W ⌈η⌉₊ n + 7) +
    SourceOriginalListPacketizer.itemEnvelope n (W ⌈η⌉₊ n) ((8*S.density+3)*n*(n.size+1)) +
    (4 * W ⌈η⌉₊ n + 5) + 5 + 3 * (2*(n+(8*S.density+3)*n*(n.size+1))+3)

theorem packet_le (f : ValidFormula) :
    SourceOriginalCNFPacketizer.envelopeTime S f ≤
      ⌈(2 : ℝ) ^ ((η : ℝ) * f.val.variables)⌉₊ * gP S f.val.variables := by
  have hK := one_le_ceil (η := η) f
  have hb := count_le_ceil S f
  have hw := digits_le S f
  have hbl : SourceOriginalListPacketizer.branchLimit S f =
      (8*S.density+3)*f.val.variables*(f.val.variables.size+1) := rfl
  unfold SourceOriginalCNFPacketizer.envelopeTime gP
  rw [hbl]
  set K := ⌈(2 : ℝ) ^ ((η : ℝ) * f.val.variables)⌉₊
  set b := (S.branches f).length
  set w := b.bits.length
  set Wn := W ⌈η⌉₊ f.val.variables
  set Y := 2*(f.val.variables+(8*S.density+3)*f.val.variables*(f.val.variables.size+1))+3
  set I := SourceOriginalListPacketizer.itemEnvelope f.val.variables w
    ((8*S.density+3)*f.val.variables*(f.val.variables.size+1))
  set I' := SourceOriginalListPacketizer.itemEnvelope f.val.variables Wn
    ((8*S.density+3)*f.val.variables*(f.val.variables.size+1))
  have hI : I ≤ I' := packet_item_mono _ _ _ _ hw
  have p1 : b * I ≤ K * I' := Nat.mul_le_mul hb hI
  have p2 : 3 * b * Y ≤ K * (3 * Y) := by
    have := Nat.mul_le_mul_right (3 * Y) hb
    calc 3 * b * Y = b * (3 * Y) := by ring
      _ ≤ K * (3 * Y) := this
  have p3 : 5 * w + 7 ≤ K * (5 * Wn + 7) :=
    le_trans (by omega) (Nat.le_mul_of_pos_left (5 * Wn + 7) hK)
  have p4 : 4 * w + 5 ≤ K * (4 * Wn + 5) :=
    le_trans (by omega) (Nat.le_mul_of_pos_left (4 * Wn + 5) hK)
  have p5 : 5 ≤ K * 5 := Nat.le_mul_of_pos_left 5 hK
  have e : K * ((5 * Wn + 7) + I' + (4 * Wn + 5) + 5 + 3 * Y) =
      K * (5 * Wn + 7) + K * I' + K * (4 * Wn + 5) + K * 5 + K * (3 * Y) := by ring
  rw [e]
  omega

noncomputable def gM (n : ℕ) : ℕ :=
  (5 * W ⌈η⌉₊ n + 7) + SourceOriginalDinurListMapper.itemEnvelope S D n +
    (4 * W ⌈η⌉₊ n + 7) + 4 * W ⌈η⌉₊ n + (2 * W ⌈η⌉₊ n + 1) +
    SourceOriginalDinurListMapper.framedEnvelope S D n + 9

theorem mapper_le (f : ValidFormula) :
    SourceOriginalDinurPrefixMachine.mapperEnvelope S D f ≤
      ⌈(2 : ℝ) ^ ((η : ℝ) * f.val.variables)⌉₊ * gM S D f.val.variables := by
  have hK := one_le_ceil (η := η) f
  have hb := count_le_ceil S f
  have hw := digits_le S f
  have hnf := natField_length (S.branches f).length
  unfold SourceOriginalDinurPrefixMachine.mapperEnvelope gM
  simp only []
  set K := ⌈(2 : ℝ) ^ ((η : ℝ) * f.val.variables)⌉₊
  set b := (S.branches f).length
  set w := b.bits.length
  set Wn := W ⌈η⌉₊ f.val.variables
  set I := SourceOriginalDinurListMapper.itemEnvelope S D f.val.variables
  set F := SourceOriginalDinurListMapper.framedEnvelope S D f.val.variables
  have p1 : b * I ≤ K * I := Nat.mul_le_mul_right I hb
  have p2 : b * (4 * w + 7) ≤ K * (4 * Wn + 7) := Nat.mul_le_mul hb (by omega)
  have p3 : b * F ≤ K * F := Nat.mul_le_mul_right F hb
  have p4 : 5 * w + 7 ≤ K * (5 * Wn + 7) :=
    le_trans (by omega) (Nat.le_mul_of_pos_left (5 * Wn + 7) hK)
  have p5 : 4 * w ≤ K * (4 * Wn) :=
    le_trans (by omega) (Nat.le_mul_of_pos_left (4 * Wn) hK)
  have p6 : (natField b).length ≤ K * (2 * Wn + 1) :=
    le_trans (by omega) (Nat.le_mul_of_pos_left (2 * Wn + 1) hK)
  have p7 : 9 ≤ K * 9 := Nat.le_mul_of_pos_left 9 hK
  have e : K * ((5 * Wn + 7) + I + (4 * Wn + 7) + 4 * Wn + (2 * Wn + 1) + F + 9) =
      K * (5 * Wn + 7) + K * I + K * (4 * Wn + 7) + K * (4 * Wn) + K * (2 * Wn + 1) +
        K * F + K * 9 := by ring
  rw [e]
  omega

noncomputable def gB (n : ℕ) : ℕ :=
  (5 * W ⌈η⌉₊ n + 7) + BooleanListMapper.itemEnv S D n +
    (4 * W ⌈η⌉₊ n + 7) + 4 * W ⌈η⌉₊ n + (2 * W ⌈η⌉₊ n + 1) +
    BooleanListMapper.framedEnv S D n + 9

theorem bool_le (f : ValidFormula) (hn : 1 ≤ f.val.variables) :
    BooleanListMapper.mapTime D S f ≤
      ⌈(2 : ℝ) ^ ((η : ℝ) * f.val.variables)⌉₊ * gB S D f.val.variables := by
  have hK := one_le_ceil (η := η) f
  have hb := count_le_ceil S f
  have hw := digits_le S f
  have hnf := natField_length (S.branches f).length
  have hm := BooleanListMapper.mapTime_le_count S D f hn
  unfold gB
  set K := ⌈(2 : ℝ) ^ ((η : ℝ) * f.val.variables)⌉₊
  set b := (S.branches f).length
  set w := b.bits.length
  set Wn := W ⌈η⌉₊ f.val.variables
  set I := BooleanListMapper.itemEnv S D f.val.variables
  set F := BooleanListMapper.framedEnv S D f.val.variables
  have p1 : b * I ≤ K * I := Nat.mul_le_mul_right I hb
  have p2 : b * (4 * w + 7) ≤ K * (4 * Wn + 7) := Nat.mul_le_mul hb (by omega)
  have p3 : b * F ≤ K * F := Nat.mul_le_mul_right F hb
  have p4 : 5 * w + 7 ≤ K * (5 * Wn + 7) :=
    le_trans (by omega) (Nat.le_mul_of_pos_left (5 * Wn + 7) hK)
  have p5 : 4 * w ≤ K * (4 * Wn) :=
    le_trans (by omega) (Nat.le_mul_of_pos_left (4 * Wn) hK)
  have p6 : (natField b).length ≤ K * (2 * Wn + 1) :=
    le_trans (by omega) (Nat.le_mul_of_pos_left (2 * Wn + 1) hK)
  have p7 : 9 ≤ K * 9 := Nat.le_mul_of_pos_left 9 hK
  have e : K * ((5 * Wn + 7) + I + (4 * Wn + 7) + 4 * Wn + (2 * Wn + 1) + F + 9) =
      K * (5 * Wn + 7) + K * I + K * (4 * Wn + 7) + K * (4 * Wn) + K * (2 * Wn + 1) +
        K * F + K * 9 := by ring
  rw [e]
  omega

noncomputable def gT (n : ℕ) : ℕ :=
  (5 * W ⌈η⌉₊ n + 7) +
    SourceOriginalBOTCanonicalListMapper.itemEnvelope B n (BooleanListMapper.outEnv S D n) +
    (4 * W ⌈η⌉₊ n + 7) + 4 * W ⌈η⌉₊ n + (2 * W ⌈η⌉₊ n + 1) +
    SourceOriginalBOTCanonicalListMapper.framedEnvelope B n (BooleanListMapper.outEnv S D n) + 9

theorem bot_le (f : ValidFormula) (hn : 1 ≤ f.val.variables) :
    SourceOriginalBOTCanonicalListMapper.mapTime B f.val.variables
        (EncodedETHSourceComposition.booleanBranches S D f) ≤
      ⌈(2 : ℝ) ^ ((η : ℝ) * f.val.variables)⌉₊ * gT S D B f.val.variables := by
  have hK := one_le_ceil (η := η) f
  have hb := count_le_ceil S f
  have hw := digits_le S f
  have hnf := natField_length (S.branches f).length
  have hm := SourceOriginalBOTCanonicalListMapper.mapTime_le_count B f.val.variables
    (BooleanListMapper.outEnv S D f.val.variables)
    (EncodedETHSourceComposition.booleanBranches S D f)
    (BooleanListMapper.boolean_word_le S D f hn)
  have hlen : (EncodedETHSourceComposition.booleanBranches S D f).length =
      (S.branches f).length := by
    simp [EncodedETHSourceComposition.booleanBranches]
  rw [hlen] at hm
  unfold gT
  set K := ⌈(2 : ℝ) ^ ((η : ℝ) * f.val.variables)⌉₊
  set b := (S.branches f).length
  set w := b.bits.length
  set Wn := W ⌈η⌉₊ f.val.variables
  set I := SourceOriginalBOTCanonicalListMapper.itemEnvelope B f.val.variables
    (BooleanListMapper.outEnv S D f.val.variables)
  set F := SourceOriginalBOTCanonicalListMapper.framedEnvelope B f.val.variables
    (BooleanListMapper.outEnv S D f.val.variables)
  have p1 : b * I ≤ K * I := Nat.mul_le_mul_right I hb
  have p2 : b * (4 * w + 7) ≤ K * (4 * Wn + 7) := Nat.mul_le_mul hb (by omega)
  have p3 : b * F ≤ K * F := Nat.mul_le_mul_right F hb
  have p4 : 5 * w + 7 ≤ K * (5 * Wn + 7) :=
    le_trans (by omega) (Nat.le_mul_of_pos_left (5 * Wn + 7) hK)
  have p5 : 4 * w ≤ K * (4 * Wn) :=
    le_trans (by omega) (Nat.le_mul_of_pos_left (4 * Wn) hK)
  have p6 : (natField b).length ≤ K * (2 * Wn + 1) :=
    le_trans (by omega) (Nat.le_mul_of_pos_left (2 * Wn + 1) hK)
  have p7 : 9 ≤ K * 9 := Nat.le_mul_of_pos_left 9 hK
  have e : K * ((5 * Wn + 7) + I + (4 * Wn + 7) + 4 * Wn + (2 * Wn + 1) + F + 9) =
      K * (5 * Wn + 7) + K * I + K * (4 * Wn + 7) + K * (4 * Wn) + K * (2 * Wn + 1) +
        K * F + K * 9 := by ring
  rw [e]
  omega

/-! ## The aggregate per-branch envelope and the summed clock -/

noncomputable def gAll (n : ℕ) : ℕ :=
  (2 * n + 4) + gP S n +
    (6 * (SourceOriginalDinurListMapper.inputEnvelope S n + 1) + 5) + gM S D n +
    (6 * (SourceOriginalDinurListMapper.outputEnvelope S D n + 1) + 4) + gB S D n +
    (6 * (BooleanListMapper.outEnv S D n + 1) + 4) + gT S D B n

theorem gAll_env : PolyEnv (gAll S D B) := by
  have hW := W_env ⌈η⌉₊
  have hP := packetItem_env S ⌈η⌉₊
  have hDi := dinurInput_env S
  have hDo := dinurOutput_env S D
  have hDI := dinurItem_env S D
  have hDF := dinurFramed_env S D
  have hBo := boolOut_env S D
  have hBI := boolItem_env S D
  have hBF := boolFramed_env S D
  have hTI := botItem_env S D B
  have hTF := botFramed_env S D B
  unfold gAll gP gM gB gT
  poly_env

/-- The literal composed clock, with the branch count factored out. -/
theorem totalTime_le_factored (f : ValidFormula) (hn : 1 ≤ f.val.variables) :
    SourcePipeline.totalTime S D B f ≤
      ⌈(2 : ℝ) ^ ((η : ℝ) * f.val.variables)⌉₊ * gAll S D B f.val.variables +
        S.timeConstant * ⌈(2 : ℝ) ^ ((η : ℝ) * f.val.variables)⌉₊ *
          ((EncodedCNF.encode f.val).length + 1) ^ S.timeExponent := by
  have hK := one_le_ceil (η := η) f
  have hb := count_le_ceil S f
  have h1 := SourceOriginalDinurPrefixMachine.totalTime_le_originalEnvelope S D f hn
  have hs := sparse_le S f
  have hp := packet_le S f
  have hmap := mapper_le S D f
  have hol := SourceOriginalDinurListMapper.outputList_length_le S D f hn
  have hbool := bool_le S D f hn
  have hbl := BooleanListMapper.booleanPacketList_length_le S D f hn
  have hbot := bot_le S D B f hn
  unfold SourceOriginalDinurPrefixMachine.originalEnvelope at h1
  unfold SourcePipeline.totalTime SourcePipeline.tailTime gAll
  set K := ⌈(2 : ℝ) ^ ((η : ℝ) * f.val.variables)⌉₊
  set b := (S.branches f).length
  set Di := SourceOriginalDinurListMapper.inputEnvelope S f.val.variables
  set Do := SourceOriginalDinurListMapper.outputEnvelope S D f.val.variables
  set Bo := BooleanListMapper.outEnv S D f.val.variables
  have q1 : 3 * b * (Di + 1) ≤ K * (3 * (Di + 1)) := by
    have := Nat.mul_le_mul_right (3 * (Di + 1)) hb
    calc 3 * b * (Di + 1) = b * (3 * (Di + 1)) := by ring
      _ ≤ K * (3 * (Di + 1)) := this
  have q2 : 3 * b * (Do + 1) ≤ K * (3 * (Do + 1)) := by
    have := Nat.mul_le_mul_right (3 * (Do + 1)) hb
    calc 3 * b * (Do + 1) = b * (3 * (Do + 1)) := by ring
      _ ≤ K * (3 * (Do + 1)) := this
  have q3 : 3 * b * (Bo + 1) ≤ K * (3 * (Bo + 1)) := by
    have := Nat.mul_le_mul_right (3 * (Bo + 1)) hb
    calc 3 * b * (Bo + 1) = b * (3 * (Bo + 1)) := by ring
      _ ≤ K * (3 * (Bo + 1)) := this
  have q4 : 5 ≤ K * 5 := Nat.le_mul_of_pos_left 5 hK
  have q5 : 4 ≤ K * 4 := Nat.le_mul_of_pos_left 4 hK
  have e : K * ((2 * f.val.variables + 4) + gP S f.val.variables + (6 * (Di + 1) + 5) +
      gM S D f.val.variables + (6 * (Do + 1) + 4) + gB S D f.val.variables +
      (6 * (Bo + 1) + 4) + gT S D B f.val.variables) =
      K * (2 * f.val.variables + 4) + K * gP S f.val.variables +
        (2 * (K * (3 * (Di + 1))) + K * 5) + K * gM S D f.val.variables +
        (2 * (K * (3 * (Do + 1))) + K * 4) + K * gB S D f.val.variables +
        (2 * (K * (3 * (Bo + 1))) + K * 4) + K * gT S D B f.val.variables := by ring
  rw [e]
  omega

/-- **Segment 4.** One fixed pipeline program, one summed clock
`C * ceil(2^(eta*n)) * (|input|+1)^E` in the ORIGINAL variable count and the
original formula length, constants fixed by the cited records before `f`. -/
theorem pipeline_clock :
    ∃ C E : ℕ, ∀ f : ValidFormula, 1 ≤ f.val.variables →
      SourcePipeline.totalTime S D B f ≤
        C * ⌈(2 : ℝ) ^ ((η : ℝ) * f.val.variables)⌉₊ *
          ((EncodedCNF.encode f.val).length + 1) ^ E := by
  obtain ⟨CG, EG, hG⟩ := PolyEnv.at_le (gAll_env S D B)
  refine ⟨CG + S.timeConstant, EG + S.timeExponent, fun f hn => ?_⟩
  have hfac := totalTime_le_factored S D B f hn
  have hnX := SourceOriginalVariableCapture.original_n_le_input f.val
  have hg := hG f.val.variables (EncodedCNF.encode f.val).length hnX
  set K := ⌈(2 : ℝ) ^ ((η : ℝ) * f.val.variables)⌉₊
  set X := (EncodedCNF.encode f.val).length + 1
  have hX : 1 ≤ X := by omega
  have h1 : X ^ EG ≤ X ^ (EG + S.timeExponent) := Nat.pow_le_pow_right hX (by omega)
  have h2 : X ^ S.timeExponent ≤ X ^ (EG + S.timeExponent) :=
    Nat.pow_le_pow_right hX (by omega)
  calc SourcePipeline.totalTime S D B f
      ≤ K * gAll S D B f.val.variables + S.timeConstant * K * X ^ S.timeExponent := hfac
    _ ≤ K * (CG * X ^ EG) + S.timeConstant * K * X ^ S.timeExponent :=
        Nat.add_le_add_right (Nat.mul_le_mul_left K hg) _
    _ ≤ K * (CG * X ^ (EG + S.timeExponent)) +
          S.timeConstant * K * X ^ (EG + S.timeExponent) :=
        Nat.add_le_add (Nat.mul_le_mul_left K (Nat.mul_le_mul_left CG h1))
          (Nat.mul_le_mul_left _ h2)
    _ = (CG + S.timeConstant) * K * X ^ (EG + S.timeExponent) := by ring

/-- Segments 1 + 4 on one object: the fixed pipeline outputs the consumer
graph list within the summed clock. -/
theorem pipeline_outputs_clock :
    ∃ C E : ℕ, ∀ f : ValidFormula, 1 ≤ f.val.variables →
      (SourcePipeline.machine S D B).OutputsWithin (EncodedCNF.encode f.val)
        (SourceListEncoding.encode (SourcePipeline.graphPackets S D B f))
        (C * ⌈(2 : ℝ) ^ ((η : ℝ) * f.val.variables)⌉₊ *
          ((EncodedCNF.encode f.val).length + 1) ^ E) := by
  obtain ⟨C, E, h⟩ := pipeline_clock S D B
  exact ⟨C, E, fun f hn => BitMachine.outputsWithin_mono _
    (SourcePipeline.pipeline_sourceGraphs S D B f) (h f hn)⟩

#print axioms count_le_ceil
#print axioms count_le_pow
#print axioms digits_le
#print axioms packet_le
#print axioms mapper_le
#print axioms bool_le
#print axioms bot_le
#print axioms gAll_env
#print axioms totalTime_le_factored
#print axioms pipeline_clock
#print axioms pipeline_outputs_clock

end EthInapproximability.CurrentPaper.SourceGenericComposite.PipelineClock
