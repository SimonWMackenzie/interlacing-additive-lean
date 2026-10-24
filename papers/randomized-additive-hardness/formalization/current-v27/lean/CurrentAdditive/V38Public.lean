import CurrentAdditive.V38Field
import CurrentAdditive.SmallBiasPublicDegree

/-!
# Public v38 field degree and concrete printed array

The selected appendix uses `n=2^b(2^t)^2` and `r=4(b+3t)`. This file
selects a field degree and irreducible modulus from those public parameters,
then identifies the returned list cells with the one matrix in the checked
YES/NO theorem. The polynomial bit-operation clock is a separate obligation.
-/

namespace CurrentAdditive.SmallBias

open Paper2.Yao Paper2.YaoLookup Workspace.Types.Protocol
open CurrentAdditive.FiniteFieldConstructor
open CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge

def v38PositionCount (b t : ℕ) : ℕ :=
  2 ^ b * (2 ^ t * 2 ^ t)

def v38ErrorExponent (b t : ℕ) : ℕ := 4 * (b + 3 * t)

def v38FieldTarget (b t : ℕ) : ℕ :=
  v38PositionCount b t * 2 ^ v38ErrorExponent b t

def v38FieldDegree (b t : ℕ) : ℕ :=
  Nat.clog 2 (v38FieldTarget b t)

theorem v38FieldTarget_gt_one (b t : ℕ) (ht : 4 ≤ t) :
    1 < v38FieldTarget b t := by
  have hpow : 2 ≤ 2 ^ t := by
    have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
      (by omega : 1 ≤ t)
    norm_num at hp
    exact hp
  dsimp [v38FieldTarget, v38PositionCount, v38ErrorExponent]
  have hb : 1 ≤ 2 ^ b := Nat.one_le_pow b 2 (by decide)
  have he : 1 ≤ 2 ^ (4 * (b + 3 * t)) :=
    Nat.one_le_pow _ 2 (by decide)
  have hother : 1 ≤ 2 ^ b * 2 ^ (4 * (b + 3 * t)) := by nlinarith
  have hmid : 1 < 2 ^ t * 2 ^ t := by nlinarith
  have hmul := Nat.mul_le_mul_right (2 ^ t * 2 ^ t) hother
  nlinarith

theorem v38FieldDegree_pos (b t : ℕ) (ht : 4 ≤ t) :
    0 < v38FieldDegree b t :=
  Nat.clog_pos (by decide) (v38FieldTarget_gt_one b t ht)

theorem v38FieldDegree_lower (b t : ℕ) :
    v38FieldTarget b t ≤ 2 ^ v38FieldDegree b t :=
  Nat.le_pow_clog (by decide) _

theorem v38FieldDegree_upper (b t : ℕ) (ht : 4 ≤ t) :
    2 ^ v38FieldDegree b t < 2 * v38FieldTarget b t := by
  have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < (2 : ℕ))
    (v38FieldTarget_gt_one b t ht)
  have hd := v38FieldDegree_pos b t ht
  have he : v38FieldDegree b t - 1 + 1 = v38FieldDegree b t := by omega
  have hpow : 2 ^ v38FieldDegree b t =
      2 * 2 ^ (v38FieldDegree b t - 1) := by
    calc
      _ = 2 ^ (v38FieldDegree b t - 1 + 1) := by rw [he]
      _ = 2 * 2 ^ (v38FieldDegree b t - 1) := by rw [pow_succ]; omega
  rw [hpow]
  exact Nat.mul_lt_mul_of_pos_left hp (by omega)

theorem v38FieldDegree_bias (b t : ℕ) :
    ((v38PositionCount b t : ℕ) : ℚ) / v38ArrayBiasQ b t ≤
      (2 ^ v38FieldDegree b t : ℚ) := by
  have hNat := v38FieldDegree_lower b t
  have heq : ((v38PositionCount b t : ℕ) : ℚ) / v38ArrayBiasQ b t =
      (v38FieldTarget b t : ℚ) := by
    simp only [v38FieldTarget, v38ArrayBiasQ, v38ErrorExponent]
    push_cast
    simp [div_eq_mul_inv]
  rw [heq]
  exact_mod_cast hNat

/-- The physical printer's row-major pair label and selected bit are
literally the labels and bit of `v38PrintedPairWord`. -/
theorem v38_streaming_list_matches_pair_array
    (b t d modulus : ℕ)
    (ℓ : Fin ((2 ^ d) ^ 2))
    (j : Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t)) :
    let xy := (printerPairLabel d).symm ℓ
    let k := (finProdFinEquiv j).val
    (StreamingPrinter.labelledWords d modulus (v38PositionCount b t))[ℓ.val]? =
      some (xy.1.val, xy.2.val,
        StreamingPrinter.word d modulus (v38PositionCount b t)
          xy.1.val xy.2.val) ∧
    (StreamingPrinter.word d modulus (v38PositionCount b t)
        xy.1.val xy.2.val)[k]? =
      some (v38PrintedPairWord b t d modulus ℓ j) := by
  dsimp only
  let xy := (printerPairLabel d).symm ℓ
  let k := (finProdFinEquiv j).val
  have hlabel : printerPairLabel d xy = ℓ :=
    (printerPairLabel d).apply_symm_apply ℓ
  constructor
  · simpa only [hlabel] using
      (streaming_labelledWords_getElem? d modulus
        (v38PositionCount b t) xy.1 xy.2)
  · simpa only [k, v38PrintedPairWord, xy, v38PositionCount] using
      (streaming_word_getElem? d modulus _ xy.1 xy.2
        (finProdFinEquiv j))

/-- A single executable list and a single literal v38 matrix carry both
YES and NO implications. The modulus and list are selected from public
`b,t`, independently of the source promise. -/
theorem v38_public_printed_matrix_yes_no
    {V E : Type*} [Fintype V]
    (b t : ℕ) (ht : 4 ≤ t)
    (edges : E → Fin (2 ^ t * 2 ^ t) ↪ V)
    (index : E ↪ Fin (2 ^ b)) :
    ∃ output : List (ℕ × ℕ × List Bool), ∃ modulus : ℕ,
      TrialSearch.makeList (v38FieldDegree b t)
        (v38PositionCount b t) = some output ∧
      TrialSearch.firstPassing (v38FieldDegree b t) = some modulus ∧
      output = StreamingPrinter.labelledWords (v38FieldDegree b t)
        modulus (v38PositionCount b t) ∧
      (let M := matrixV38 (placeEdges edges index)
          (fullSelector (2 ^ (t - 1)) (2 ^ b))
          (v38PrintedPairWord b t (v38FieldDegree b t) modulus)
       (∀ colour : V → Fin (2 ^ t),
         (∀ e c, 2 ^ t - 1 ≤
           colourFiberCard (fun i => colour (edges e i)) c) →
         Dalt .alice M ≤ 2 * b + 4 * t + 2) ∧
       ((∀ colour : V → Fin (2 ^ (2 ^ t)),
         ∃ e c, ∀ i, colour (edges e i) = c) →
         (2 * b + 4 * t + 2) + 2 * t - 8 ≤ Dalt .alice M)) := by
  let d := v38FieldDegree b t
  obtain ⟨modulus, hfound⟩ :=
    TrialSearch.firstPassing_total d (v38FieldDegree_pos b t ht)
  have hirr := TrialSearch.firstPassing_correct (v38FieldDegree_pos b t ht) hfound
  obtain ⟨tail, htail, hcandidate⟩ := TrialSearch.firstPassing_is_candidate hfound
  have hlt : modulus < 2 ^ (d + 1) := by
    rw [hcandidate]
    exact monicBits_lt _ tail htail
  have htop : modulus.testBit d = true := by
    rw [hcandidate]
    exact monicBits_topBit _ tail htail
  have hmonic : (polynomial (d + 1) modulus).Monic := by
    rw [hcandidate]
    exact monicBits_monic _ tail htail
  have hdegree : (polynomial (d + 1) modulus).natDegree = d := by
    rw [hcandidate]
    exact monicBits_degree _ tail htail
  letI : Fact (Irreducible (polynomial (d + 1) modulus)) := ⟨hirr⟩
  obtain ⟨output, houtput⟩ := TrialSearch.makeList_total d
    (v38PositionCount b t) (v38FieldDegree_pos b t ht)
  have hout : output = StreamingPrinter.labelledWords d modulus
      (v38PositionCount b t) := by
    unfold TrialSearch.makeList at houtput
    simp only [hfound, Option.map_some, Option.some.injEq] at houtput
    exact houtput.symm
  refine ⟨output, modulus, houtput, hfound, hout, ?_⟩
  exact v38_concrete_matrix_yes_no b t d modulus ht
    (v38FieldDegree_pos b t ht) hlt htop hmonic hdegree
    (by simpa only [v38PositionCount] using v38FieldDegree_bias b t)
    edges index

#print axioms CurrentAdditive.SmallBias.v38FieldDegree_bias
#print axioms CurrentAdditive.SmallBias.v38_streaming_list_matches_pair_array
#print axioms CurrentAdditive.SmallBias.v38_public_printed_matrix_yes_no

end CurrentAdditive.SmallBias
