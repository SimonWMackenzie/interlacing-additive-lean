import CurrentAdditive.IntegerBitSupport
import CurrentAdditive.EntryAdapter
import CurrentAdditive.CoefficientScale
import CurrentAdditive.CodeDCanonicalSourceV2
import CurrentAdditive.MinimumRatioStepSpec
import CurrentAdditive.RationalCanonical

set_option maxHeartbeats 1000000

/-!
Intermediate arithmetic for the actual Code D rational operations.
The retained-weight result and the cursor-entry result are used separately:
neither is treated as a proof of a complete physical machine clock.
-/

namespace CurrentAdditive.TransientArithmetic

open SequentialCode RationalBitBounds RationalCandidateCompletion
open EliminationEntryBounds

/-- Both canonical rational fields fit the stated binary length. -/
def Fits (b : Nat) (x : ℚ) : Prop :=
  Nat.size x.num.natAbs ≤ b ∧ Nat.size x.den ≤ b

theorem fits_mono {b c : Nat} {x : ℚ} (h : Fits b x) (hbc : b ≤ c) :
    Fits c x := ⟨h.1.trans hbc, h.2.trans hbc⟩

theorem fits_of_representation (x : ℚ) (a : ℤ) (d : Nat)
    (hd : 0 < d) (hx : x = (a : ℚ) / (d : ℚ))
    (b : Nat) (ha : Nat.size a.natAbs ≤ b) (hdb : Nat.size d ≤ b) :
    Fits b x := by
  have hd' : (d : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hh := rat_components_le_of_divInt x a (d : ℤ) hd' (by simpa using hx)
  exact ⟨(Nat.size_le_size hh.1).trans ha,
    (Nat.size_le_size (by simpa using hh.2)).trans hdb⟩

theorem fits_commonDenominator {κ : Type*} {w : κ → ℚ}
    (enc : CommonDenominator w) (b : Nat)
    (hd : Nat.size enc.denominator ≤ b)
    (hn : ∀ i, Nat.size (enc.numerator i).natAbs ≤ b) (i : κ) :
    Fits b (w i) :=
  fits_of_representation (w i) (enc.numerator i) enc.denominator
    enc.positive (enc.represents i) b (hn i) hd

theorem fits_mul {b c : Nat} {x y : ℚ} (hx : Fits b x) (hy : Fits c y) :
    Fits (b + c + 1) (x * y) := by
  have h := components_mul (components_of_bits x b hx.1 hx.2)
    (components_of_bits y c hy.1 hy.2)
  rw [← pow_add] at h
  exact components_fits_bits _ _ h

theorem fits_div {b c : Nat} {x y : ℚ} (hx : Fits b x) (hy : Fits c y)
    (hy0 : y ≠ 0) : Fits (b + c + 1) (x / y) := by
  have h := components_div (components_of_bits x b hx.1 hx.2)
    (components_of_bits y c hy.1 hy.2) hy0
  rw [← pow_add] at h
  exact components_fits_bits _ _ h

theorem fits_sub {b c : Nat} {x y : ℚ} (hx : Fits b x) (hy : Fits c y) :
    Fits (b + c + 2) (x - y) := by
  have h := components_sub (components_of_bits x b hx.1 hx.2)
    (components_of_bits y c hy.1 hy.2)
  have he : 2 * (2 ^ b * 2 ^ c) = 2 ^ (b + c + 1) := by
    rw [pow_succ, pow_add]
    ring
  rw [he] at h
  simpa [Nat.add_assoc] using components_fits_bits _ _ h

/-- These are the unnormalised signed cross-products compared by exact
rational order, before any common factor is cancelled. -/
theorem comparison_cross_products_bits {b c : Nat} {x y : ℚ}
    (hx : Fits b x) (hy : Fits c y) :
    Nat.size (x.num * (y.den : ℤ)).natAbs ≤ b + c + 1 ∧
    Nat.size (y.num * (x.den : ℤ)).natAbs ≤ b + c + 1 := by
  have hxc := components_of_bits x b hx.1 hx.2
  have hyc := components_of_bits y c hy.1 hy.2
  constructor
  · apply size_le_of_pow_bound
    simpa [Int.natAbs_mul, ← pow_add] using Nat.mul_le_mul hxc.1 hyc.2
  · apply size_le_of_pow_bound
    simpa [Int.natAbs_mul, ← pow_add, Nat.add_comm] using
      Nat.mul_le_mul hyc.1 hxc.2

/-- The actual ratio, product, and subtraction appearing in the executable
weight update, including values which are discarded after zero filtering. -/
theorem update_temporaries_bits {b c : Nat} {w wi cj ci : ℚ}
    (hw : Fits b w) (hwi : Fits b wi)
    (hcj : Fits c cj) (hci : Fits c ci) (hcj0 : cj ≠ 0) :
    Fits (b + c + 1) (w / cj) ∧
    Fits (b + 2 * c + 2) ((w / cj) * ci) ∧
    Fits (2 * b + 2 * c + 4) (wi - (w / cj) * ci) := by
  have hr := fits_div hw hcj hcj0
  have hp := fits_mul hr hci
  have hs := fits_sub hwi hp
  refine ⟨hr, ?_, ?_⟩
  · simpa only [show b + c + 1 + c + 1 = b + 2 * c + 2 by omega] using hp
  · simpa only [show b + (b + c + 1 + c + 1) + 2 =
        2 * b + 2 * c + 4 by omega] using hs

theorem minimumRatio_fits (weights coeff : Array ℚ) (b c : Nat)
    (hw : ∀ i : Fin weights.size, Fits b weights[i])
    (hc : ∀ i : Fin coeff.size, Fits c coeff[i])
    (lambda : ℚ) (hmin : minimumRatio weights coeff = some lambda) :
    Fits (b + c + 1) lambda := by
  obtain ⟨j, hj, hpos, hratio⟩ := minimumRatio_attained weights coeff lambda hmin
  have hjw : j < weights.size :=
    (List.mem_range.mp hj).trans_le (Nat.min_le_left _ _)
  have hjc : j < coeff.size :=
    (List.mem_range.mp hj).trans_le (Nat.min_le_right _ _)
  rw [hratio]
  have h0 : coeff[j] ≠ 0 := by simpa [hjc] using ne_of_gt hpos
  simpa [hjw, hjc] using fits_div (hw ⟨j, hjw⟩) (hc ⟨j, hjc⟩) h0

/-- Every cell actually constructed by eliminateWeights has the same
polynomial intermediate bound as the attained minimum ratio. -/
theorem eliminateWeights_temporaries (weights coeff out : Array ℚ)
    (b c : Nat)
    (hw : ∀ i : Fin weights.size, Fits b weights[i])
    (hc : ∀ i : Fin coeff.size, Fits c coeff[i])
    (hsize : coeff.size = weights.size)
    (hout : eliminateWeights weights coeff = some out) :
    ∃ lambda : ℚ,
      minimumRatio weights coeff = some lambda ∧
      Fits (b + c + 1) lambda ∧
      out.size = weights.size ∧
      ∀ i : Fin weights.size,
        Fits (b + 2 * c + 2) (lambda * (coeff[i.val]?.getD 0)) ∧
        Fits (2 * b + 2 * c + 4) (out[i.val]?.getD 0) := by
  cases hmin : minimumRatio weights coeff with
  | none => simp [eliminateWeights, hmin] at hout
  | some lambda =>
      have hl := minimumRatio_fits weights coeff b c hw hc lambda hmin
      have ho := hout
      simp [eliminateWeights, hmin] at ho
      subst out
      refine ⟨lambda, rfl, hl, by simp, ?_⟩
      intro i
      have hic : i.val < coeff.size := by omega
      have hp := fits_mul hl (hc ⟨i.val, hic⟩)
      have hs := fits_sub (hw i) hp
      constructor
      · simpa only [Array.getElem?_eq_getElem hic, Option.getD_some,
          show b + c + 1 + c + 1 = b + 2 * c + 2 by omega] using hp
      · simpa only [Array.getElem?_ofFn, dif_pos i.isLt, Option.getD_some,
          Array.getElem?_eq_getElem hic] using
          (show Fits (2 * b + 2 * c + 4)
            (weights[i] - lambda * coeff[i.val]) from by
              simpa only [show b + (b + c + 1 + c + 1) + 2 =
                2 * b + 2 * c + 4 by omega] using hs)

/-- This adapter consumes the exact squared Hadamard bounds without
weakening their hypotheses or choosing a different rational relation. -/
theorem hadamard_representation_fits (x : ℚ) (a : ℤ) (d r : Nat)
    (hd : 0 < d) (hx : x = (a : ℚ) / (d : ℚ))
    (ha : a.natAbs ^ 2 ≤ r ^ r) (hdb : d ^ 2 ≤ r ^ r) :
    Fits (r * Nat.size (r + 1) + 1) x := by
  have hpow : r ^ r ≤ 2 ^ (r * Nat.size (r + 1)) := by
    calc
      r ^ r ≤ (r + 1) ^ r := Nat.pow_le_pow_left (by omega) _
      _ ≤ (2 ^ Nat.size (r + 1)) ^ r :=
        Nat.pow_le_pow_left (le_of_lt (Nat.lt_size_self _)) _
      _ = 2 ^ (r * Nat.size (r + 1)) := by
        rw [← pow_mul, Nat.mul_comm]
  have ha' : a.natAbs ≤ r ^ r := by nlinarith [ha]
  have hd' : d ≤ r ^ r := by nlinarith [hdb]
  exact fits_of_representation x a d hd hx _
    (size_le_of_pow_bound (ha'.trans hpow))
    (size_le_of_pow_bound (hd'.trans hpow))

/-- Existing reviewed Gram bounds give an unconditional polynomial budget
for the actual materialized relation; no Hadamard normalisation is assumed. -/
theorem certified_materialized_fits (a : Array (Array ℚ))
    (h01 : ∀ i : Fin a.size, ∀ j : Fin (columnCount a),
      SequentialArrayBridge.matrixOfArray a i j = 0 ∨
      SequentialArrayBridge.matrixOfArray a i j = 1)
    (cert : {x : Array ℚ // IsDependence a x})
    (hcert : MaterializedGauss.certifiedMaterializedDependence a = some cert) :
    ∀ i : Fin cert.val.size,
      Fits (4 * a.size * Nat.size (a.size + 1) + 1) cert.val[i] := by
  obtain ⟨d, z, hd, hdb, hz, hsize, hrep⟩ :=
    certified_materialized_shared a h01 cert hcert
  intro i
  let j : Fin (columnCount a) := ⟨i.val, by omega⟩
  apply fits_of_representation cert.val[i] (z j) d hd
  · simpa [j, i.isLt] using hrep j
  · exact shared_gram_bits a.size _ (hz j)
  · exact shared_gram_bits a.size _ hdb

/-- Canonical fields of every retained array in the actual elimination
trace inherit its checked common-denominator budget. -/
theorem traced_weights_fit {α : Type*} (n : Nat) (φ : α → Fin n → ℚ)
    (hn : 0 < n) (hφ : ∀ x j, φ x j = 0 ∨ φ x j = 1)
    (source current : Array (α × ℚ)) (t : Nat)
    (htrace : IntegerBitSupport.EliminationTrace n φ t source current)
    (hpos : SequentialSourceCode.SourcePositive source)
    (hmass : sourceMass source = 1)
    (enc : CommonDenominator (fun i : Fin source.size => source[i].2)) :
    ∀ i : Fin current.size,
      Fits (Nat.size enc.denominator + 4 * t * n * Nat.size (n + 1) + 1)
        current[i].2 := by
  obtain ⟨encOut, hd, hnum⟩ := IntegerBitSupport.eliminationTrace_weight_bits
    n φ hn hφ source current t htrace hpos hmass enc
  intro i
  exact fits_commonDenominator encOut _ hd
    (fun j => (hnum j).trans hd) i

/-- Join the retained-weight theorem to the exact next rational dependence
and the actual eager update, charging all update cells before deletion. -/
theorem traced_actual_elimination_temporaries {α : Type*}
    (n : Nat) (φ : α → Fin n → ℚ)
    (hn : 0 < n) (hφ : ∀ x j, φ x j = 0 ∨ φ x j = 1)
    (source current : Array (α × ℚ)) (t : Nat)
    (htrace : IntegerBitSupport.EliminationTrace n φ t source current)
    (hpos : SequentialSourceCode.SourcePositive source)
    (hmass : sourceMass source = 1)
    (enc : CommonDenominator (fun i : Fin source.size => source[i].2))
    (cert : {x : Array ℚ // IsDependence (featureRows n φ current) x})
    (hcert : MaterializedGauss.certifiedMaterializedDependence
      (featureRows n φ current) = some cert)
    (updated : Array ℚ)
    (hupdate : eliminateWeights (current.map Prod.snd) cert.val = some updated) :
    let b := Nat.size enc.denominator + 4 * t * n * Nat.size (n + 1) + 1
    let c := 4 * n * Nat.size (n + 1) + 1
    ∃ lambda : ℚ,
      minimumRatio (current.map Prod.snd) cert.val = some lambda ∧
      Fits (b + c + 1) lambda ∧
      updated.size = current.size ∧
      ∀ i : Fin current.size,
        Fits (b + 2 * c + 2) (lambda * (cert.val[i.val]?.getD 0)) ∧
        Fits (2 * b + 2 * c + 4) (updated[i.val]?.getD 0) := by
  intro b c
  have hw := traced_weights_fit n φ hn hφ source current t htrace hpos hmass enc
  have h01 := featureRows_zero_one_local n φ current hφ
  have hc := certified_materialized_fits (featureRows n φ current) h01 cert hcert
  have hsize : cert.val.size = (current.map Prod.snd).size := by
    have hs := (dependence_spec _ _).mp cert.property |>.1
    simpa [SequentialCompressionTotality.featureRows_columnCount n φ current hn]
      using hs
  have hw' : ∀ i : Fin (current.map Prod.snd).size,
      Fits b (current.map Prod.snd)[i] := by
    intro i
    simpa [b] using hw ⟨i.val, by simpa using i.isLt⟩
  have hc' : ∀ i : Fin cert.val.size, Fits c cert.val[i] := by
    intro i
    simpa [c, featureRows] using hc i
  obtain ⟨lambda, hl, hlf, hs, hall⟩ := eliminateWeights_temporaries
    (current.map Prod.snd) cert.val updated b c hw' hc' hsize hupdate
  refine ⟨lambda, hl, hlf, by simpa using hs, ?_⟩
  intro i
  simpa using hall ⟨i.val, by simpa using i.isLt⟩

theorem rawOfRat_code_length (x : ℚ) (b : Nat) (hx : Fits b x) :
    (CodeDCodec.encodeRawRat (CodeDCanonicalSourceV2.rawOfRat x)).length ≤
      4 * b + 5 := by
  rw [CodeDCodec.encodeRawRat,
    EthInapproximability.CurrentPaper.BitMachineBankCodec.encode_length]
  have hs : (if x.num < 0 then [true] else ([] : List Bool)).length ≤ 1 := by
    split_ifs <;> simp
  rcases hx with ⟨hn, hd⟩
  simp [CodeDCodec.rawRatBank, CodeDCanonicalSourceV2.rawOfRat,
    Fin.sum_univ_succ, Nat.size_eq_bits_len] at *
  omega

/-- Exact canonical input bytes of the physical ratio/product callback. -/
theorem pairBytes_length (x y : ℚ) (b c : Nat)
    (hx : Fits b x) (hy : Fits c y) :
    (CodeDPairProductTargetV2.pairBytes
      (CodeDCanonicalSourceV2.rawOfRat x)
      (CodeDCanonicalSourceV2.rawOfRat y)).length ≤ 8 * b + 8 * c + 22 := by
  have hxl := rawOfRat_code_length x b hx
  have hyl := rawOfRat_code_length y c hy
  simp only [CodeDPairProductTargetV2.pairBytes,
    EthInapproximability.CurrentPaper.BitMachineBankCodec.encode_length]
  simp [CodeDPairProductTargetV2.pairBank, Fin.sum_univ_succ] at *
  omega

theorem bestPacket_length (best : Option ℚ) (b : Nat)
    (hb : ∀ x ∈ best, Fits b x) :
    (MinimumRatioStepSpec.bestPacket best).length ≤ 4 * b + 6 := by
  cases best with
  | none => simp [MinimumRatioStepSpec.bestPacket]
  | some x =>
      have hx := rawOfRat_code_length x b (hb x (by simp))
      simpa [MinimumRatioStepSpec.bestPacket,
        CodeDCanonicalSource.rawOfRat, CodeDCanonicalSourceV2.rawOfRat] using
        (Nat.add_le_add_left hx 1)

theorem semanticStep_fits (best : Option ℚ) (weight coeff : ℚ)
    (b c r : Nat) (hw : Fits b weight) (hc : Fits c coeff)
    (hbest : ∀ x ∈ best, Fits r x) (hr : b + c + 1 ≤ r) :
    ∀ x ∈ MinimumRatioStepSpec.semanticStep best weight coeff, Fits r x := by
  intro x hx
  unfold MinimumRatioStepSpec.semanticStep at hx
  split_ifs at hx with hp
  · have hratio := fits_mono (fits_div hw hc (ne_of_gt hp)) hr
    cases best with
    | none =>
        have he : x = weight / coeff := by simpa using hx.symm
        rw [he]; exact hratio
    | some old =>
        dsimp only at hx
        split_ifs at hx
        · have he : x = weight / coeff := by simpa using hx.symm
          rw [he]; exact hratio
        · have ho := hbest old (by simp)
          have he : x = old := by simpa using hx.symm
          rw [he]; exact ho
  · exact hbest x hx

/-- Normalisation itself shrinks both literal raw arithmetic fields. -/
theorem normalization_fields_do_not_grow (r : CodeDCodec.RawRat) :
    (BinaryGCDNormalization.normalize r).numerator.length ≤ r.numerator.length ∧
    (BinaryGCDNormalization.normalize r).denominator.length ≤ r.denominator.length :=
  ⟨BinaryGCDNormalization.normalize_numerator_length_le r,
    BinaryGCDNormalization.normalize_denominator_length_le r⟩

/-- The exact integer scaling cancels in the product used by the actual
rational update.  This is the same update as the manuscript's integer formula. -/
theorem actual_ratio_integer_scaling (w ci cj : ℚ) (zi zj : ℤ) (d : Nat)
    (hd : 0 < d) (hci : ci = (zi : ℚ) / (d : ℚ))
    (hcj : cj = (zj : ℚ) / (d : ℚ)) (hzj : zj ≠ 0) :
    (w / cj) * ci = (w / (zj : ℚ)) * (zi : ℚ) := by
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hzjq : (zj : ℚ) ≠ 0 := by exact_mod_cast hzj
  rw [hci, hcj]
  field_simp

/-- Every prefix of the exact semantic ratio scan keeps an attained value
whose canonical packet has a uniform bound. -/
theorem ratio_scan_prefix_fits (items : List (ℚ × ℚ)) (b c : Nat)
    (hitems : ∀ p ∈ items, Fits b p.1 ∧ Fits c p.2)
    (best : Option ℚ)
    (hbest : ∀ x ∈ best, Fits (b + c + 1) x) :
    ∀ x ∈ items.foldl
      (fun prev p => MinimumRatioStepSpec.semanticStep prev p.1 p.2) best,
      Fits (b + c + 1) x := by
  induction items generalizing best with
  | nil => exact hbest
  | cons p rest ih =>
      have hp := hitems p (by simp)
      have hrest : ∀ p ∈ rest, Fits b p.1 ∧ Fits c p.2 := by
        intro p hp; exact hitems p (by simp [hp])
      exact ih hrest _ (semanticStep_fits best p.1 p.2 b c _ hp.1 hp.2 hbest le_rfl)

/-- The actual cursor theorem discharges the cell-size premise at every
scan position; this is not a recurrence which repeatedly squares a bound. -/
theorem actual_cursor_cell_fits {m k : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (t : Nat) (ht : t ≤ k) (i : Fin m) (j : Fin k) :
    Fits ((m + 3) * (m + 1) ^ 2 + 1)
      ((cursorAfter (fun i j => (A i j : ℚ)) t).B i j) := by
  have h := every_actual_step_entry_bits A h01 t ht i j
  exact ⟨h.2, h.1⟩

/-- Every arithmetic expression of every successful actual Gaussian pivot
has a polynomial canonical field bound, uniformly over its scan position. -/
theorem actual_pivot_intermediates_fit {m k : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (t : Nat) (ht : t ≤ k)
    (hr : (cursorAfter (fun i j => (A i j : ℚ)) t).r < m)
    (hc : (cursorAfter (fun i j => (A i j : ℚ)) t).c < k)
    (p : Fin m)
    (hp : SequentialTotality.pivotTyped
      (cursorAfter (fun i j => (A i j : ℚ)) t).B
      (cursorAfter (fun i j => (A i j : ℚ)) t).r
      ⟨(cursorAfter (fun i j => (A i j : ℚ)) t).c, hc⟩ = some p)
    (i : Fin m) (j : Fin k) :
    let state := cursorAfter (fun i j => (A i j : ℚ)) t
    let rf : Fin m := ⟨state.r, hr⟩
    let cf : Fin k := ⟨state.c, hc⟩
    let B := SequentialTotality.swapTyped state.B rf p
    let budget := 4 * ((m + 3) * (m + 1) ^ 2 + 1) + 2
    Fits budget (B rf j / B rf cf) ∧
    Fits budget (B i cf / B rf cf) ∧
    Fits budget ((B i cf / B rf cf) * B rf j) ∧
    Fits budget (B i j - (B i cf / B rf cf) * B rf j) ∧
    Fits budget (SequentialTotality.clearTyped B rf cf i j) := by
  exact actualPivot_temporary_bits A h01 t ht hr hc p hp i j

#print axioms traced_actual_elimination_temporaries
#print axioms hadamard_representation_fits
#print axioms actual_pivot_intermediates_fit
#print axioms normalization_fields_do_not_grow
#print axioms ratio_scan_prefix_fits
#print axioms pairBytes_length
#print axioms actual_ratio_integer_scaling

end CurrentAdditive.TransientArithmetic
