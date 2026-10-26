import Paper2.CmpRun
import Paper2.MedPoly

/-!
# WP-U18a (ii), segment M2 (part 4): the comparator meets `CmpSpec`; the median algorithm with no
comparator premise

Lane `owner:a-cmp-1` (private, 27 September 2026). Paper A, lock v12, I:73-76 (footnote: polynomial
comparison with binary rationals), I:117-125 ("Accept the source exactly when its estimate is below
B+k/2"). Decisions: D-A1 (lane a-model's `PrefixAlgorithm`), D-A3 (ii) (lane a-model's codec
`Paper2.AModel.encodeDyadic z j = encodeInteger z ++ natField j`, parser `readDyadic`, decoder
`decodeDyadic`, reused by exact name).

**Threshold format (this lane's choice, recorded for WP-U18b).** The median machine's input `w`
carries the threshold numerator `m` as its leading self-delimiting field: `thrW w = val(lead w) / 2`,
and `thrW (natField m ++ rest) = m / 2` (`thrW_natField`). With `m = 2B + k` this is `B + k/2`
(`thrW_midpoint`). Words `w` with no complete leading field give the value of the greedily decoded
payload bits (still a total, explicit function; `CmpSpec` holds for every `w`).
-/

set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

namespace Paper2.CmpOwner

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachine
open EthInapproximability.CurrentPaper.EncodedCommunication (field readField bitsValue natField
  readNat readField_append)
open EthInapproximability.CurrentPaper.EncodedComplexity (pair)
open Paper2.MedianOwner Paper2.MedianOwner.Med Paper2.MedianOwner.Final
open Paper2.AModel (PrefixAlgorithm)

/-! ## Arithmetic of the printed bit -/

theorem lastOr_some_ne_none : ∀ (b : Bool) (bs : List Bool), lastOr (some b) bs ≠ none
  | b, [] => by simp [lastOr]
  | _, c :: bs => by simpa [lastOr] using lastOr_some_ne_none c bs

theorem lastOr_eq_none_iff (bs : List Bool) : lastOr none bs = none ↔ bs = [] := by
  cases bs with
  | nil => simp [lastOr]
  | cons b bs => simp [lastOr, lastOr_some_ne_none b bs]

theorem lastOr_cons_ne (b : Bool) : ∀ (bs : List Bool), bs ≠ [] →
    lastOr none (b :: bs) = lastOr none bs
  | [], h => absurd rfl h
  | c :: bs, _ => by simp [lastOr]

theorem bits_zero_ne_cons (b : Bool) (bs : List Bool) : (0 : ℕ).bits ≠ b :: bs := by simp

/-- Canonicity of a payload (the `readNat` check) is the last-bit test the machine performs. -/
theorem canon_iff : ∀ bs : List Bool, (bitsValue bs).bits = bs ↔ lastOr none bs ≠ some false
  | [] => by simp [bitsValue, lastOr]
  | [b] => by cases b <;> simp [bitsValue, lastOr, Nat.bit]
  | b :: c :: bs => by
    have ih := canon_iff (c :: bs)
    rw [lastOr_cons_ne b (c :: bs) (by simp)]
    rw [← ih]
    set v := bitsValue (c :: bs) with hv
    have hval : bitsValue (b :: c :: bs) = Nat.bit b v := rfl
    rw [hval]
    by_cases h0 : v = 0
    · have hne : v.bits ≠ c :: bs := by rw [h0]; simp
      simp only [hne, iff_false]
      rw [h0]
      cases b
      · simp [Nat.bit]
      · intro h
        have h1 : (Nat.bit true 0).bits = true :: (0 : ℕ).bits :=
          Nat.bits_append_bit 0 true (fun _ => rfl)
        rw [h1] at h
        simp at h
    · rw [Nat.bits_append_bit v b (fun h => absurd h h0)]
      simp

theorem value_ne_zero_of_canon {bs : List Bool} (hc : (bitsValue bs).bits = bs) (hne : bs ≠ []) :
    bitsValue bs ≠ 0 := by
  intro h
  rw [h] at hc
  simp at hc
  exact hne hc

theorem bitsValue_drop : ∀ (j : ℕ) (L : List Bool), bitsValue (L.drop j) = bitsValue L / 2 ^ j
  | 0, L => by simp
  | j + 1, [] => by simp [bitsValue]
  | j + 1, a :: L => by
    rw [List.drop_succ_cons, bitsValue_drop j L, bitsValue_cons, pow_succ, Nat.mul_comm (2 ^ j) 2,
      ← Nat.div_div_eq_div_mul]
    congr 1
    cases a <;> simp <;> omega

/-- The threshold carried by `w`: `val(lead w) / 2`. -/
noncomputable def thrW (w : List Bool) : ℝ := (bitsValue (lead w) : ℝ) / 2

theorem thrW_natField (m : ℕ) (rest : List Bool) : thrW (natField m ++ rest) = (m : ℝ) / 2 := by
  simp [thrW, natField, lead_field]

theorem thrW_midpoint (B k : ℕ) (rest : List Bool) :
    thrW (natField (2 * B + k) ++ rest) = (B : ℝ) + (k : ℝ) / 2 := by
  rw [thrW_natField]; push_cast; ring

/-- The nonnegative comparison: `z / 2^j < m / 2` iff the machine's bit is `true`. -/
theorem nonneg_compare (zs js mb : List Bool) :
    ((bitsValue zs : ℝ) / 2 ^ bitsValue js < (bitsValue mb : ℝ) / 2) ↔
      cmpF (loopF js (false :: zs)) mb false = true := by
  rw [cmpF_eq, loopF_eq, bitsValue_drop, bitsValue_cons]
  simp only [Bool.toNat_false, add_zero, Bool.false_eq_true, and_false, or_false,
    decide_eq_true_eq]
  -- lane a-model's `dyadic_lt_midpoint_iff_real` (frozen predecessor; it wraps the admitted
  -- `Amplification.dyadic_lt_midpoint_iff`) at `B = 0`, `k = m`
  have h := Paper2.AModel.dyadic_lt_midpoint_iff_real (bitsValue zs : ℤ) (bitsValue js) 0
    (bitsValue mb)
  simp only [Int.cast_natCast, Nat.cast_zero, zero_add, CharP.cast_eq_zero] at h
  rw [h, Nat.div_lt_iff_lt_mul (by positivity)]
  constructor
  · intro h'; exact_mod_cast (by linarith [h'] : (2 * (bitsValue zs : ℤ)) < bitsValue mb * 2 ^ bitsValue js)
  · intro h'
    have : (2 * (bitsValue zs : ℤ)) < bitsValue mb * 2 ^ bitsValue js := by exact_mod_cast h'
    linarith

/-- **The printed bit is exactly the specification bit.** -/
theorem spec_iff (w out : List Bool) :
    spec w out = true ↔ Below Paper2.AModel.decodeDyadic (thrW w) out := by
  unfold Below Paper2.AModel.decodeDyadic
  cases out with
  | nil => simp [spec, specOut, Paper2.AModel.readDyadic]
  | cons s bits =>
    cases hr : readField bits with
    | none =>
      simp [spec, specOut, hr, Paper2.AModel.readDyadic, readNat]
    | some p =>
      rcases p with ⟨zs, r1⟩
      have hc := canon_iff zs
      by_cases hz : lastOr none zs = some false
      · have hnc : ¬ (bitsValue zs).bits = zs := by rw [hc]; simp [hz]
        simp [spec, specOut, hr, hz, Paper2.AModel.readDyadic, readNat, hnc]
      · have hcz : (bitsValue zs).bits = zs := hc.mpr hz
        by_cases hneg : s = true ∧ lastOr none zs = none
        · have hzs : zs = [] := (lastOr_eq_none_iff zs).mp hneg.2
          subst hzs
          obtain ⟨hs, _⟩ := hneg
          subst hs
          simp [spec, specOut, hr, Paper2.AModel.readDyadic, readNat, bitsValue, lastOr]
        · have hbad : ¬ (lastOr none zs = some false ∨ (s = true ∧ lastOr none zs = none)) := by
            rintro (h | h)
            · exact hz h
            · exact hneg h
          cases hr1 : readField r1 with
          | none =>
            simp [spec, specOut, hr, hbad, hr1, Paper2.AModel.readDyadic, readNat, hcz]
          | some q =>
            rcases q with ⟨js, r2⟩
            have hcj := canon_iff js
            by_cases hj : lastOr none js = some false
            · have hnj : ¬ (bitsValue js).bits = js := by rw [hcj]; simp [hj]
              simp [spec, specOut, hr, hbad, hr1, hj, Paper2.AModel.readDyadic, readNat, hcz, hnj]
            · have hcj' : (bitsValue js).bits = js := hcj.mpr hj
              by_cases hr2 : r2 = []
              · subst hr2
                cases s with
                | true =>
                  have hzne : zs ≠ [] := by
                    intro h; apply hneg; exact ⟨rfl, (lastOr_eq_none_iff zs).mpr h⟩
                  have hv0 := value_ne_zero_of_canon hcz hzne
                  have hrd : Paper2.AModel.readDyadic (true :: bits) =
                      some (-(bitsValue zs : ℤ), bitsValue js) := by
                    simp [Paper2.AModel.readDyadic, readNat, hr, hr1, hcz, hcj', hv0]
                  have hnn : lastOr none zs ≠ none := fun h => hzne ((lastOr_eq_none_iff zs).mp h)
                  have hsp : spec w (true :: bits) = true := by
                    simp [spec, specOut, hr, hz, hnn, hr1, hj]
                  rw [hsp, hrd]
                  simp only [Option.map_some, Option.some.injEq, exists_eq_left', true_iff]
                  push_cast
                  have hpos : (0 : ℝ) < bitsValue zs := by exact_mod_cast Nat.pos_of_ne_zero hv0
                  have hm : (0 : ℝ) ≤ bitsValue (lead w) := by positivity
                  have : -(bitsValue zs : ℝ) / 2 ^ bitsValue js < 0 := by
                    apply div_neg_of_neg_of_pos (by linarith) (by positivity)
                  unfold thrW; linarith
                | false =>
                  have hrd : Paper2.AModel.readDyadic (false :: bits) =
                      some ((bitsValue zs : ℤ), bitsValue js) := by
                    simp [Paper2.AModel.readDyadic, readNat, hr, hr1, hcz, hcj']
                  have hsp : spec w (false :: bits) = cmpF (loopF js (false :: zs)) (lead w) false := by
                    simp [spec, specOut, hr, hz, hr1, hj]
                  rw [hsp, hrd, ← nonneg_compare]
                  simp only [Option.map_some, Option.some.injEq, exists_eq_left']
                  push_cast
                  rfl
              · simp [spec, specOut, hr, hbad, hr1, hj, hr2, Paper2.AModel.readDyadic, readNat,
                  hcz, hcj']

end Paper2.CmpOwner
