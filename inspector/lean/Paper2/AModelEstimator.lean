import Paper2.AModelPrefix
import Paper2.YaoBppDraft
import Paper2.A4Amplification
import EthInapproximability.CurrentPaper.EncodedETHTail

/-!
# Paper A (lock v12), lane `owner:a-model-1`, segment 2: the D-A3 / D-Y3 estimator interface

Author decisions of 27 September 2026 (`AUTHOR_DECISIONS_2026-09-27.md`):
* **D-A3**: "Input: the matrix part of what the reduction prints, `(rows, cols, table)` (option (c),
  a projection machine from `outputBits`). Output: a dyadic rational (binary fraction), option
  (ii), with a rounding front end."
* **D-Y3**: "(a) the same format as D-A3."

Lock v12 text implemented (`versions/2026-09-22-protocol-labels-v12/source/sections/`):
* `01-introduction.tex:72-76`: "An additive-error-$a$ estimator returns a number $\widehat D(M)$
  with $|\widehat D(M)-\D(M)|\le a$. A randomized estimator must succeed with probability at least
  $2/3$ on every input.\footnote{The numerical output must permit polynomial-time comparison with
  binary rationals of polynomial length, as required by the decision procedure using the
  estimator.}"
* `07-yao.tex:375-379` (`yao:bpp`): "estimating any of $D_A^{\mathrm{alt}}$,
  $D_B^{\mathrm{alt}}$, $D_{\mathrm{free}}^{\mathrm{alt}}$, or $Y_{\mathrm{free}}$ within additive
  error $u$ on every explicit total Boolean matrix".

Codecs: the input is `matrixWord rows cols table = natField rows ++ natField cols ++ table`, i.e.
the admitted `EncodedCommunication.encodeInstance` word with the threshold field dropped
(`encodeInstance_eq_split`, `decodeMatrix_of_decodeInstance`). No admitted binary-rational codec
exists (grep of Paper2 and CurrentPaper for dyadic/rational codecs: none); the output codec
`encodeDyadic z j = encodeInteger z ++ natField j` reuses the admitted signed-integer codec
`EncodedETHTail.encodeInteger` for the numerator and a `natField` exponent, value `z / 2^j`.
Rounding front end: `dyadic_floor_error` (reusing the admitted `Amplification.floor_error`) and
the midpoint comparison `dyadic_lt_midpoint_iff_real` (the real form of the admitted
`Amplification.dyadic_lt_midpoint_iff`).

NOT built here: the physical projection machine from `outputBits` to `matrixWord` (D-A3 "a
projection machine"), and the physical comparator. Both are machine obligations of the composed
decider. No ledger row is closed.
-/

noncomputable section

namespace Paper2.AModel

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open EthInapproximability.CurrentPaper.EncodedComplexity
open Workspace.Types.CommComplexity
open Paper2 Paper2.FiniteLaw
open Paper2.Unit4Shell.Definitions
open Paper2.YaoBppDraft

/-! ## Input codec (D-A3 option (c)) -/

/-- **D-A3 input word** (lock `01-introduction.tex:72-73`, "an estimator returns a number
$\widehat D(M)$"; `M` given as the matrix part of what the reduction prints): self-delimiting
binary fields for the row and column counts, then the literal row-major table. This is
`EncodedCommunication.encodeInstance` without its threshold field. -/
def matrixWord (rows cols : ℕ) (table : List Bool) : List Bool :=
  natField rows ++ natField cols ++ table

/-- D-A3: well-formedness of a matrix triple (positive dimensions, exact table length), the same
conditions as `EncodedCommunication.Instance.Valid`. -/
def MatrixValid (rows cols : ℕ) (table : List Bool) : Prop :=
  0 < rows ∧ 0 < cols ∧ table.length = rows * cols

instance (rows cols : ℕ) (table : List Bool) : Decidable (MatrixValid rows cols table) :=
  inferInstanceAs (Decidable (0 < rows ∧ 0 < cols ∧ table.length = rows * cols))

/-- D-A3 input decoder: canonical fields, positive dimensions and exact table length; every other
word is rejected (`none`). -/
def decodeMatrix (w : List Bool) : Option (ℕ × ℕ × List Bool) := do
  let (rows, rest) ← readNat w
  let (cols, table) ← readNat rest
  if MatrixValid rows cols table then some (rows, cols, table) else none

theorem decodeMatrix_matrixWord {rows cols : ℕ} {table : List Bool}
    (h : MatrixValid rows cols table) :
    decodeMatrix (matrixWord rows cols table) = some (rows, cols, table) := by
  simp [decodeMatrix, matrixWord, List.append_assoc, readNat_append, h]

theorem decodeMatrix_sound {w : List Bool} {rows cols : ℕ} {table : List Bool}
    (h : decodeMatrix w = some (rows, cols, table)) :
    matrixWord rows cols table = w ∧ MatrixValid rows cols table := by
  unfold decodeMatrix at h
  cases h₁ : readNat w with
  | none => simp [h₁] at h
  | some p₁ =>
      rcases p₁ with ⟨r, tail₁⟩
      cases h₂ : readNat tail₁ with
      | none => simp [h₁, h₂] at h
      | some p₂ =>
          rcases p₂ with ⟨c, t⟩
          simp only [h₁, h₂, Bind.bind, Option.bind] at h
          split at h
          · rename_i hv
            cases Option.some.inj h
            refine ⟨?_, hv⟩
            simp only [matrixWord, List.append_assoc, readNat_sound h₂, readNat_sound h₁]
          · contradiction

/-- The matrix word of an encoded instance (its threshold dropped). -/
def instanceMatrixWord (i : Instance) : List Bool := matrixWord i.rows i.cols i.table

/-- The admitted instance word is the matrix word with the threshold field inserted. -/
theorem encodeInstance_eq_split (i : Instance) :
    encodeInstance i = natField i.rows ++ natField i.cols ++ natField i.threshold ++ i.table :=
  rfl

/-- Dropping the threshold field of a decodable instance word gives a decodable matrix word with
the same dimensions and table. -/
theorem decodeMatrix_of_decodeInstance {w : List Bool} {i : Instance}
    (h : decodeInstance w = some i) :
    decodeMatrix (instanceMatrixWord i) = some (i.rows, i.cols, i.table) :=
  decodeMatrix_matrixWord (decode_valid h)

/-- Conversely, any threshold can be inserted into a decodable matrix word. -/
theorem decodeInstance_of_decodeMatrix {w : List Bool} {rows cols : ℕ} {table : List Bool}
    (h : decodeMatrix w = some (rows, cols, table)) (threshold : ℕ) :
    decodeInstance (encodeInstance ⟨rows, cols, threshold, table⟩) =
      some ⟨rows, cols, threshold, table⟩ :=
  decode_encode _ (decodeMatrix_sound h).2

/-! ## Output codec (D-A3 option (ii)): dyadic rationals -/

/-- **D-A3 numeric output** (lock `01-introduction.tex:74-76`, footnote: "binary rationals of
polynomial length"): the dyadic rational `z / 2^j` printed as the admitted signed-integer word of
`z` followed by the `natField` of `j`. -/
def encodeDyadic (z : ℤ) (j : ℕ) : List Bool := EncodedETHTail.encodeInteger z ++ natField j

/-- D-A3 output parser: sign bit, canonical magnitude field, canonical exponent field, nothing
after; the sign of zero is nonnegative (as `EncodedETHTail.readInteger`). -/
def readDyadic : List Bool → Option (ℤ × ℕ)
  | [] => none
  | negative :: bits => do
      let (magnitude, rest) ← readNat bits
      let (j, rest') ← readNat rest
      if rest' = [] ∧ (negative = true → magnitude ≠ 0) then
        pure ((if negative then -(magnitude : ℤ) else (magnitude : ℤ)), j)
      else none

/-- D-A3 numeric decoder `List Bool → Option ℝ` (the DRAFT `Estimates` parameter): the value
`z / 2^j` of a parsed dyadic word. -/
def decodeDyadic (w : List Bool) : Option ℝ :=
  (readDyadic w).map (fun p => (p.1 : ℝ) / 2 ^ p.2)

theorem readDyadic_encode (z : ℤ) (j : ℕ) : readDyadic (encodeDyadic z j) = some (z, j) := by
  have hread (n : ℕ) : readNat (natField n) = some (n, []) := by
    simpa only [List.append_nil] using readNat_append n []
  cases z with
  | ofNat n =>
      have hn : ¬(Int.ofNat n < 0) := not_lt_of_ge (Int.natCast_nonneg n)
      simp [encodeDyadic, EncodedETHTail.encodeInteger, readDyadic, readNat_append, hread, hn]
  | negSucc n =>
      have hn : Int.negSucc n < 0 := by omega
      simp [encodeDyadic, EncodedETHTail.encodeInteger, readDyadic, readNat_append, hread, hn,
        Int.natAbs_negSucc]
      omega

theorem decodeDyadic_encode (z : ℤ) (j : ℕ) :
    decodeDyadic (encodeDyadic z j) = some ((z : ℝ) / 2 ^ j) := by
  simp [decodeDyadic, readDyadic_encode]

/-- Rounding front end: flooring a dyadic estimate `z / 2^j` (the integer `z / 2^j`, a shift)
keeps an integer additive error bound around an integer target (reuses the admitted
`Amplification.floor_error`). -/
theorem dyadic_floor_error (z : ℤ) (j : ℕ) (c : ℕ) (A : ℤ)
    (h : |(z : ℝ) / 2 ^ j - (c : ℝ)| ≤ (A : ℝ)) :
    |z / (2 ^ j : ℕ) - (c : ℤ)| ≤ A := by
  have hq : |(z : ℚ) / 2 ^ j - ((c : ℤ) : ℚ)| ≤ (A : ℚ) := by
    have h' : ((|(z : ℚ) / 2 ^ j - ((c : ℤ) : ℚ)| : ℚ) : ℝ) ≤ ((A : ℚ) : ℝ) := by
      push_cast; exact h
    exact_mod_cast h'
  have hf := Paper2.Unit4Shell.Amplification.floor_error ((z : ℚ) / 2 ^ j) (c : ℤ) A hq
  have hfl : ⌊(z : ℚ) / 2 ^ j⌋ = z / ((2 ^ j : ℕ) : ℤ) := by
    have := Rat.floor_intCast_div_natCast z (2 ^ j)
    simpa using this
  rw [hfl] at hf
  exact hf

/-- Real form of the admitted `Amplification.dyadic_lt_midpoint_iff`: comparing a dyadic
estimate with the midpoint `B + k/2` is one integer comparison. -/
theorem dyadic_lt_midpoint_iff_real (z : ℤ) (j B k : ℕ) :
    ((z : ℝ) / 2 ^ j < (B : ℝ) + (k : ℝ) / 2) ↔ 2 * z < 2 ^ j * (2 * (B : ℤ) + k) := by
  have hq := Paper2.Unit4Shell.Amplification.dyadic_lt_midpoint_iff z j B k
  rw [← hq]
  constructor
  · intro h
    have : (((z : ℚ) / 2 ^ j : ℚ) : ℝ) < (((B : ℚ) + (k : ℚ) / 2 : ℚ) : ℝ) := by
      push_cast; exact h
    exact_mod_cast this
  · intro h
    have : (((z : ℚ) / 2 ^ j : ℚ) : ℝ) < (((B : ℚ) + (k : ℚ) / 2 : ℚ) : ℝ) := by
      exact_mod_cast h
    push_cast at this
    exact this

/-! ## The estimated quantities and the estimator predicates -/

/-- **D-A3 target** (lock `01-introduction.tex:72-73`, "$\D(M)$"): the deterministic communication
complexity `D` of the decoded table game, defined exactly on the decodable matrix words. -/
def targetD (w : List Bool) : Option ℕ :=
  (decodeMatrix w).map (fun m => D (ProtocolVerifier.tableGame m.1 m.2.1 m.2.2))

theorem targetD_matrixWord {rows cols : ℕ} {table : List Bool}
    (h : MatrixValid rows cols table) :
    targetD (matrixWord rows cols table) = some (D (ProtocolVerifier.tableGame rows cols table)) := by
  simp [targetD, decodeMatrix_matrixWord h]

/-- **D-A3 estimator** in the D-A1 prefix model (lock `01-introduction.tex:72-74`, "returns a
number $\widehat D(M)$ with $|\widehat D(M)-\D(M)|\le a$ ... must succeed with probability at least
$2/3$ on every input"): on every decodable matrix word, with probability at least `2/3` over the
uniform tape the printed word is a dyadic rational within additive error `a` of `D`. -/
def PrefixAlgorithm.EstimatesD (A : PrefixAlgorithm) (a : ℝ) : Prop :=
  ∀ w c, targetD w = some c →
    2 / 3 ≤ A.prob w (fun out => ∃ v, decodeDyadic out = some v ∧ |v - c| ≤ a)

/-- The D-A3 estimator is the DRAFT `Estimates` at `target := targetD`, `decode := decodeDyadic`. -/
theorem PrefixAlgorithm.estimatesD_iff_draft (A : PrefixAlgorithm) (a : ℝ) :
    A.EstimatesD a ↔ A.toDraft.Estimates targetD decodeDyadic a := Iff.rfl

/-- D-Y3: the instance of a matrix triple with threshold `0` (the Yao measures ignore it). -/
def matrixInstance (m : ℕ × ℕ × List Bool) : Instance := ⟨m.1, m.2.1, 0, m.2.2⟩

/-- The admitted DRAFT `YaoMeasure.eval` does not read the threshold. -/
theorem YaoMeasure_eval_threshold (μ : YaoMeasure) (i : Instance) (B : ℕ) :
    μ.eval ⟨i.rows, i.cols, B, i.table⟩ = μ.eval i := by
  cases μ <;> rfl

/-- **D-Y3 target** (lock `07-yao.tex:375-379`, "any of $D_A^{\mathrm{alt}}$, ...,
$Y_{\mathrm{free}}$ ... on every explicit total Boolean matrix"): the admitted DRAFT
`YaoMeasure.eval` of the decoded matrix, defined exactly on the decodable matrix words (D-A3
format). -/
def targetYao (μ : YaoMeasure) (w : List Bool) : Option ℕ :=
  (decodeMatrix w).map (fun m => μ.eval (matrixInstance m))

/-- On the matrix word of a decodable instance word, the D-Y3 target is the admitted DRAFT
`yaoTarget` of the instance word (the only change of format is dropping the threshold). -/
theorem targetYao_instance (μ : YaoMeasure) {w : List Bool} {i : Instance}
    (h : decodeInstance w = some i) :
    targetYao μ (instanceMatrixWord i) = yaoTarget μ w := by
  simp only [targetYao, decodeMatrix_of_decodeInstance h, yaoTarget, h, Option.map_some,
    matrixInstance]
  exact congrArg some (YaoMeasure_eval_threshold μ i 0)

/-- **D-Y3 estimator** in the D-A1 prefix model (lock `07-yao.tex:375-379`, "estimating ... within
additive error $u$ on every explicit total Boolean matrix"; conventions `01-introduction.tex:72-76`). -/
def PrefixAlgorithm.EstimatesYao (A : PrefixAlgorithm) (μ : YaoMeasure) (u : ℝ) : Prop :=
  ∀ w c, targetYao μ w = some c →
    2 / 3 ≤ A.prob w (fun out => ∃ v, decodeDyadic out = some v ∧ |v - c| ≤ u)

theorem PrefixAlgorithm.estimatesYao_iff_draft (A : PrefixAlgorithm) (μ : YaoMeasure) (u : ℝ) :
    A.EstimatesYao μ u ↔ A.toDraft.Estimates (targetYao μ) decodeDyadic u := Iff.rfl

end Paper2.AModel

end

#print axioms Paper2.AModel.decodeMatrix_matrixWord
#print axioms Paper2.AModel.decodeMatrix_sound
#print axioms Paper2.AModel.decodeMatrix_of_decodeInstance
#print axioms Paper2.AModel.decodeInstance_of_decodeMatrix
#print axioms Paper2.AModel.readDyadic_encode
#print axioms Paper2.AModel.decodeDyadic_encode
#print axioms Paper2.AModel.dyadic_floor_error
#print axioms Paper2.AModel.dyadic_lt_midpoint_iff_real
#print axioms Paper2.AModel.targetD_matrixWord
#print axioms Paper2.AModel.PrefixAlgorithm.estimatesD_iff_draft
#print axioms Paper2.AModel.YaoMeasure_eval_threshold
#print axioms Paper2.AModel.targetYao_instance
#print axioms Paper2.AModel.PrefixAlgorithm.estimatesYao_iff_draft
