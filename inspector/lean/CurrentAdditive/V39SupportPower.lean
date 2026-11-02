import CurrentAdditive.V39GeneratedSupportBudget

/-! Uniform fixed-degree bounds on the actual retained label and Boolean-cell
counts. Rational bit lengths and execution time are deliberately not inferred
from these counting bounds. The order 8192 is a fixed construction constant.
-/

namespace CurrentAdditive.V39GeneratedConstruction

namespace SupportPower

def order : ℕ := 8192
def gammaDegree : ℕ := 3*order
def innerDegree : ℕ := 4*order
def outerDegree : ℕ := (3+gammaDegree)*order
def metadataDegree : ℕ := 3*order
def baseDegree : ℕ := 3*order
def selectorDegree : ℕ := (2+innerDegree)*order
def colDegree : ℕ := 1+metadataDegree+baseDegree+selectorDegree
def rowDegree : ℕ := (4+outerDegree+gammaDegree)*order
def cellDegree : ℕ := rowDegree+colDegree

theorem sum_power (z a b x y : ℕ) (hz : 2 ≤ z)
    (hx : x ≤ z^a) (hy : y ≤ z^b) : x+y ≤ z^(max a b+1) := by
  have ha := hx.trans (Nat.pow_le_pow_right (by omega : 0 < z) (le_max_left a b))
  have hb := hy.trans (Nat.pow_le_pow_right (by omega : 0 < z) (le_max_right a b))
  rw [pow_succ]
  nlinarith

theorem one_add_power (z a x : ℕ) (hz : 2 ≤ z)
    (hx : x ≤ z^a) : 1+x ≤ z^(a+1) := by
  have h := sum_power z 0 a 1 x hz (by simp) hx
  simpa only [Nat.zero_max] using h

theorem mul_power (z a b x y : ℕ)
    (hx : x ≤ z^a) (hy : y ≤ z^b) : x*y ≤ z^(a+b) := by
  simpa only [pow_add] using Nat.mul_le_mul hx hy

theorem power_power (z a x : ℕ) (hx : x ≤ z^a) :
    x^order ≤ z^(a*order) := by
  simpa only [pow_mul] using Nat.pow_le_pow_left hx order

/-- Parameters and the current dimensions are bounded independently of the
graph promise. Both output dimensions obey one fixed monomial envelope. -/
theorem budgets (q₁ q₂ s w Q nx ny ni z : ℕ) (hz : 2 ≤ z)
    (hγ : q₁+s+1 ≤ z) (hqi : q₁ ≤ z) (hq : q₂ ≤ z)
    (hs : s ≤ z) (hw : w ≤ z) (hQ : Q ≤ z)
    (hx : nx ≤ z) (hy : ny ≤ z) (hni : s+ni ≤ z) :
    rowBudget q₁ q₂ s w Q ny ≤ z^rowDegree ∧
    colBudget q₁ q₂ s w Q nx ni ≤ z^colDegree := by
  have atom {a : ℕ} (ha : a ≤ z) : a ≤ z^1 := by simpa only [pow_one] using ha
  have hg : gammaBudget q₁ s ny ≤ z^gammaDegree := by
    exact power_power z 3 _
      (one_add_power z 2 _ hz (mul_power z 1 1 _ _ (atom hγ) (atom hy)))
  have hi : innerBudget q₁ q₂ nx ≤ z^innerDegree := by
    exact power_power z 4 _
      (one_add_power z 3 _ hz (mul_power z 1 2 _ _ (atom hq)
        (mul_power z 1 1 _ _ (atom hqi) (atom hx))))
  have ho : outerBudget q₁ q₂ s ny ≤ z^outerDegree := by
    have hm := mul_power z 1 (1+gammaDegree) _ _
      (atom hs) (mul_power z 1 gammaDegree _ _ (atom hq) hg)
    have he : 1+(1+gammaDegree) = 2+gammaDegree := by omega
    rw [he] at hm
    have ha := one_add_power z (2+gammaDegree) _ hz hm
    have he' : 2+gammaDegree+1 = 3+gammaDegree := by omega
    rw [he'] at ha
    exact power_power z (3+gammaDegree) _ ha
  have hm : metadataBudget s w ni ≤ z^metadataDegree := by
    exact power_power z 3 _
      (one_add_power z 2 _ hz (mul_power z 1 1 _ _ (atom hw) (atom hni)))
  have hb : baseBudget w nx ≤ z^baseDegree := by
    exact power_power z 3 _
      (one_add_power z 2 _ hz (mul_power z 1 1 _ _ (atom hw) (atom hx)))
  have hsel : selectorBudget q₁ q₂ w nx ≤ z^selectorDegree := by
    exact power_power z (2+innerDegree) _
      (by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using (one_add_power z (1+innerDegree) _ hz
          (mul_power z 1 innerDegree _ _ (atom hw) hi)))
  have hleft : outerBudget q₁ q₂ s ny*gammaBudget q₁ s ny ≤
      z^(outerDegree+gammaDegree) := mul_power z _ _ _ _ ho hg
  have hright : q₂*gammaBudget q₁ s ny ≤ z^(outerDegree+gammaDegree) := by
    apply (mul_power z 1 gammaDegree _ _ (atom hq) hg).trans
    apply Nat.pow_le_pow_right (by omega)
    have : 1 ≤ outerDegree := by decide
    omega
  have hcolumns : outerBudget q₁ q₂ s ny*gammaBudget q₁ s ny+
      q₂*gammaBudget q₁ s ny ≤ z^(outerDegree+gammaDegree+1) := by
    simpa only [max_self] using sum_power z _ _ _ _ hz hleft hright
  constructor
  · have hm := mul_power z 1 (outerDegree+gammaDegree+1) _ _ (atom hw) hcolumns
    have he : 1+(outerDegree+gammaDegree+1) = 2+outerDegree+gammaDegree := by omega
    rw [he] at hm
    have hm' := mul_power z 1 (2+outerDegree+gammaDegree) _ _ (atom hQ) hm
    have he' : 1+(2+outerDegree+gammaDegree) = 3+outerDegree+gammaDegree := by omega
    rw [he'] at hm'
    have ha := one_add_power z (3+outerDegree+gammaDegree) _ hz hm'
    have he'' : 3+outerDegree+gammaDegree+1 = 4+outerDegree+gammaDegree := by omega
    rw [he''] at ha
    exact power_power z (4+outerDegree+gammaDegree) _ ha
  · exact (by simpa only [colDegree, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using (mul_power z 1 (metadataDegree+baseDegree+selectorDegree) _ _ (atom hQ)
        (by simpa only [Nat.add_assoc]
          using (mul_power z metadataDegree (baseDegree+selectorDegree) _ _ hm
            (mul_power z baseDegree selectorDegree _ _ hb hsel)))))

end SupportPower

/-- A concrete complete-slot count. This charges every Boolean entry and
both rational slots, but does not claim to charge the bits within a rational. -/
def StoredMatrix.slots (R : StoredMatrix) : ℕ :=
  R.rows*R.cols+R.rows+R.cols

variable {q₁ q₂ s w Q ni : ℕ}
  [NeZero q₁] [NeZero q₂] [NeZero s] [NeZero w] [NeZero Q]

theorem storedStep_cells_power (μI : Paper2.PositiveRationalLaw (Fin ni))
    (activity : Fin ni → Fin q₂ → Option (Fin s)) (R : StoredMatrix)
    (z : ℕ) (hz : 2 ≤ z)
    (hγ : q₁+s+1 ≤ z) (hqi : q₁ ≤ z) (hq : q₂ ≤ z)
    (hs : s ≤ z) (hw : w ≤ z) (hQ : Q ≤ z)
    (hx : R.rows ≤ z) (hy : R.cols ≤ z) (hni : s+ni ≤ z) :
    (StoredMatrix.step (q₁ := q₁) (s := s) (w := w) (Q := Q) μI activity R).rows *
      (StoredMatrix.step (q₁ := q₁) (s := s) (w := w) (Q := Q) μI activity R).cols ≤
        z^SupportPower.cellDegree := by
  have h := storedStep_dimensions (q₁ := q₁) (s := s) (w := w) (Q := Q) μI activity R
  have b := SupportPower.budgets q₁ q₂ s w Q R.rows R.cols ni z hz
    hγ hqi hq hs hw hQ hx hy hni
  exact (Nat.mul_le_mul h.1 h.2).trans
    (SupportPower.mul_power z _ _ _ _ b.1 b.2)

def supportEnvelope (q₁ q₂ s w Q ni : ℕ) (R : StoredMatrix) : ℕ :=
  q₁+q₂+s+w+Q+ni+R.rows*R.cols+4

/-- One fixed effective power of two dominates the literal nested support
degrees. It is a count exponent, not an unproved bit-clock bound. -/
def supportAmplification : ℕ := 2^64

theorem supportDegree_le_amplification : SupportPower.cellDegree+1 ≤ supportAmplification := by
  norm_num [SupportPower.cellDegree, SupportPower.rowDegree, SupportPower.colDegree,
    SupportPower.outerDegree, SupportPower.gammaDegree, SupportPower.metadataDegree,
    SupportPower.baseDegree, SupportPower.selectorDegree, SupportPower.innerDegree,
    SupportPower.order, supportAmplification]

theorem supportEnvelope_step (μI : Paper2.PositiveRationalLaw (Fin ni))
    (activity : Fin ni → Fin q₂ → Option (Fin s)) (R : StoredMatrix) :
    supportEnvelope q₁ q₂ s w Q ni
      (StoredMatrix.step (q₁ := q₁) (s := s) (w := w) (Q := Q) μI activity R) ≤
        (supportEnvelope q₁ q₂ s w Q ni R)^supportAmplification := by
  let z := supportEnvelope q₁ q₂ s w Q ni R
  have hrow : R.rows ≤ R.rows*R.cols := by
    simpa using Nat.mul_le_mul_left R.rows (law_size_pos R.colLaw)
  have hcol : R.cols ≤ R.rows*R.cols := by
    simpa using Nat.mul_le_mul_right R.cols (law_size_pos R.rowLaw)
  have hz : 2 ≤ z := by dsimp [z, supportEnvelope]; omega
  have hb := storedStep_cells_power (q₁ := q₁) (s := s) (w := w) (Q := Q)
    μI activity R z hz (by dsimp [z,supportEnvelope]; omega)
      (by dsimp [z,supportEnvelope]; omega) (by dsimp [z,supportEnvelope]; omega)
      (by dsimp [z,supportEnvelope]; omega) (by dsimp [z,supportEnvelope]; omega)
      (by dsimp [z,supportEnvelope]; omega) (by dsimp [z,supportEnvelope]; omega)
      (by dsimp [z,supportEnvelope]; omega) (by dsimp [z,supportEnvelope]; omega)
  have hD : 1 ≤ SupportPower.cellDegree := by decide
  have hzpow : z ≤ z^SupportPower.cellDegree := Nat.le_self_pow (by omega) z
  have hsmall : supportEnvelope q₁ q₂ s w Q ni
      (StoredMatrix.step (q₁ := q₁) (s := s) (w := w) (Q := Q) μI activity R) ≤
      z+z^SupportPower.cellDegree := by
    change q₁+q₂+s+w+Q+ni+
      (StoredMatrix.step (q₁ := q₁) (s := s) (w := w) (Q := Q) μI activity R).rows *
      (StoredMatrix.step (q₁ := q₁) (s := s) (w := w) (Q := Q) μI activity R).cols+4 ≤
      z+z^SupportPower.cellDegree
    have hzsum : q₁+q₂+s+w+Q+ni+4 ≤ z := by dsimp [z,supportEnvelope]; omega
    omega
  calc
    _ ≤ z+z^SupportPower.cellDegree := hsmall
    _ ≤ z^(SupportPower.cellDegree+1) := by rw [pow_succ]; nlinarith
    _ ≤ z^supportAmplification :=
      Nat.pow_le_pow_right (by omega) supportDegree_le_amplification

theorem supportEnvelope_iterate (μI : Paper2.PositiveRationalLaw (Fin ni))
    (activity : Fin ni → Fin q₂ → Option (Fin s)) (R : StoredMatrix) (k : ℕ) :
    supportEnvelope q₁ q₂ s w Q ni
      (StoredMatrix.iterate (q₁ := q₁) (s := s) (w := w) (Q := Q) μI activity k R) ≤
        (supportEnvelope q₁ q₂ s w Q ni R)^(supportAmplification^k) := by
  induction k with
  | zero => simp [StoredMatrix.iterate]
  | succ k ih =>
    have h := supportEnvelope_step (q₁ := q₁) (s := s) (w := w) (Q := Q) μI activity
      (StoredMatrix.iterate (q₁ := q₁) (s := s) (w := w) (Q := Q) μI activity k R)
    apply h.trans
    have hp := Nat.pow_le_pow_left ih supportAmplification
    simpa only [← pow_mul, pow_succ] using hp

end CurrentAdditive.V39GeneratedConstruction

#print axioms CurrentAdditive.V39GeneratedConstruction.SupportPower.budgets
#print axioms CurrentAdditive.V39GeneratedConstruction.storedStep_cells_power
#print axioms CurrentAdditive.V39GeneratedConstruction.supportEnvelope_iterate
