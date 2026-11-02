import CurrentAdditive.RoundedProgram
import CurrentAdditive.V38Matrix
import Paper2.RecursiveSamplingSource

set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000

/-! Literal v38 one-step complete-label programs. The only reused v12
    generator pieces are the unchanged uniform template/item rule and the
    unchanged full-product inner raw/outer payloads. The v38 two-family
    column mixture is defined here with its actual 255/256 interval. -/

namespace CurrentAdditive.V38OneStep

open Paper2 Paper2.RecursiveSamplingProgram Paper2.RecursiveSamplingLaws
open Paper2.RecursiveSampling
open CurrentAdditive.V38Matrix

variable {X Y V : Type*} {q₁ q₂ s w Q : ℕ}

/-- The 256-ticket v38 mixture: 0--254 ordinary, 255 diagonal. -/
def tagged [NeZero q₂] (pY : Program Y) :
    Program (TaggedColumn q₁ q₂ s Y) :=
  .draw 256 (by decide) fun t =>
    if t.val < 255 then
      Program.map Sum.inl (Paper2.RecursiveSampling.raw
        (q₁ := q₁) (q₂ := q₂) (s := s) pY)
    else
      Program.map Sum.inr (Paper2.RecursiveSampling.outer
        (q₁ := q₁) (q₂ := q₂) (s := s) pY)

/-- The two item families are sampled by their actual group and local
coordinates, rather than by enumerating the complete item carrier. -/
def vertexItems [NeZero (4 * s)] (pV : Program V) :
    Program (Fin (4 * s) × V) :=
  RecursiveSamplingLaws.prod (Paper2.RecursiveSampling.uniform (4 * s)) pV

def auxiliaryItems [NeZero (4 * s)] [NeZero (s - 3)] :
    Program (Fin (4 * s) × Fin (s - 3)) :=
  RecursiveSamplingLaws.prod (Paper2.RecursiveSampling.uniform (4 * s))
    (Paper2.RecursiveSampling.uniform (s - 3))

/-- One complete raw row: the unchanged 510/512, 1/512, 1/512 rule,
relabelled by the explicit item-association bijection. -/
def rawRows [NeZero q₁] [NeZero s] [NeZero (4 * s)] [NeZero (s - 3)]
    (pV : Program V) (pX : Program X) :
    Program (Paper2.SourceMatrix.RawRow q₁ q₂ s X
      (CurrentAdditive.EdgeSourceMatrix.Items s V)) :=
  Program.map (Paper2.SourceLawBinding.rawRowEquiv q₁ q₂ s X V)
    (Paper2.RecursiveSampling.rows
      (q₁ := q₁) (q₂ := q₂) (s := s)
      (vertexItems (s := s) pV) (auxiliaryItems (s := s)) pX)

/-- The complete successor row `((i_t,Z_t))_[Q]`. -/
def successorRow [NeZero q₂] [NeZero w]
    (pY : Program Y) :
    Program (Fin Q → Fin w × TaggedColumn q₁ q₂ s Y) :=
  RecursiveSamplingLaws.iid
    (RecursiveSamplingLaws.prod (Paper2.RecursiveSampling.uniform w)
      (tagged (q₁ := q₁) (q₂ := q₂) (s := s) pY)) Q

/-- The complete successor column `(j,(k_i)_[w])`. -/
def successorColumn [NeZero q₁] [NeZero s] [NeZero (4 * s)]
    [NeZero (s - 3)] [NeZero Q]
    (pV : Program V) (pX : Program X) :
    Program (Fin Q × (Fin w → Paper2.SourceMatrix.RawRow q₁ q₂ s X
      (CurrentAdditive.EdgeSourceMatrix.Items s V))) :=
  RecursiveSamplingLaws.prod (Paper2.RecursiveSampling.uniform Q)
    (RecursiveSamplingLaws.iid (rawRows (q₁ := q₁) (q₂ := q₂) (s := s) pV pX) w)

section ExactLaws

variable [Fintype X] [Fintype Y] [Fintype V]

private theorem expect_if {B : Type*} (h : Prop) [Decidable h]
    (p q : Program B) (f : B → ℝ) :
    Program.expect (if h then p else q) f =
      if h then Program.expect p f else Program.expect q f := by
  split_ifs <;> rfl

private theorem ticket_average (a b : ℝ) :
    (256 : ℝ)⁻¹ *
        (∑ t : Fin 256, if t.val < 255 then a else b) =
      (255 / 256 : ℝ) * a + (1 / 256 : ℝ) * b := by
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  simp
  ring

private theorem tagged_expect [NeZero q₂]
    (ν : PositiveRationalLaw Y)
    (f : TaggedColumn q₁ q₂ s Y → ℝ) :
    (∑ Z, (taggedLaw (q₁ := q₁) (q₂ := q₂) (s := s) ν).toFiniteLaw.weight Z * f Z) =
      (255 / 256 : ℝ) *
        (∑ Z, (Paper2.SourceLaws.rawLaw ν q₁ q₂ s).toFiniteLaw.weight Z * f (.inl Z)) +
      (1 / 256 : ℝ) *
        (∑ j, (Paper2.SourceLaws.outerLaw ν q₁ q₂ s).toFiniteLaw.weight j * f (.inr j)) := by
  rw [Fintype.sum_sum_type]
  simp only [PositiveRationalLaw.toFiniteLaw, taggedLaw,
    Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Finset.mul_sum, mul_assoc]

theorem generates_tagged [NeZero q₂]
    {pY : Program Y} {ν : PositiveRationalLaw Y}
    (hp : Generates pY ν.toFiniteLaw) :
    Generates (tagged (q₁ := q₁) (q₂ := q₂) (s := s) pY)
      (taggedLaw (q₁ := q₁) (q₂ := q₂) (s := s) ν).toFiniteLaw := by
  intro f
  rw [tagged, Program.expect_draw]
  simp only [expect_if, Program.expect_map]
  simp only [Nat.cast_ofNat]
  rw [ticket_average, Paper2.RecursiveSampling.generates_raw hp,
    Paper2.RecursiveSampling.generates_outer hp]
  exact (tagged_expect ν f).symm

theorem generates_vertexItems [NeZero (4 * s)] [Nonempty V]
    {pV : Program V} (hp : Generates pV (PositiveRationalLaw.uniform V).toFiniteLaw) :
    Generates (vertexItems (s := s) pV)
      (PositiveRationalLaw.uniform (Fin (4 * s) × V)).toFiniteLaw := by
  rw [← RecursiveSamplingLaws.uniform_prod]
  exact generates_rational_prod (generates_uniform (4 * s)) hp

theorem generates_auxiliaryItems [NeZero (4 * s)] [NeZero (s - 3)] :
    Generates (auxiliaryItems (s := s))
      (PositiveRationalLaw.uniform (Fin (4 * s) × Fin (s - 3))).toFiniteLaw := by
  rw [← RecursiveSamplingLaws.uniform_prod]
  exact generates_rational_prod (generates_uniform (4 * s)) (generates_uniform (s - 3))

theorem generates_rawRows [NeZero q₁] [NeZero q₂] [NeZero s]
    [NeZero (4 * s)] [NeZero (s - 3)] [Nonempty V]
    {pV : Program V} {pX : Program X} {μ : PositiveRationalLaw X}
    (hv : Generates pV (PositiveRationalLaw.uniform V).toFiniteLaw)
    (hx : Generates pX μ.toFiniteLaw) :
    Generates (rawRows (q₁ := q₁) (q₂ := q₂) (s := s) pV pX)
      (columnLaw (q₁ := q₁) (q₂ := q₂) (s := s) (V := V) μ
        (by have h := Nat.pos_of_ne_zero (NeZero.ne (s - 3)); omega)).toFiniteLaw := by
  let hs : 4 ≤ s := by have h := Nat.pos_of_ne_zero (NeZero.ne (s - 3)); omega
  letI : Nonempty (Fin (4 * s) × V) := inferInstance
  letI : Nonempty (Fin (4 * s) × Fin (s - 3)) := inferInstance
  change Generates (Program.map (Paper2.SourceLawBinding.rawRowEquiv q₁ q₂ s X V)
    (Paper2.RecursiveSampling.rows
      (vertexItems (s := s) pV) (auxiliaryItems (s := s)) pX)) _
  rw [columnLaw, CurrentAdditive.EdgeSourceMatrix.matrixColumnLaw]
  exact generates_relabel
    (Paper2.RecursiveSampling.generates_rows
      (generates_vertexItems hv) generates_auxiliaryItems hx)
    (Paper2.SourceLawBinding.rawRowEquiv q₁ q₂ s X V)

end ExactLaws

section SuccessorLaws

variable [Fintype X] [Fintype Y] [Fintype V]

noncomputable def successorRowLaw [NeZero q₂] [NeZero w]
    (ν : PositiveRationalLaw Y) :
    PositiveRationalLaw (Fin Q → Fin w × TaggedColumn q₁ q₂ s Y) :=
  ((PositiveRationalLaw.uniform (Fin w)).prod
    (taggedLaw (q₁ := q₁) (q₂ := q₂) (s := s) ν)).iid Q

noncomputable def successorColumnLaw [NeZero q₁] [NeZero Q]
    [Nonempty V] (μ : PositiveRationalLaw X) (hs : 4 ≤ s) :
    PositiveRationalLaw (Fin Q ×
      (Fin w → Paper2.SourceMatrix.RawRow q₁ q₂ s X
        (CurrentAdditive.EdgeSourceMatrix.Items s V))) :=
  (PositiveRationalLaw.uniform (Fin Q)).prod
    ((columnLaw (q₁ := q₁) (q₂ := q₂) (s := s) (V := V) μ hs).iid w)

theorem generates_successorRow [NeZero q₂] [NeZero w]
    {pY : Program Y} {ν : PositiveRationalLaw Y}
    (hp : Generates pY ν.toFiniteLaw) :
    Generates (successorRow (q₁ := q₁) (q₂ := q₂) (s := s)
      (w := w) (Q := Q) pY)
      (successorRowLaw (q₁ := q₁) (q₂ := q₂) (s := s)
        (w := w) (Q := Q) ν).toFiniteLaw := by
  exact generates_rational_iid
    (generates_rational_prod (generates_uniform w) (generates_tagged hp)) Q

theorem generates_successorColumn [NeZero q₁] [NeZero q₂]
    [NeZero s] [NeZero (4 * s)] [NeZero (s - 3)] [NeZero Q]
    [Nonempty V]
    {pV : Program V} {pX : Program X} {μ : PositiveRationalLaw X}
    (hv : Generates pV (PositiveRationalLaw.uniform V).toFiniteLaw)
    (hx : Generates pX μ.toFiniteLaw) :
    Generates (successorColumn (q₁ := q₁) (q₂ := q₂) (s := s)
      (w := w) (Q := Q) pV pX)
      (successorColumnLaw (q₁ := q₁) (q₂ := q₂) (s := s)
        (w := w) (Q := Q) (V := V) μ
        (by have h := Nat.pos_of_ne_zero (NeZero.ne (s - 3)); omega)).toFiniteLaw := by
  exact generates_rational_prod (generates_uniform Q)
    (generates_rational_iid (generates_rawRows hv hx) w)

end SuccessorLaws

section FullSample

variable [Fintype X] [Fintype Y] [Fintype V]

abbrev RowLabel (q₁ q₂ s w Q : ℕ) (Y : Type*) :=
  Fin Q → Fin w × TaggedColumn q₁ q₂ s Y

abbrev ColumnLabel (q₁ q₂ s w Q : ℕ) (X V : Type*) :=
  Fin Q × (Fin w → Paper2.SourceMatrix.RawRow q₁ q₂ s X
    (CurrentAdditive.EdgeSourceMatrix.Items s V))

/-- Generate exactly `m` complete successor row labels and `m` complete
successor column labels, retaining every independent coordinate. -/
def fullSample [NeZero q₁] [NeZero q₂] [NeZero s]
    [NeZero (4 * s)] [NeZero (s - 3)] [NeZero w] [NeZero Q]
    (m : ℕ) (pV : Program V) (pX : Program X) (pY : Program Y) :
    Program ((Fin m → RowLabel q₁ q₂ s w Q Y) ×
      (Fin m → ColumnLabel q₁ q₂ s w Q X V)) :=
  RecursiveSamplingLaws.prod
    (RecursiveSamplingLaws.iid (successorRow (q₁ := q₁) (q₂ := q₂)
      (s := s) (w := w) (Q := Q) pY) m)
    (RecursiveSamplingLaws.iid (successorColumn (q₁ := q₁) (q₂ := q₂)
      (s := s) (w := w) (Q := Q) pV pX) m)

noncomputable def fullSampleLaw [NeZero q₁] [NeZero q₂]
    [NeZero w] [NeZero Q] [Nonempty V]
    (m : ℕ) (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (hs : 4 ≤ s) :
    PositiveRationalLaw ((Fin m → RowLabel q₁ q₂ s w Q Y) ×
      (Fin m → ColumnLabel q₁ q₂ s w Q X V)) :=
  ((successorRowLaw (q₁ := q₁) (q₂ := q₂) (s := s)
    (w := w) (Q := Q) ν).iid m).prod
    ((successorColumnLaw (q₁ := q₁) (q₂ := q₂) (s := s)
      (w := w) (Q := Q) (V := V) μ hs).iid m)

theorem generates_fullSample [NeZero q₁] [NeZero q₂]
    [NeZero s] [NeZero (4 * s)] [NeZero (s - 3)]
    [NeZero w] [NeZero Q] [Nonempty V]
    {pV : Program V} {pX : Program X} {pY : Program Y}
    {μ : PositiveRationalLaw X} {ν : PositiveRationalLaw Y}
    (hv : Generates pV (PositiveRationalLaw.uniform V).toFiniteLaw)
    (hx : Generates pX μ.toFiniteLaw)
    (hy : Generates pY ν.toFiniteLaw) (m : ℕ) :
    Generates (fullSample (q₁ := q₁) (q₂ := q₂) (s := s)
      (w := w) (Q := Q) m pV pX pY)
      (fullSampleLaw (q₁ := q₁) (q₂ := q₂) (s := s)
        (w := w) (Q := Q) (V := V) m μ ν
        (by have h := Nat.pos_of_ne_zero (NeZero.ne (s - 3)); omega)).toFiniteLaw := by
  exact generates_rational_prod
    (generates_rational_iid (generates_successorRow hy) m)
    (generates_rational_iid (generates_successorColumn hv hx) m)

end FullSample

section Table

variable {m : ℕ}

/-- Evaluate all `m²` intersections of the complete sampled labels. The
successor row chooses its `j`th pair using the successor column's `j`, and
the successor column chooses its `i`th raw row using that pair's `i`. -/
def table
    (M : TaggedColumn q₁ q₂ s Y →
      Paper2.SourceMatrix.RawRow q₁ q₂ s X
        (CurrentAdditive.EdgeSourceMatrix.Items s V) → Bool)
    (z : (Fin m → RowLabel q₁ q₂ s w Q Y) ×
      (Fin m → ColumnLabel q₁ q₂ s w Q X V)) :
    Fin m → Fin m → Bool :=
  fun i j =>
    let pair := z.1 i (z.2 j).1
    M pair.2 ((z.2 j).2 pair.1)

theorem table_entry
    (M : TaggedColumn q₁ q₂ s Y →
      Paper2.SourceMatrix.RawRow q₁ q₂ s X
        (CurrentAdditive.EdgeSourceMatrix.Items s V) → Bool)
    (z : (Fin m → RowLabel q₁ q₂ s w Q Y) ×
      (Fin m → ColumnLabel q₁ q₂ s w Q X V))
    (i j : Fin m) :
    table M z i j =
      M (z.1 i (z.2 j).1).2 ((z.2 j).2 (z.1 i (z.2 j).1).1) := rfl

end Table

section RoundedTable

variable [Fintype X] [Fintype Y] [Fintype V]

/-- The literal public alphabet cap displayed in the v38 manuscript. -/
def publicA (n s q₂ w Q p₀ : ℕ) : ℕ :=
  max 512 (max (4 * s * (n + s)) (max q₂ (max w (max Q p₀))))

/-- The literal integer form of `ceil(log₂(200 A Ndraw))`. -/
def publicBits (A Ndraw : ℕ) : ℕ := Nat.clog 2 (200 * A * Ndraw)

theorem publicBits_budget (A Ndraw : ℕ) :
    200 * A * Ndraw ≤ 2 ^ publicBits A Ndraw := by
  exact Nat.le_pow_clog (by decide : 1 < 2) (200 * A * Ndraw)

def sampledTable [NeZero q₁] [NeZero q₂] [NeZero s]
    [NeZero (4 * s)] [NeZero (s - 3)] [NeZero w] [NeZero Q]
    (m : ℕ) (pV : Program V) (pX : Program X) (pY : Program Y)
    (A Ndraw : ℕ)
    (hA : (fullSample (q₁ := q₁) (q₂ := q₂) (s := s)
      (w := w) (Q := Q) m pV pX pY).maxAlphabet ≤ A)
    (hN : (fullSample (q₁ := q₁) (q₂ := q₂) (s := s)
      (w := w) (Q := Q) m pV pX pY).maxDraws ≤ Ndraw)
    (M : TaggedColumn q₁ q₂ s Y →
      Paper2.SourceMatrix.RawRow q₁ q₂ s X
        (CurrentAdditive.EdgeSourceMatrix.Items s V) → Bool)
    (bits : CurrentAdditive.RoundedDraw.BitBlocks (publicBits A Ndraw) Ndraw) :
    Fin m → Fin m → Bool :=
  table M (CurrentAdditive.RoundedProgram.runProgram (publicBits A Ndraw) Ndraw
    ⟨fullSample (q₁ := q₁) (q₂ := q₂) (s := s)
      (w := w) (Q := Q) m pV pX pY, hA⟩ hN bits)

/-- All joint table events are within `1/200` of the exact independent
positive-rational label law, including the table's deterministic lookup. -/
theorem sampledTable_event_error_200 [NeZero q₁] [NeZero q₂]
    [NeZero s] [NeZero (4 * s)] [NeZero (s - 3)]
    [NeZero w] [NeZero Q] [Nonempty V]
    (m : ℕ) (pV : Program V) (pX : Program X) (pY : Program Y)
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (hv : Generates pV (PositiveRationalLaw.uniform V).toFiniteLaw)
    (hx : Generates pX μ.toFiniteLaw)
    (hy : Generates pY ν.toFiniteLaw)
    (A Ndraw : ℕ)
    (hA : (fullSample (q₁ := q₁) (q₂ := q₂) (s := s)
      (w := w) (Q := Q) m pV pX pY).maxAlphabet ≤ A)
    (hN : (fullSample (q₁ := q₁) (q₂ := q₂) (s := s)
      (w := w) (Q := Q) m pV pX pY).maxDraws ≤ Ndraw)
    (M : TaggedColumn q₁ q₂ s Y →
      Paper2.SourceMatrix.RawRow q₁ q₂ s X
        (CurrentAdditive.EdgeSourceMatrix.Items s V) → Bool)
    (P : (Fin m → Fin m → Bool) → Prop) :
    |(CurrentAdditive.RoundedDraw.bitBlocksLaw (publicBits A Ndraw) Ndraw).prob
      (fun bits => P (sampledTable (q₁ := q₁) (q₂ := q₂) (s := s)
        (w := w) (Q := Q) m pV pX pY A Ndraw hA hN M bits)) -
      (fullSampleLaw (q₁ := q₁) (q₂ := q₂) (s := s)
        (w := w) (Q := Q) (V := V) m μ ν
        (by have h := Nat.pos_of_ne_zero (NeZero.ne (s - 3)); omega)).toFiniteLaw.prob
          (fun z => P (table M z))| ≤ (1 : ℝ) / 200 := by
  let s0 : Paper2.RecursiveSamplingCapped.State
      ((Fin m → RowLabel q₁ q₂ s w Q Y) ×
        (Fin m → ColumnLabel q₁ q₂ s w Q X V)) A :=
    ⟨fullSample (q₁ := q₁) (q₂ := q₂) (s := s)
      (w := w) (Q := Q) m pV pX pY, hA⟩
  have h := CurrentAdditive.RoundedProgram.runProgram_event_error_200
    (publicBits A Ndraw) Ndraw s0 hN
    (publicBits_budget A Ndraw)
    {z | P (table M z)}
  have hlaw := generates_eventProb
    (generates_fullSample (q₁ := q₁) (q₂ := q₂) (s := s)
      (w := w) (Q := Q) hv hx hy m)
    {z | P (table M z)}
  change _ ≤ _ at h
  rw [hlaw] at h
  exact h

#print axioms generates_tagged
#print axioms generates_rawRows
#print axioms generates_fullSample
#print axioms sampledTable_event_error_200

end RoundedTable

end CurrentAdditive.V38OneStep
