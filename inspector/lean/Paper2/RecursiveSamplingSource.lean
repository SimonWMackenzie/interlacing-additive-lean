import Paper2.RecursiveSamplingLaws
import Paper2.RecursiveSamplingMixtures

/-!
# Local generators for the actual protected source labels

Frozen v12 Appendix D, lines 30--51. These programs build one word, template,
or tagged source label by recursive calls to the supplied base generator.
They never draw uniformly from, or enumerate, a complete product carrier.
The exact law proofs below identify the generated labels with `SourceLaws`.
-/

namespace Paper2.RecursiveSampling

open SourceMatrix RecursiveSamplingProgram RecursiveSamplingLaws

variable {X Y V A : Type*} {q₁ q₂ s : ℕ}

def uniform (n : ℕ) [NeZero n] : Program (Fin n) :=
  Program.uniform n (Nat.pos_of_ne_zero (NeZero.ne n))

def outer [NeZero q₂] (p : Program Y) : Program (OuterColumn q₁ q₂ s Y) :=
  prod (uniform q₂) (iid p (q₁ + s + 1))

def raw [NeZero q₂] (p : Program Y) : Program (RawColumn q₁ q₂ s Y) :=
  prod (iid p (s + 1)) (iid (outer p) s)

def fixedTail [NeZero q₂] (p : Program Y) :
    Program (Fin s → OuterColumn q₁ q₂ s Y) := iid (outer p) s

/-- The fixed tail itself is public data, supplied by `RecursiveDefaults`;
the fixed-tail tag samples only its independent outer-column tuple. -/
def tagged [NeZero q₂] (p : Program Y) : Program (TaggedColumn q₁ q₂ s Y) :=
  .draw 256 (by decide) fun t =>
    if t.val < 254 then Program.map TaggedColumn.unrestricted (raw p)
    else if t.val = 254 then Program.map TaggedColumn.fixedTail (fixedTail p)
    else Program.map TaggedColumn.diagonal (outer p)

def template [NeZero q₁] (p : Program X) : Program (Template q₁ q₂ X) :=
  iid (prod (uniform q₁) p) q₂

def templateRow [NeZero q₁] [NeZero s] (p : Program X) :
    Program (Fin s × Template q₁ q₂ X) := prod (uniform s) (template p)

def itemRow (labels : Program V) (p : Program X) : Program (V × X) := prod labels p

/-- Template, vertex and auxiliary choices use the exact denominator 512.
The item-label programs are independent of the generated base row. -/
def rows [NeZero q₁] [NeZero s] (vertices : Program V) (auxiliaries : Program A)
    (p : Program X) : Program (RawRow q₁ q₂ s X (V ⊕ A)) :=
  .draw 512 (by decide) fun t =>
    if t.val < 510 then Program.map Sum.inl (templateRow p)
    else if t.val = 510 then
      Program.map (fun k => Sum.inr (Sum.inl k.1, k.2)) (itemRow vertices p)
    else Program.map (fun k => Sum.inr (Sum.inr k.1, k.2)) (itemRow auxiliaries p)

section Laws

variable [Fintype X] [Fintype Y] [Fintype V] [Fintype A]

private theorem expect_if {B : Type*} (h : Prop) [Decidable h]
    (p q : Program B) (f : B → ℝ) :
    Program.expect (if h then p else q) f =
      if h then Program.expect p f else Program.expect q f := by
  split_ifs <;> rfl

theorem generates_outer [NeZero q₂] {p : Program Y} {ν : PositiveRationalLaw Y}
    (hp : Generates p ν.toFiniteLaw) :
    Generates (outer (q₁ := q₁) (q₂ := q₂) (s := s) p)
      (SourceLaws.outerLaw ν q₁ q₂ s).toFiniteLaw :=
  generates_rational_prod (generates_uniform q₂)
    (generates_rational_iid hp (q₁ + s + 1))

theorem generates_raw [NeZero q₂] {p : Program Y} {ν : PositiveRationalLaw Y}
    (hp : Generates p ν.toFiniteLaw) :
    Generates (raw (q₁ := q₁) (q₂ := q₂) (s := s) p)
      (SourceLaws.rawLaw ν q₁ q₂ s).toFiniteLaw :=
  generates_rational_prod (generates_rational_iid hp (s + 1))
    (generates_rational_iid (generates_outer hp) s)

theorem generates_fixedTail [NeZero q₂] {p : Program Y} {ν : PositiveRationalLaw Y}
    (hp : Generates p ν.toFiniteLaw) :
    Generates (fixedTail (q₁ := q₁) (q₂ := q₂) (s := s) p)
      (SourceLaws.fixedTailLaw ν q₁ q₂ s).toFiniteLaw :=
  generates_rational_iid (generates_outer hp) s

theorem generates_tagged [NeZero q₂] {p : Program Y} {ν : PositiveRationalLaw Y}
    (hp : Generates p ν.toFiniteLaw) :
    Generates (tagged (q₁ := q₁) (q₂ := q₂) (s := s) p)
      (SourceLaws.taggedLaw ν q₁ q₂ s).toFiniteLaw := by
  intro f
  rw [tagged, Program.expect_draw]
  simp only [expect_if, Program.expect_map]
  simp only [Nat.cast_ofNat]
  rw [RecursiveSamplingMixtures.tagged_ticket_average,
    generates_raw hp, generates_fixedTail hp, generates_outer hp]
  exact (RecursiveSamplingMixtures.tagged_expect ν q₁ q₂ s f).symm

theorem generates_template [NeZero q₁] {p : Program X} {μ : PositiveRationalLaw X}
    (hp : Generates p μ.toFiniteLaw) :
    Generates (template (q₁ := q₁) (q₂ := q₂) p)
      (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw :=
  generates_rational_iid (generates_rational_prod (generates_uniform q₁) hp) q₂

theorem generates_templateRow [NeZero q₁] [NeZero s]
    {p : Program X} {μ : PositiveRationalLaw X} (hp : Generates p μ.toFiniteLaw) :
    Generates (templateRow (q₁ := q₁) (q₂ := q₂) (s := s) p)
      (SourceLaws.templateRowLaw μ q₁ q₂ s).toFiniteLaw :=
  generates_rational_prod (generates_uniform s) (generates_template hp)

theorem generates_itemRow [Nonempty V] {p : Program X} {μ : PositiveRationalLaw X}
    {labels : Program V} (hl : Generates labels (PositiveRationalLaw.uniform V).toFiniteLaw)
    (hp : Generates p μ.toFiniteLaw) :
    Generates (itemRow labels p) (SourceLaws.itemRowLaw μ V).toFiniteLaw :=
  generates_rational_prod hl hp

theorem generates_rows [NeZero q₁] [NeZero s] [Nonempty V] [Nonempty A]
    {p : Program X} {μ : PositiveRationalLaw X} {vertices : Program V} {auxiliaries : Program A}
    (hv : Generates vertices (PositiveRationalLaw.uniform V).toFiniteLaw)
    (ha : Generates auxiliaries (PositiveRationalLaw.uniform A).toFiniteLaw)
    (hp : Generates p μ.toFiniteLaw) :
    Generates (rows (q₁ := q₁) (q₂ := q₂) (s := s) vertices auxiliaries p)
      (SourceLaws.rowLaw μ q₁ q₂ s).toFiniteLaw := by
  intro f
  rw [rows, Program.expect_draw]
  simp only [expect_if, Program.expect_map]
  simp only [Nat.cast_ofNat]
  rw [RecursiveSamplingMixtures.row_ticket_average,
    generates_templateRow hp, generates_itemRow hv hp, generates_itemRow ha hp]
  exact (RecursiveSamplingMixtures.row_expect μ q₁ q₂ s f).symm

end Laws

theorem maxDraws_outer_le [NeZero q₂] (p : Program Y) :
    Program.maxDraws (outer (q₁ := q₁) (q₂ := q₂) (s := s) p) ≤
      1 + (q₁ + s + 1) * Program.maxDraws p := by
  exact (maxDraws_prod_le _ _).trans (by
    simpa only [uniform, Program.maxDraws_uniform] using
      Nat.add_le_add_left (maxDraws_iid_le p (q₁ + s + 1)) 1)

theorem maxDraws_raw_le [NeZero q₂] (p : Program Y) :
    Program.maxDraws (raw (q₁ := q₁) (q₂ := q₂) (s := s) p) ≤
      (s + 1) * Program.maxDraws p + s * (1 + (q₁ + s + 1) * Program.maxDraws p) :=
  (maxDraws_prod_le _ _).trans (Nat.add_le_add (maxDraws_iid_le p (s + 1))
    ((maxDraws_iid_le _ s).trans (Nat.mul_le_mul_left s (maxDraws_outer_le p))))

theorem maxDraws_tagged_le [NeZero q₂] (hs : 1 ≤ s) (p : Program Y) :
    Program.maxDraws (tagged (q₁ := q₁) (q₂ := q₂) (s := s) p) ≤
      1 + s + ((s + 1) + s * (q₁ + s + 1)) * Program.maxDraws p := by
  let d := Program.maxDraws p
  have hraw := maxDraws_raw_le (q₁ := q₁) (q₂ := q₂) (s := s) p
  have hfixed : Program.maxDraws (fixedTail (q₁ := q₁) (q₂ := q₂) (s := s) p) ≤
      s * (1 + (q₁ + s + 1) * d) :=
    (maxDraws_iid_le _ s).trans (Nat.mul_le_mul_left s (maxDraws_outer_le p))
  have hout := maxDraws_outer_le (q₁ := q₁) (q₂ := q₂) (s := s) p
  have hsup : Finset.univ.sup (fun t : Fin 256 => Program.maxDraws
      (if t.val < 254 then Program.map TaggedColumn.unrestricted (raw (q₁ := q₁) (q₂ := q₂) (s := s) p)
       else if t.val = 254 then Program.map TaggedColumn.fixedTail (fixedTail (q₁ := q₁) (q₂ := q₂) (s := s) p)
       else Program.map TaggedColumn.diagonal (outer (q₁ := q₁) (q₂ := q₂) (s := s) p))) ≤
        s + ((s + 1) + s * (q₁ + s + 1)) * d := by
    apply Finset.sup_le
    intro t _
    split_ifs <;> rw [Program.maxDraws_map]
    · nlinarith
    · nlinarith
    · have hm : 1 + (q₁ + s + 1) * d ≤ s * (1 + (q₁ + s + 1) * d) :=
        Nat.le_mul_of_pos_left _ (by omega)
      nlinarith
  change 1 + _ ≤ _
  exact (Nat.add_le_add_left hsup 1).trans (by dsimp only [d]; omega)

theorem maxDraws_templateRow_le [NeZero q₁] [NeZero s] (p : Program X) :
    Program.maxDraws (templateRow (q₁ := q₁) (q₂ := q₂) (s := s) p) ≤
      1 + q₂ * (1 + Program.maxDraws p) := by
  have hi : Program.maxDraws (template (q₁ := q₁) (q₂ := q₂) p) ≤
      q₂ * (1 + Program.maxDraws p) :=
    (maxDraws_iid_le _ q₂).trans (Nat.mul_le_mul_left q₂ (by
      simpa only [uniform, Program.maxDraws_uniform] using maxDraws_prod_le (uniform q₁) p))
  exact (maxDraws_prod_le _ _).trans (by
    simpa only [uniform, Program.maxDraws_uniform] using Nat.add_le_add_left hi 1)

theorem maxDraws_rows_le [NeZero q₁] [NeZero q₂] [NeZero s]
    (vertices : Program V) (auxiliaries : Program A) (p : Program X)
    (hv : Program.maxDraws vertices ≤ 2) (ha : Program.maxDraws auxiliaries ≤ 2) :
    Program.maxDraws (rows (q₁ := q₁) (q₂ := q₂) (s := s) vertices auxiliaries p) ≤
      3 + q₂ * (1 + Program.maxDraws p) := by
  have hq : 1 ≤ q₂ := Nat.pos_of_ne_zero (NeZero.ne q₂)
  have ht := maxDraws_templateRow_le (q₁ := q₁) (q₂ := q₂) (s := s) p
  have hvp : Program.maxDraws (itemRow vertices p) ≤ 2 + Program.maxDraws p :=
    (maxDraws_prod_le _ _).trans (Nat.add_le_add_right hv _)
  have hap : Program.maxDraws (itemRow auxiliaries p) ≤ 2 + Program.maxDraws p :=
    (maxDraws_prod_le _ _).trans (Nat.add_le_add_right ha _)
  have hm : 1 + Program.maxDraws p ≤ q₂ * (1 + Program.maxDraws p) :=
    Nat.le_mul_of_pos_left _ (by omega)
  change 1 + Finset.univ.sup _ ≤ _
  suffices hh : Finset.univ.sup (fun t : Fin 512 => Program.maxDraws
      (if t.val < 510 then Program.map Sum.inl (templateRow (q₁ := q₁) (q₂ := q₂) (s := s) p)
       else if t.val = 510 then
         Program.map (fun k => Sum.inr (Sum.inl k.1, k.2)) (itemRow vertices p)
       else Program.map (fun k => Sum.inr (Sum.inr k.1, k.2)) (itemRow auxiliaries p))) ≤
        2 + q₂ * (1 + Program.maxDraws p) by
    simpa only [← Nat.add_assoc] using Nat.add_le_add_left hh 1
  apply Finset.sup_le
  intro t _
  split_ifs <;> rw [Program.maxDraws_map] <;> omega

end Paper2.RecursiveSampling
