import EthInapproximability.CurrentPaper.WeightedDuplication

/-!
# Actual matrices for the current amplification construction

Source: v8 `03-parameterized-construction.tex`, equations
`eq:paper-M1-definition`, `eq:paper-M2-M3-definition`,
`eq:paper-active-injection`, `eq:paper-B-carriers`,
`eq:paper-B-template`, `eq:paper-B-source`; and v8
`A-stage4-details.tex`, the joint-tail diagonal and input groups following
`lem:paper-weighted-blowup`.

All coordinates are zero-based. Vertex and auxiliary items have separate
finite public enumerations. An explicit public permutation sends their
concatenation to the original ordered indices of the supplied Boolean vector
family; the active rank is computed in that ORIGINAL order. The concrete
graph producer must supply its copy-major lexicographic permutation.
The source support bound is an explicit input. No balancedness,
colouring, communication lower bound, or protected-hardness premise is assumed.
This module constructs the matrices; the graph-to-vector source and the
balanced-family algorithm remain separate producers.
-/

namespace EthInapproximability.CurrentPaper.Construction

open scoped BigOperators
open Workspace.Types.CommComplexity

universe u

def qOne (a : ℕ) : ℕ := 2 ^ a - 2

def firstLength (a s : ℕ) : ℕ := qOne a + (s + 1)

theorem qOne_add_two (a : ℕ) (ha : 1 ≤ a) : qOne a + 2 = 2 ^ a := by
  have h : 2 ≤ 2 ^ a := by
    simpa using (Nat.pow_le_pow_right (by omega : 1 ≤ 2) ha)
  unfold qOne
  omega

theorem qOne_add_three (a : ℕ) (ha : 1 ≤ a) : qOne a + 3 = 2 ^ a + 1 := by
  have h := qOne_add_two a ha
  omega

/-- Original interlace coordinates occupy the first `qOne a` entries. -/
def firstCoordinate (a s : ℕ) (i : Fin (qOne a)) : Fin (firstLength a s) :=
  Fin.castAdd (s + 1) i

/-- The last `s+1` entries are the inputs reserved for graph rows. -/
def tailCoordinate (a s : ℕ) (i : Fin (s + 1)) : Fin (firstLength a s) :=
  Fin.natAdd (qOne a) i

@[simp] theorem firstCoordinate_val (a s : ℕ) (i : Fin (qOne a)) :
    (firstCoordinate a s i).val = i.val := rfl

@[simp] theorem tailCoordinate_val (a s : ℕ) (i : Fin (s + 1)) :
    (tailCoordinate a s i).val = qOne a + i.val := rfl

theorem firstCoordinate_ne_tailCoordinate (a s : ℕ) (i : Fin (qOne a))
    (j : Fin (s + 1)) : firstCoordinate a s i ≠ tailCoordinate a s j := by
  intro h
  have hv := congrArg Fin.val h
  simp only [firstCoordinate_val, tailCoordinate_val] at hv
  omega

abbrev FirstColumns (a s : ℕ) (Y : Type u) := Fin (firstLength a s) → Y
abbrev FirstRows (a : ℕ) (X : Type u) := Fin (qOne a) × X
abbrev SecondRows (a s q : ℕ) (Y : Type u) := Fin q × FirstColumns a s Y
abbrev ThirdRows (s L : ℕ) := Fin s × Fin L
abbrev ThirdColumns (a s q : ℕ) (Y : Type u) := Fin s → SecondRows a s q Y
abbrev VertexRows (nv : ℕ) (X : Type u) := Fin nv × X
abbrev AuxiliaryRows (nb : ℕ) (X : Type u) := Fin nb × X
abbrev RawRows (s L nv nb : ℕ) (X : Type u) :=
  ThirdRows s L ⊕ (VertexRows nv X ⊕ AuxiliaryRows nb X)
abbrev RawColumns (a s q : ℕ) (Y : Type u) :=
  (Fin (s + 1) → Y) × ThirdColumns a s q Y

variable {X Y : Type u}

def firstMatrix (R : X → Y → Bool) (a s : ℕ) :
    FirstRows a X → FirstColumns a s Y → Bool :=
  fun r γ => R r.2 (γ (firstCoordinate a s r.1))

/-- The family is an indexed accessor, retaining multiplicities of repeated tuples. -/
abbrev SecondFamily (a q L : ℕ) (X : Type u) := Fin L → Fin q → FirstRows a X

def secondMatrix (R : X → Y → Bool) (a s q L : ℕ)
    (family : SecondFamily a q L X) : SecondRows a s q Y → Fin L → Bool :=
  fun r ℓ => firstMatrix R a s (family ℓ r.1) r.2

def thirdMatrix (R : X → Y → Bool) (a s q L : ℕ)
    (family : SecondFamily a q L X) : ThirdRows s L → ThirdColumns a s q Y → Bool :=
  fun r c => secondMatrix R a s q L family (c r.1) r.2

@[simp] theorem firstMatrix_apply (R : X → Y → Bool) (a s : ℕ)
    (r : FirstRows a X) (γ : FirstColumns a s Y) :
    firstMatrix R a s r γ = R r.2 (γ (firstCoordinate a s r.1)) := rfl

/-- The `s+1` reserved tail entries have no effect on the first matrix. -/
theorem firstMatrix_eq_of_prefix_eq (R : X → Y → Bool) (a s : ℕ)
    (γ δ : FirstColumns a s Y)
    (h : ∀ i, γ (firstCoordinate a s i) = δ (firstCoordinate a s i))
    (r : FirstRows a X) : firstMatrix R a s r γ = firstMatrix R a s r δ :=
  congrArg (R r.2) (h r.1)

@[simp] theorem secondMatrix_apply (R : X → Y → Bool) (a s q L : ℕ)
    (family : SecondFamily a q L X) (α : Fin q) (γ : FirstColumns a s Y) (ℓ : Fin L) :
    secondMatrix R a s q L family (α, γ) ℓ =
      R (family ℓ α).2 (γ (firstCoordinate a s (family ℓ α).1)) := rfl

section ActiveRanks

variable {n q s : ℕ} (vectors : Fin n → Fin q → Bool)

def activeItems (α : Fin q) : Finset (Fin n) :=
  Finset.univ.filter (fun i => vectors i α = true)

def activeBefore (α : Fin q) (i : Fin n) : Finset (Fin n) :=
  (activeItems vectors α).filter (fun j => j < i)

def activeRank (α : Fin q) (i : Fin n) : ℕ := (activeBefore vectors α i).card

theorem activeRank_lt_card (α : Fin q) (i : Fin n) (hi : vectors i α = true) :
    activeRank vectors α i < (activeItems vectors α).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro heq
  have hm : i ∈ activeItems vectors α := by simp [activeItems, hi]
  have hb : i ∈ activeBefore vectors α i := by rw [heq]; exact hm
  simp [activeBefore] at hb

theorem activeRank_strictMono (α : Fin q) (i j : Fin n)
    (hi : vectors i α = true) (hij : i < j) :
    activeRank vectors α i < activeRank vectors α j := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro k hk
    simp only [activeBefore, Finset.mem_filter] at hk ⊢
    exact ⟨hk.1, lt_trans hk.2 hij⟩
  · intro heq
    have hm : i ∈ activeBefore vectors α j := by simp [activeBefore, activeItems, hi, hij]
    have hb : i ∈ activeBefore vectors α i := by rw [heq]; exact hm
    simp [activeBefore] at hb

/-- Public zero-based rank of an active item, not an arbitrary supplied injection. -/
def activeSlot (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (α : Fin q) (i : {i : Fin n // vectors i α = true}) : Fin s :=
  ⟨activeRank vectors α i.1, (activeRank_lt_card vectors α i.1 i.2).trans_le (cap α)⟩

@[simp] theorem activeSlot_val (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (α : Fin q) (i : {i : Fin n // vectors i α = true}) :
    (activeSlot vectors cap α i).val = (activeBefore vectors α i.1).card := rfl

theorem activeSlot_injective (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (α : Fin q) : Function.Injective (activeSlot vectors cap α) := by
  intro i j h
  have hv := congrArg Fin.val h
  apply Subtype.ext
  apply le_antisymm
  · by_contra hn
    have hlt := activeRank_strictMono vectors α j.1 i.1 j.2 (lt_of_not_ge hn)
    change activeRank vectors α i.1 = activeRank vectors α j.1 at hv
    omega
  · by_contra hn
    have hlt := activeRank_strictMono vectors α i.1 j.1 i.2 (lt_of_not_ge hn)
    change activeRank vectors α i.1 = activeRank vectors α j.1 at hv
    omega

/-- Adding one recovers the paper's one-based formula for `pi`. -/
theorem activeSlot_oneBased (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (α : Fin q) (i : {i : Fin n // vectors i α = true}) :
    (activeSlot vectors cap α i).val + 1 = 1 + (activeBefore vectors α i.1).card := by
  simp [Nat.add_comm]

end ActiveRanks

def firstBin (s : ℕ) (hs : 0 < s) : Fin s := ⟨0, hs⟩

/-- Maps concatenated row labels to the original public item order. -/
abbrev ItemOrder (nv nb : ℕ) := Fin (nv + nb) ≃ Fin (nv + nb)

def vertexIndex {nv nb : ℕ} (order : ItemOrder nv nb) (i : Fin nv) : Fin (nv + nb) :=
  order (Fin.castAdd nb i)

def auxiliaryIndex {nv nb : ℕ} (order : ItemOrder nv nb) (i : Fin nb) : Fin (nv + nb) :=
  order (Fin.natAdd nv i)

theorem vertexIndex_injective {nv nb : ℕ} (order : ItemOrder nv nb) :
    Function.Injective (vertexIndex order) := by
  intro i j h
  have heq : Fin.castAdd nb i = Fin.castAdd nb j := order.injective h
  have hv := congrArg (fun k : Fin (nv + nb) => k.val) heq
  apply Fin.ext
  exact hv

theorem auxiliaryIndex_injective {nv nb : ℕ} (order : ItemOrder nv nb) :
    Function.Injective (auxiliaryIndex order) := by
  intro i j h
  have heq : Fin.natAdd nv i = Fin.natAdd nv j := order.injective h
  have hv := congrArg (fun k : Fin (nv + nb) => k.val) heq
  apply Fin.ext
  simpa using hv

theorem vertexIndex_ne_auxiliaryIndex {nv nb : ℕ} (order : ItemOrder nv nb)
    (i : Fin nv) (j : Fin nb) : vertexIndex order i ≠ auxiliaryIndex order j := by
  intro h
  have heq : Fin.castAdd nb i = Fin.natAdd nv j := order.injective h
  have hv := congrArg (fun k : Fin (nv + nb) => k.val) heq
  change i.val = nv + j.val at hv
  omega

/-- The separate row types give exactly the paper's `T + (I × X)` carrier. -/
def rawRowEquiv (s L nv nb : ℕ) (order : ItemOrder nv nb) :
    RawRows s L nv nb X ≃ ThirdRows s L ⊕ (Fin (nv + nb) × X) :=
  Equiv.sumCongr (Equiv.refl _)
    ((Equiv.sumProdDistrib (Fin nv) (Fin nb) X).symm.trans
      (Equiv.prodCongr (finSumFinEquiv.trans order) (Equiv.refl X)))

@[simp] theorem rawRowEquiv_vertex (s L nv nb : ℕ) (order : ItemOrder nv nb)
    (i : Fin nv) (x : X) :
    rawRowEquiv s L nv nb order (Sum.inr (Sum.inl (i, x))) =
      Sum.inr (vertexIndex order i, x) := rfl

@[simp] theorem rawRowEquiv_auxiliary (s L nv nb : ℕ) (order : ItemOrder nv nb)
    (i : Fin nb) (x : X) :
    rawRowEquiv s L nv nb order (Sum.inr (Sum.inr (i, x))) =
      Sum.inr (auxiliaryIndex order i, x) := rfl

def aligned {a s q : ℕ} (hs : 0 < s) (c : RawColumns a s q Y) : Prop :=
  ∀ p, (c.2 p).1 = (c.2 (firstBin s hs)).1

instance alignedDecidable {a s q : ℕ} (hs : 0 < s) (c : RawColumns a s q Y) :
    Decidable (aligned hs c) := by unfold aligned; infer_instance

def graphEntry (R : X → Y → Bool) {a s q n : ℕ} (hs : 0 < s)
    (vectors : Fin n → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (i : Fin n) (x : X) (c : RawColumns a s q Y) : Bool :=
  if aligned hs c then
    let α := (c.2 (firstBin s hs)).1
    if hi : vectors i α = true then
      R x (c.1 (Fin.castAdd 1 (activeSlot vectors cap α ⟨i, hi⟩)))
    else R x (c.1 (Fin.last s))
  else R x (c.1 (Fin.last s))

theorem activeSlot_ne_inactive {n q s : ℕ} (vectors : Fin n → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (α : Fin q) (i : {i : Fin n // vectors i α = true}) :
    Fin.castAdd 1 (activeSlot vectors cap α i) ≠ Fin.last s := by
  intro h
  have heq := congrArg (fun k : Fin (s + 1) => k.val) h
  have hlt := (activeSlot vectors cap α i).isLt
  change (activeSlot vectors cap α i).val = s at heq
  omega

theorem graphEntry_nonaligned (R : X → Y → Bool) {a s q n : ℕ} (hs : 0 < s)
    (vectors : Fin n → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (i : Fin n) (x : X) (c : RawColumns a s q Y) (h : ¬ aligned hs c) :
    graphEntry R hs vectors cap i x c = R x (c.1 (Fin.last s)) := by
  simp [graphEntry, h]

theorem graphEntry_active (R : X → Y → Bool) {a s q n : ℕ} (hs : 0 < s)
    (vectors : Fin n → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (i : Fin n) (x : X) (c : RawColumns a s q Y) (h : aligned hs c)
    (hi : vectors i (c.2 (firstBin s hs)).1 = true) :
    graphEntry R hs vectors cap i x c =
      R x (c.1 (Fin.castAdd 1
        (activeSlot vectors cap (c.2 (firstBin s hs)).1 ⟨i, hi⟩))) := by
  simp [graphEntry, h, hi]

theorem graphEntry_inactive (R : X → Y → Bool) {a s q n : ℕ} (hs : 0 < s)
    (vectors : Fin n → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (i : Fin n) (x : X) (c : RawColumns a s q Y)
    (hi : vectors i (c.2 (firstBin s hs)).1 = false) :
    graphEntry R hs vectors cap i x c = R x (c.1 (Fin.last s)) := by
  simp [graphEntry, hi]

/-- The three raw row types are literal disjoint summands. -/
def rawMatrix (R : X → Y → Bool) (a s q L nv nb : ℕ) (hs : 0 < s)
    (family : SecondFamily a q L X) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s) :
    RawRows s L nv nb X → RawColumns a s q Y → Bool
  | .inl r, c => thirdMatrix R a s q L family r c.2
  | .inr (.inl r), c => graphEntry R hs vectors cap (vertexIndex order r.1) r.2 c
  | .inr (.inr r), c => graphEntry R hs vectors cap (auxiliaryIndex order r.1) r.2 c

@[simp] theorem rawMatrix_template (R : X → Y → Bool) (a s q L nv nb : ℕ)
    (hs : 0 < s) (family : SecondFamily a q L X) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (p : Fin s) (ℓ : Fin L) (c : RawColumns a s q Y) :
    rawMatrix R a s q L nv nb hs family order vectors cap (Sum.inl (p, ℓ)) c =
      secondMatrix R a s q L family (c.2 p) ℓ := rfl

@[simp] theorem rawMatrix_vertex (R : X → Y → Bool) (a s q L nv nb : ℕ)
    (hs : 0 < s) (family : SecondFamily a q L X) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (i : Fin nv) (x : X) (c : RawColumns a s q Y) :
    rawMatrix R a s q L nv nb hs family order vectors cap (Sum.inr (Sum.inl (i, x))) c =
      graphEntry R hs vectors cap (vertexIndex order i) x c := rfl

@[simp] theorem rawMatrix_auxiliary (R : X → Y → Bool) (a s q L nv nb : ℕ)
    (hs : 0 < s) (family : SecondFamily a q L X) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (i : Fin nb) (x : X) (c : RawColumns a s q Y) :
    rawMatrix R a s q L nv nb hs family order vectors cap (Sum.inr (Sum.inr (i, x))) c =
      graphEntry R hs vectors cap (auxiliaryIndex order i) x c := rfl

/-- The diagonal uses the unused tail of the very SAME tuple as every bin. -/
def diagonal {a s q : ℕ} (d : SecondRows a s q Y) : RawColumns a s q Y :=
  (fun i => d.2 (tailCoordinate a s i), fun _ => d)

@[simp] theorem diagonal_bin {a s q : ℕ} (d : SecondRows a s q Y) (p : Fin s) :
    (diagonal d).2 p = d := rfl

@[simp] theorem diagonal_tail {a s q : ℕ} (d : SecondRows a s q Y) (i : Fin (s + 1)) :
    (diagonal d).1 i = d.2 (tailCoordinate a s i) := rfl

theorem diagonal_injective {a s q : ℕ} (hs : 0 < s) :
    Function.Injective (diagonal (a := a) (s := s) (q := q) (Y := Y)) := by
  intro d e h
  exact congrArg (fun c : RawColumns a s q Y => c.2 (firstBin s hs)) h

theorem diagonal_aligned {a s q : ℕ} (hs : 0 < s) (d : SecondRows a s q Y) :
    aligned hs (diagonal d) := fun _ => rfl

/-- An active graph row uses its own coordinate in the diagonal's common tuple. -/
theorem graphEntry_diagonal_active (R : X → Y → Bool) {a s q n : ℕ}
    (hs : 0 < s) (vectors : Fin n → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (α : Fin q) (γ : FirstColumns a s Y) (i : Fin n) (hi : vectors i α = true)
    (x : X) :
    graphEntry R hs vectors cap i x (diagonal (α, γ)) =
      R x (γ (tailCoordinate a s (Fin.castAdd 1 (activeSlot vectors cap α ⟨i, hi⟩)))) := by
  simp [graphEntry, diagonal, hi, aligned]

/-- Inactive graph rows use the final unused coordinate of that same tuple. -/
theorem graphEntry_diagonal_inactive (R : X → Y → Bool) {a s q n : ℕ}
    (hs : 0 < s) (vectors : Fin n → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (α : Fin q) (γ : FirstColumns a s Y) (i : Fin n) (hi : vectors i α = false)
    (x : X) :
    graphEntry R hs vectors cap i x (diagonal (α, γ)) =
      R x (γ (tailCoordinate a s (Fin.last s))) := by
  simp [graphEntry, diagonal, hi, aligned]

theorem secondRows_nonempty [Nonempty Y] (a s q : ℕ) (hq : 0 < q) :
    Nonempty (SecondRows a s q Y) := by
  exact ⟨(⟨0, hq⟩, fun _ => Classical.choice (inferInstance : Nonempty Y))⟩

section Cardinalities

variable [Fintype X] [Fintype Y]

@[simp] theorem card_firstRows (a : ℕ) :
    Fintype.card (FirstRows a X) = qOne a * Fintype.card X := by
  simp [FirstRows]

@[simp] theorem card_firstColumns (a s : ℕ) :
    Fintype.card (FirstColumns a s Y) = Fintype.card Y ^ firstLength a s := by
  simp [FirstColumns]

@[simp] theorem card_secondRows (a s q : ℕ) :
    Fintype.card (SecondRows a s q Y) = q * Fintype.card Y ^ firstLength a s := by
  simp [SecondRows]

@[simp] theorem card_thirdRows (s L : ℕ) :
    Fintype.card (ThirdRows s L) = s * L := by simp [ThirdRows]

@[simp] theorem card_thirdColumns (a s q : ℕ) :
    Fintype.card (ThirdColumns a s q Y) =
      (q * Fintype.card Y ^ firstLength a s) ^ s := by
  simp [ThirdColumns]

@[simp] theorem card_rawRows (s L nv nb : ℕ) :
    Fintype.card (RawRows s L nv nb X) = s * L + (nv + nb) * Fintype.card X := by
  simp [RawRows, ThirdRows, VertexRows, AuxiliaryRows]
  ring

@[simp] theorem card_rawColumns (a s q : ℕ) :
    Fintype.card (RawColumns a s q Y) = Fintype.card Y ^ (s + 1) *
      (q * Fintype.card Y ^ firstLength a s) ^ s := by
  simp [RawColumns, ThirdColumns]

/-- The formerly abstract uniform multiplicity is fixed to the paper's value. -/
def uniformCopies (a s q : ℕ) : ℕ := Fintype.card (SecondRows a s q Y) ^ s

theorem uniformCopies_pos [Nonempty Y] (a s q : ℕ) (hq : 0 < q) :
    0 < uniformCopies (Y := Y) a s q := by
  letI := secondRows_nonempty (Y := Y) a s q hq
  exact pow_pos Fintype.card_pos _

/-- `ULift` only aligns universes; it changes neither input labels nor cardinality. -/
abbrev TemplateSupport (s L : ℕ) := ULift.{u} (ThirdRows s L)

abbrev ProtectedRows (s L nv nb : ℕ) (X : Type u) [Fintype X] :=
  WeightedDuplication.Rows (RawRows s L nv nb X) (TemplateSupport.{u} s L)
    (VertexRows nv X) (AuxiliaryRows nb X)

abbrev ProtectedColumns (a s q : ℕ) (Y : Type u) [Fintype Y] :=
  WeightedDuplication.Columns (RawColumns a s q Y) (SecondRows a s q Y)
    (uniformCopies (Y := Y) a s q)

/-- `N` is the actual transpose of the two-support labelled duplication of `B`. -/
def protectedMatrix (R : X → Y → Bool) (a s q L nv nb : ℕ) (hs : 0 < s)
    (family : SecondFamily a q L X) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s) :
    ProtectedColumns a s q Y → ProtectedRows s L nv nb X → Bool :=
  WeightedDuplication.transposedMatrix (rawMatrix R a s q L nv nb hs family order vectors cap)
    (fun r : TemplateSupport.{u} s L => Sum.inl r.down)
    (fun r => Sum.inr (Sum.inl r)) (fun r => Sum.inr (Sum.inr r))
    diagonal (uniformCopies (Y := Y) a s q)

theorem card_protectedColumns (a s q : ℕ) :
    Fintype.card (ProtectedColumns a s q Y) =
      184 * (Fintype.card Y ^ (s + 1) *
        (q * Fintype.card Y ^ firstLength a s) ^ s) *
      (q * Fintype.card Y ^ firstLength a s) *
      (q * Fintype.card Y ^ firstLength a s) ^ s := by
  rw [WeightedDuplication.card_columns]
  simp [uniformCopies]

theorem card_protectedRows (s L nv nb : ℕ) :
    Fintype.card (ProtectedRows s L nv nb X) =
      2 ^ 22 * (s * L + (nv + nb) * Fintype.card X) *
      (s * L) * (nv * Fintype.card X) * (nb * Fintype.card X) := by
  rw [WeightedDuplication.card_rows]
  rw [card_rawRows]
  simp only [TemplateSupport, ThirdRows, VertexRows, AuxiliaryRows,
    Fintype.card_ulift, Fintype.card_prod, Fintype.card_fin]

theorem D_protectedMatrix [Nonempty X] [Nonempty Y]
    (R : X → Y → Bool) (a s q L nv nb : ℕ) (hs : 0 < s) (hq : 0 < q)
    (hL : 0 < L) (hv : 0 < nv) (hb : 0 < nb)
    (family : SecondFamily a q L X) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s) :
    D (protectedMatrix R a s q L nv nb hs family order vectors cap) =
      D (rawMatrix R a s q L nv nb hs family order vectors cap) := by
  letI : Nonempty (Fin s) := ⟨⟨0, hs⟩⟩
  letI : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  letI : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  letI : Nonempty (Fin nv) := ⟨⟨0, hv⟩⟩
  letI : Nonempty (Fin nb) := ⟨⟨0, hb⟩⟩
  apply WeightedDuplication.D_transposedMatrix
  exact pow_pos Fintype.card_pos _

end Cardinalities

end EthInapproximability.CurrentPaper.Construction
