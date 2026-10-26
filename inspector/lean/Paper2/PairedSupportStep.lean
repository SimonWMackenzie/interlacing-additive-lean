import Paper2.SourceSupportStep

/-!
# Independently heavy paths for paired ordinary and foreign supports

Frozen v12, Section 5, `res:paired`. A pair consists of two different
tagged coordinate blocks. Each support chooses its own heavy query fibre.
Equal choices keep the pair; different choices turn it into two singles.
In particular, a separated foreign singleton remains counted. This is not
the one-support, two-large-halves transition used by the source NO proof.
-/

namespace Paper2.PairedSupportStep

open SourceSupportStep

variable {I W : Type*}

/-- Both tagged blocks of each paired coordinate. -/
def pairBlocks (P : Finset I) : Finset (Bool × I) := Finset.univ.product P

/-- Single blocks never overlap either member of a pair at the same node. -/
def Valid (S : Finset (Bool × I)) (P : Finset I) : Prop :=
  ∀ i ∈ P, ∀ tag : Bool, (tag, i) ∉ S

/-- Every active block, retaining both tags even when their labels agree. -/
noncomputable def active (S : Finset (Bool × I)) (P : Finset I) : Finset (Bool × I) := by
  classical
  exact S ∪ pairBlocks P

/-- One counted block per pair, together with all already separated singles. -/
noncomputable def primary (S : Finset (Bool × I)) (P : Finset I) : Finset (Bool × I) := by
  classical
  exact S ∪ P.image (fun i => (false, i))

@[simp] theorem mem_pairBlocks (P : Finset I) (a : Bool × I) :
    a ∈ pairBlocks P ↔ a.2 ∈ P := by
  simp [pairBlocks]

@[simp] theorem mem_active (S : Finset (Bool × I)) (P : Finset I) (a : Bool × I) :
    a ∈ active S P ↔ a ∈ S ∨ a.2 ∈ P := by
  classical
  simp [active]

@[simp] theorem mem_primary (S : Finset (Bool × I)) (P : Finset I) (a : Bool × I) :
    a ∈ primary S P ↔ a ∈ S ∨ (a.1 = false ∧ a.2 ∈ P) := by
  classical
  rcases a with ⟨tag, i⟩
  cases tag <;> simp [primary]

variable [Fintype W]

/-- The independently chosen child of one actual tagged support. -/
noncomputable def choice (μ : FiniteLaw W) (F : (Bool × I) → Finset W)
    (query : (Bool × I) → W → Bool) (a : Bool × I) : Bool :=
  heavyBit μ (F a) (query a)

/-- Pairs split only because their two independently heavy bits differ. -/
noncomputable def splitPairs (μ : FiniteLaw W) (P : Finset I)
    (F : (Bool × I) → Finset W) (query : (Bool × I) → W → Bool) : Finset I := by
  classical
  exact P.filter fun i => choice μ F query (false, i) ≠ choice μ F query (true, i)

noncomputable def childPairs (μ : FiniteLaw W) (P : Finset I)
    (F : (Bool × I) → Finset W) (query : (Bool × I) → W → Bool) (b : Bool) : Finset I := by
  classical
  exact P.filter fun i => choice μ F query (false, i) = b ∧ choice μ F query (true, i) = b

noncomputable def childSingles (μ : FiniteLaw W) (S : Finset (Bool × I)) (P : Finset I)
    (F : (Bool × I) → Finset W) (query : (Bool × I) → W → Bool)
    (b : Bool) : Finset (Bool × I) := by
  classical
  exact (S.filter fun a => choice μ F query a = b) ∪
    ((pairBlocks (splitPairs μ P F query)).filter fun a => choice μ F query a = b)

/-- The retained support is its actual word fibre in the chosen child. -/
noncomputable def childSupport (F : (Bool × I) → Finset W)
    (query : (Bool × I) → W → Bool) (b : Bool) (a : Bool × I) : Finset W :=
  fibre (F a) (query a) b

@[simp] theorem mem_splitPairs (μ : FiniteLaw W) (P : Finset I)
    (F : (Bool × I) → Finset W) (query : (Bool × I) → W → Bool) (i : I) :
    i ∈ splitPairs μ P F query ↔
      i ∈ P ∧ choice μ F query (false, i) ≠ choice μ F query (true, i) := by
  classical
  simp [splitPairs]

@[simp] theorem mem_childPairs (μ : FiniteLaw W) (P : Finset I)
    (F : (Bool × I) → Finset W) (query : (Bool × I) → W → Bool) (b : Bool) (i : I) :
    i ∈ childPairs μ P F query b ↔
      i ∈ P ∧ choice μ F query (false, i) = b ∧ choice μ F query (true, i) = b := by
  classical
  simp [childPairs]

@[simp] theorem mem_childSingles (μ : FiniteLaw W) (S : Finset (Bool × I)) (P : Finset I)
    (F : (Bool × I) → Finset W) (query : (Bool × I) → W → Bool)
    (b : Bool) (a : Bool × I) :
    a ∈ childSingles μ S P F query b ↔
      (a ∈ S ∨ a.2 ∈ splitPairs μ P F query) ∧ choice μ F query a = b := by
  classical
  simp only [childSingles, Finset.mem_union, Finset.mem_filter, mem_pairBlocks]
  tauto

omit [Fintype W] in
@[simp] theorem mem_childSupport (F : (Bool × I) → Finset W)
    (query : (Bool × I) → W → Bool) (b : Bool) (a : Bool × I) (w : W) :
    w ∈ childSupport F query b a ↔ w ∈ F a ∧ query a w = b :=
  mem_fibre (F a) (query a) b w

/-- Each active tagged block follows exactly its own independently heavy bit. -/
theorem child_active_iff (μ : FiniteLaw W) (S : Finset (Bool × I)) (P : Finset I)
    (F : (Bool × I) → Finset W) (query : (Bool × I) → W → Bool)
    (b : Bool) (a : Bool × I) :
    a ∈ active (childSingles μ S P F query b) (childPairs μ P F query b) ↔
      a ∈ active S P ∧ choice μ F query a = b := by
  rcases a with ⟨tag, i⟩
  cases tag <;> cases b <;>
    cases h0 : choice μ F query (false, i) <;>
    cases h1 : choice μ F query (true, i) <;> simp [h0, h1]

theorem child_valid (μ : FiniteLaw W) (S : Finset (Bool × I)) (P : Finset I)
    (F : (Bool × I) → Finset W) (query : (Bool × I) → W → Bool)
    (b : Bool) (hv : Valid S P) :
    Valid (childSingles μ S P F query b) (childPairs μ P F query b) := by
  intro i hi tag hs
  obtain ⟨hiP, h0, h1⟩ := (mem_childPairs μ P F query b i).mp hi
  obtain ⟨hs | hsplit, _⟩ := (mem_childSingles μ S P F query b (tag, i)).mp hs
  · exact hv i hiP tag hs
  · exact ((mem_splitPairs μ P F query i).mp hsplit).2 (h0.trans h1.symm)

theorem child_active_subset (μ : FiniteLaw W) (S : Finset (Bool × I)) (P : Finset I)
    (F : (Bool × I) → Finset W) (query : (Bool × I) → W → Bool) (b : Bool) :
    active (childSingles μ S P F query b) (childPairs μ P F query b) ⊆ active S P := by
  intro a ha
  exact ((child_active_iff μ S P F query b a).mp ha).1

theorem childPairs_subset (μ : FiniteLaw W) (P : Finset I)
    (F : (Bool × I) → Finset W) (query : (Bool × I) → W → Bool) (b : Bool) :
    childPairs μ P F query b ⊆ P := by
  intro i hi
  exact ((mem_childPairs μ P F query b i).mp hi).1

omit [Fintype W] in
theorem childSupport_subset (F : (Bool × I) → Finset W)
    (query : (Bool × I) → W → Bool) (b : Bool) (a : Bool × I) :
    childSupport F query b a ⊆ F a :=
  fibre_subset (F a) (query a) b

/-- A parent floor of twice the next floor is retained independently by
every active member, including a foreign singleton from a split pair. -/
theorem child_floor (μ : FiniteLaw W) (S : Finset (Bool × I)) (P : Finset I)
    (F : (Bool × I) → Finset W) (query : (Bool × I) → W → Bool)
    (t : ℝ) (b : Bool) (hfloor : ∀ a ∈ active S P, 2 * t ≤ mass μ (F a)) :
    ∀ a ∈ active (childSingles μ S P F query b) (childPairs μ P F query b),
      t ≤ mass μ (childSupport F query b a) := by
  intro a ha
  obtain ⟨ha, hb⟩ := (child_active_iff μ S P F query b a).mp ha
  change t ≤ mass μ (fibre (F a) (query a) b)
  rw [← hb]
  exact heavy_floor μ (F a) (query a) t (hfloor a ha)

/-- Every routed word uses the same actual column label and reaches the
chosen Bob child; the map does not depend on the row input. -/
theorem child_reaches {C : Type*} (μ : FiniteLaw W)
    (S : Finset (Bool × I)) (P : Finset I) (F : (Bool × I) → Finset W)
    (input : (Bool × I) → W → C) (query : C → Bool) (U : Set C) (b : Bool)
    (hret : ∀ a ∈ active S P, ∀ w ∈ F a, input a w ∈ U) :
    ∀ a ∈ active (childSingles μ S P F (fun a w => query (input a w)) b)
      (childPairs μ P F (fun a w => query (input a w)) b),
      ∀ w ∈ childSupport F (fun a w => query (input a w)) b a,
        input a w ∈ U ∧ query (input a w) = b := by
  intro a ha w hw
  obtain ⟨ha, _⟩ := (child_active_iff μ S P F _ b a).mp ha
  obtain ⟨hw, hb⟩ := (mem_childSupport F _ b a w).mp hw
  exact ⟨hret a ha w hw, hb⟩

theorem childSupport_nonempty (μ : FiniteLaw W) (S : Finset (Bool × I)) (P : Finset I)
    (F : (Bool × I) → Finset W) (query : (Bool × I) → W → Bool)
    (t : ℝ) (b : Bool) (ht : 0 < t)
    (hfloor : ∀ a ∈ active S P, 2 * t ≤ mass μ (F a)) :
    ∀ a ∈ active (childSingles μ S P F query b) (childPairs μ P F query b),
      (childSupport F query b a).Nonempty := by
  intro a ha
  have hf := child_floor μ S P F query t b hfloor a ha
  by_contra hn
  have he := Finset.not_nonempty_iff_eq_empty.mp hn
  simp [he, mass] at hf
  linarith

end Paper2.PairedSupportStep
