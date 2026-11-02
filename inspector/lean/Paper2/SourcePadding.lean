import Mathlib

/-!
# Inactive padding and exact coordinate repetition

Source: frozen Paper 2 v12, source item witness argument (T11).

Padding adds coordinates with no active items.  Repetition makes labelled
copies of every coordinate.  Both operations preserve a YES assignment;
the number of witness coordinates is unchanged by padding and is multiplied
exactly by the repetition count.  Constructors never inspect a colouring.
-/

namespace Paper2.SourcePadding

variable {C I B : Type*}

/-- A retained bin contains two distinct active items and one inactive item. -/
def Witness (active : C → I → Prop) (keep : I → Prop) (bin : I → B) (c : C) : Prop :=
  ∃ i j h, i ≠ j ∧ keep i ∧ keep j ∧ keep h ∧
    active c i ∧ active c j ∧ ¬ active c h ∧ bin i = bin j ∧ bin i = bin h

noncomputable def witnessCoords [Fintype C] (active : C → I → Prop)
    (keep : I → Prop) (bin : I → B) : Finset C := by
  classical
  exact Finset.univ.filter (Witness active keep bin)

@[simp] theorem mem_witnessCoords [Fintype C] (active : C → I → Prop)
    (keep : I → Prop) (bin : I → B) (c : C) :
    c ∈ witnessCoords active keep bin ↔ Witness active keep bin c := by
  classical
  simp [witnessCoords]

abbrev Padded (C : Type*) [Fintype C] (q : ℕ) := C ⊕ Fin (q - Fintype.card C)

def paddedActive [Fintype C] (active : C → I → Prop) (q : ℕ) : Padded C q → I → Prop
  | .inl c, i => active c i
  | .inr _, _ => False

abbrev Repeated (C : Type*) [Fintype C] (q r : ℕ) := Padded C q × Fin r

def repeatedActive [Fintype C] (active : C → I → Prop) (q r : ℕ) :
    Repeated C q r → I → Prop := fun c i => paddedActive active q c.1 i

theorem card_padded [Fintype C] {q : ℕ} (hq : Fintype.card C ≤ q) :
    Fintype.card (Padded C q) = q := by
  simp [Padded, Nat.add_sub_of_le hq]

theorem card_repeated [Fintype C] {q r : ℕ} (hq : Fintype.card C ≤ q) :
    Fintype.card (Repeated C q r) = q * r := by
  rw [Fintype.card_prod, card_padded hq, Fintype.card_fin]

@[simp] theorem witness_padded_inl [Fintype C] (active : C → I → Prop)
    (keep : I → Prop) (bin : I → B) (q : ℕ) (c : C) :
    Witness (paddedActive active q) keep bin (.inl c) ↔ Witness active keep bin c := Iff.rfl

@[simp] theorem not_witness_padded_inr [Fintype C] (active : C → I → Prop)
    (keep : I → Prop) (bin : I → B) (q : ℕ) (j : Fin (q - Fintype.card C)) :
    ¬ Witness (paddedActive active q) keep bin (.inr j) := by
  simp [Witness, paddedActive]

@[simp] theorem witness_repeated [Fintype C] (active : C → I → Prop)
    (keep : I → Prop) (bin : I → B) (q r : ℕ) (c : Repeated C q r) :
    Witness (repeatedActive active q r) keep bin c ↔
      Witness (paddedActive active q) keep bin c.1 := Iff.rfl

def padEmbedding [Fintype C] (q : ℕ) : C ↪ Padded C q :=
  ⟨Sum.inl, Sum.inl_injective⟩

theorem witnessCoords_padded [Fintype C] (active : C → I → Prop)
    (keep : I → Prop) (bin : I → B) (q : ℕ) :
    witnessCoords (paddedActive active q) keep bin =
      (witnessCoords active keep bin).map (padEmbedding q) := by
  classical
  ext c
  cases c <;> simp [padEmbedding]

theorem card_witnessCoords_padded [Fintype C] (active : C → I → Prop)
    (keep : I → Prop) (bin : I → B) (q : ℕ) :
    (witnessCoords (paddedActive active q) keep bin).card =
      (witnessCoords active keep bin).card := by
  rw [witnessCoords_padded, Finset.card_map]

theorem witnessCoords_repeated [Fintype C] (active : C → I → Prop)
    (keep : I → Prop) (bin : I → B) (q r : ℕ) :
    witnessCoords (repeatedActive active q r) keep bin =
      (witnessCoords (paddedActive active q) keep bin) ×ˢ (Finset.univ : Finset (Fin r)) := by
  classical
  ext c
  simp

theorem card_witnessCoords_repeated [Fintype C] (active : C → I → Prop)
    (keep : I → Prop) (bin : I → B) (q r : ℕ) :
    (witnessCoords (repeatedActive active q r) keep bin).card =
      (witnessCoords active keep bin).card * r := by
  rw [witnessCoords_repeated, Finset.card_product, card_witnessCoords_padded]
  simp

theorem padded_active_injective [Fintype C] (active : C → I → Prop) (assign : I → B)
    (h : ∀ c, Set.InjOn assign {i | active c i}) (q : ℕ) :
    ∀ c, Set.InjOn assign {i | paddedActive active q c i} := by
  intro c
  cases c with
  | inl c => exact h c
  | inr j => intro i hi; exact False.elim hi

theorem repeated_active_injective [Fintype C] (active : C → I → Prop) (assign : I → B)
    (h : ∀ c, Set.InjOn assign {i | active c i}) (q r : ℕ) :
    ∀ c, Set.InjOn assign {i | repeatedActive active q r c i} := by
  intro c
  exact padded_active_injective active assign h q c.1

/-- The smallest power of two at least the coordinate count. -/
def powTwoCeil (n : ℕ) : ℕ := 2 ^ Nat.clog 2 n

theorem le_powTwoCeil (n : ℕ) : n ≤ powTwoCeil n := Nat.le_pow_clog (by decide) n

theorem powTwoCeil_lt_two_mul {n : ℕ} (hn : 0 < n) : powTwoCeil n < 2 * n := by
  by_cases hsmall : n = 1
  · subst n
    norm_num [powTwoCeil]
  · have hn' : 1 < n := by omega
    have hc : 0 < Nat.clog 2 n := Nat.clog_pos (by decide) hn'
    have hp : 2 ^ (Nat.clog 2 n).pred < n := Nat.pow_pred_clog_lt_self (by decide) hn'
    unfold powTwoCeil
    rw [← Nat.succ_pred_eq_of_pos hc, Nat.pow_succ]
    omega

end Paper2.SourcePadding
