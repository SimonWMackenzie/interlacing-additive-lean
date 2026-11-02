import EthInapproximability.CurrentPaper.AmplificationFirstProfiles
import EthInapproximability.CurrentPaper.GraphVectors

/-!
# Upper protocols for the actual protected matrix

Source: frozen v8 `03-parameterized-construction.tex`,
`eq:paper-B-yes` and the general upper protocol immediately preceding
`eq:paper-B-no-exact`. Alice sends a bin, Bob sends its coordinate,
and Alice selects one of the remaining copies of the input matrix.
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.ProtectedUpper

open NPCC Workspace.Types.CommComplexity Workspace.Types.Interlace
open Construction
open EthInapproximability.ParameterizedNP.GuardedSourceGraph

universe u
variable {X Y : Type u} [Fintype X] [Fintype Y] [Nonempty Y]

/-- If a public row label determines Bob's input to the original matrix,
Alice can send that label and then execute the original protocol. -/
theorem selector_upper {A B : Type u} [Fintype A] [Fintype B]
    (R : X → Y → Bool) (k : ℕ) (label : A → Fin (2 ^ k))
    (input : A → X) (selector : A → B → Y)
    (hselector : ∀ a a', label a = label a' → selector a = selector a') :
    D (fun a b => R (input a) (selector a b)) ≤ D R + k := by
  classical
  let col : B → Fin (2 ^ k) → Y := fun b j =>
    if h : ∃ a, label a = j then selector (Classical.choose h) b
    else Classical.arbitrary Y
  have heq : (fun a b => R (input a) (selector a b)) =
      fun a b => interlaceFun R (2 ^ k) (label a, input a) (col b) := by
    funext a b
    have h : ∃ a', label a' = label a := ⟨a, rfl⟩
    simp only [interlaceFun, col, dif_pos h]
    exact congrArg (R (input a))
      (congrFun (hselector a (Classical.choose h) (Classical.choose_spec h).symm) b)
  rw [heq]
  exact (D_mapNodes_le _ (fun a => (label a, input a)) col).trans
    (EthInapproximability.ParameterizedNP.powerOfTwoInterlace_upper R k)

abbrev Rows (s L n : ℕ) := ThirdRows s L ⊕ (Fin n × X)

def bin {s L n : ℕ} (σ : Fin n → Fin s) : Rows (X := X) s L n → Fin s
  | .inl r => r.1
  | .inr r => σ r.1

def input {a s q L n : ℕ} (family : SecondFamily a q L X) (α : Fin q) :
    Rows (X := X) s L n → X
  | .inl r => (family r.2 α).2
  | .inr r => r.2

def graphSelector {a s q n : ℕ} (hs : 0 < s)
    (vectors : Fin n → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (i : Fin n) (c : RawColumns a s q Y) : Y :=
  if aligned hs c then
    let α := (c.2 (firstBin s hs)).1
    if hi : vectors i α = true then
      c.1 (Fin.castAdd 1 (activeSlot vectors cap α ⟨i, hi⟩))
    else c.1 (Fin.last s)
  else c.1 (Fin.last s)

def selector {a s q L n : ℕ} (hs : 0 < s)
    (family : SecondFamily a q L X) (vectors : Fin n → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s) :
    Rows (X := X) s L n → RawColumns a s q Y → Y
  | .inl r, c => (c.2 r.1).2 (firstCoordinate a s (family r.2 (c.2 r.1).1).1)
  | .inr r, c => graphSelector hs vectors cap r.1 c

def matrix (R : X → Y → Bool) {a s q L n : ℕ} (hs : 0 < s)
    (family : SecondFamily a q L X) (vectors : Fin n → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s) :
    Rows (X := X) s L n → RawColumns a s q Y → Bool
  | .inl r, c => thirdMatrix R a s q L family r c.2
  | .inr r, c => graphEntry R hs vectors cap r.1 r.2 c

theorem pinned_evaluation (R : X → Y → Bool) {a s q L n : ℕ} (hs : 0 < s)
    (family : SecondFamily a q L X) (vectors : Fin n → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s) (σ : Fin n → Fin s)
    (p : Fin s) (α : Fin q) (r : {r : Rows (X := X) s L n // bin σ r = p})
    (c : {c : RawColumns a s q Y // (c.2 p).1 = α}) :
    matrix R hs family vectors cap r.val c.val =
      R (input family α r.val) (selector hs family vectors cap r.val c.val) := by
  rcases r with ⟨r | r, hr⟩
  · change r.1 = p at hr
    simp only [matrix, thirdMatrix, secondMatrix, firstMatrix, input, selector]
    rw [hr, c.property]
  · simp only [matrix, input, selector, graphEntry, graphSelector]
    split
    · split <;> rfl
    · rfl

def yesLabel {a s q L n : ℕ} (ha : 1 ≤ a)
    (family : SecondFamily a q L X) (vectors : Fin n → Fin q → Bool)
    (α : Fin q) : Rows (X := X) s L n → Fin (2 ^ a)
  | .inl r => ⟨(family r.2 α).1.val, (family r.2 α).1.isLt.trans_le (Nat.sub_le _ _)⟩
  | .inr r => ⟨qOne a + (if vectors r.1 α = true then 1 else 0), by
      have := qOne_add_two a ha
      split <;> omega⟩

theorem graphSelector_inactive {a s q n : ℕ} (hs : 0 < s)
    (vectors : Fin n → Fin q → Bool) (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (i : Fin n) (p : Fin s) (α : Fin q) (c : RawColumns a s q Y)
    (hc : (c.2 p).1 = α) (hi : vectors i α ≠ true) :
    graphSelector hs vectors cap i c = c.1 (Fin.last s) := by
  by_cases hal : aligned hs c
  · have heq : (c.2 (firstBin s hs)).1 = α := (hal p).symm.trans hc
    simp [graphSelector, hal, heq, hi]
  · simp [graphSelector, hal]

theorem yes_local_upper (R : X → Y → Bool) {a s q L n : ℕ}
    (ha : 1 ≤ a) (hs : 0 < s) (family : SecondFamily a q L X)
    (vectors : Fin n → Fin q → Bool) (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (σ : Fin n → Fin s) (hlegal : Legal vectors Finset.univ σ)
    (p : Fin s) (α : Fin q) :
    D (fun (r : {r : Rows (X := X) s L n // bin σ r = p})
      (c : {c : RawColumns a s q Y // (c.2 p).1 = α}) =>
      matrix R hs family vectors cap r.val c.val) ≤ D R + a := by
  classical
  simp_rw [pinned_evaluation R hs family vectors cap σ p α]
  apply selector_upper (A := {r : Rows (X := X) s L n // bin σ r = p})
    (B := {c : RawColumns a s q Y // (c.2 p).1 = α})
    R a (fun r => yesLabel ha family vectors α r.val)
    (fun r => input family α r.val) (fun r c => selector hs family vectors cap r.val c.val)
  intro r r' heq
  have hb := r.property
  have hb' := r'.property
  have hv := congrArg Fin.val heq
  funext c
  rcases hr : r.val with r₀ | i <;> rcases hr' : r'.val with r₁ | j
  · rw [hr] at hb hv
    rw [hr'] at hb' hv
    change r₀.1 = p at hb
    change r₁.1 = p at hb'
    change (family r₀.2 α).1.val = (family r₁.2 α).1.val at hv
    simp only [selector, hb, hb', c.property, Fin.ext hv]
  · rw [hr, hr'] at hv
    change (family r₀.2 α).1.val = qOne a + (if vectors j.1 α = true then 1 else 0) at hv
    have := (family r₀.2 α).1.isLt
    split at hv <;> omega
  · rw [hr, hr'] at hv
    change qOne a + (if vectors i.1 α = true then 1 else 0) = (family r₁.2 α).1.val at hv
    have := (family r₁.2 α).1.isLt
    split at hv <;> omega
  · rw [hr] at hb hv
    rw [hr'] at hb' hv
    change σ i.1 = p at hb
    change σ j.1 = p at hb'
    change qOne a + (if vectors i.1 α = true then 1 else 0) =
      qOne a + (if vectors j.1 α = true then 1 else 0) at hv
    by_cases hi : vectors i.1 α = true <;> by_cases hj : vectors j.1 α = true
    · have hij : i.1 = j.1 := Finset.card_le_one.mp (hlegal p α) i.1
        (by simp [ParameterizedNP.GuardedSourceGraph.mem_activeSet, hb, hi]) j.1
        (by simp [ParameterizedNP.GuardedSourceGraph.mem_activeSet, hb', hj])
      simp only [selector, hij]
    · simp [hi, hj] at hv
    · simp [hi, hj] at hv
    · exact (graphSelector_inactive hs vectors cap i.1 p α c.val c.property hi).trans
        (graphSelector_inactive hs vectors cap j.1 p α c.val c.property hj).symm

def anyLabel {a s q L n k : ℕ} (hwidth : qOne a + (s + 1) ≤ 2 ^ k)
    (family : SecondFamily a q L X) (vectors : Fin n → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s) (α : Fin q) :
    Rows (X := X) s L n → Fin (2 ^ k)
  | .inl r => ⟨(family r.2 α).1.val, by have := (family r.2 α).1.isLt; omega⟩
  | .inr r => ⟨qOne a +
      (if hi : vectors r.1 α = true then (activeSlot vectors cap α ⟨r.1, hi⟩).val else s), by
      split
      · have := (activeSlot vectors cap α ⟨r.1, ‹vectors r.1 α = true›⟩).isLt
        omega
      · omega⟩

theorem any_local_upper (R : X → Y → Bool) {a s q L n k : ℕ}
    (hwidth : qOne a + (s + 1) ≤ 2 ^ k) (hs : 0 < s)
    (family : SecondFamily a q L X) (vectors : Fin n → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s) (σ : Fin n → Fin s)
    (p : Fin s) (α : Fin q) :
    D (fun (r : {r : Rows (X := X) s L n // bin σ r = p})
      (c : {c : RawColumns a s q Y // (c.2 p).1 = α}) =>
      matrix R hs family vectors cap r.val c.val) ≤ D R + k := by
  classical
  simp_rw [pinned_evaluation R hs family vectors cap σ p α]
  apply selector_upper (A := {r : Rows (X := X) s L n // bin σ r = p})
    (B := {c : RawColumns a s q Y // (c.2 p).1 = α})
    R k (fun r => anyLabel hwidth family vectors cap α r.val)
    (fun r => input family α r.val) (fun r c => selector hs family vectors cap r.val c.val)
  intro r r' heq
  have hb := r.property
  have hb' := r'.property
  have hv := congrArg Fin.val heq
  funext c
  rcases hr : r.val with r₀ | i <;> rcases hr' : r'.val with r₁ | j
  · rw [hr] at hb hv
    rw [hr'] at hb' hv
    change r₀.1 = p at hb
    change r₁.1 = p at hb'
    change (family r₀.2 α).1.val = (family r₁.2 α).1.val at hv
    simp only [selector, hb, hb', c.property, Fin.ext hv]
  · rw [hr, hr'] at hv
    change (family r₀.2 α).1.val = qOne a +
      (if hj : vectors j.1 α = true then (activeSlot vectors cap α ⟨j.1, hj⟩).val else s) at hv
    have := (family r₀.2 α).1.isLt
    split at hv <;> omega
  · rw [hr, hr'] at hv
    change qOne a +
      (if hi : vectors i.1 α = true then (activeSlot vectors cap α ⟨i.1, hi⟩).val else s) =
      (family r₁.2 α).1.val at hv
    have := (family r₁.2 α).1.isLt
    split at hv <;> omega
  · rw [hr, hr'] at hv
    change qOne a +
      (if hi : vectors i.1 α = true then (activeSlot vectors cap α ⟨i.1, hi⟩).val else s) =
      qOne a +
      (if hj : vectors j.1 α = true then (activeSlot vectors cap α ⟨j.1, hj⟩).val else s) at hv
    by_cases hi : vectors i.1 α = true <;> by_cases hj : vectors j.1 α = true
    · rw [dif_pos hi, dif_pos hj] at hv
      have heq : activeSlot vectors cap α ⟨i.1, hi⟩ = activeSlot vectors cap α ⟨j.1, hj⟩ :=
        Fin.ext (by omega)
      have hij : i.1 = j.1 := congrArg Subtype.val (activeSlot_injective vectors cap α heq)
      simp only [selector, hij]
    · rw [dif_pos hi, dif_neg hj] at hv
      have := (activeSlot vectors cap α ⟨i.1, hi⟩).isLt
      omega
    · rw [dif_neg hi, dif_pos hj] at hv
      have := (activeSlot vectors cap α ⟨j.1, hj⟩).isLt
      omega
    · exact (graphSelector_inactive hs vectors cap i.1 p α c.val c.property hi).trans
        (graphSelector_inactive hs vectors cap j.1 p α c.val c.property hj).symm

theorem matrix_yes_upper (R : X → Y → Bool) {a b r L n : ℕ}
    (ha : 1 ≤ a) (family : SecondFamily a (2 ^ r) L X)
    (vectors : Fin n → Fin (2 ^ r) → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ 2 ^ b)
    (σ : Fin n → Fin (2 ^ b)) (hlegal : Legal vectors Finset.univ σ) :
    D (matrix R (pow_pos (by omega) b) family vectors cap) ≤ D R + a + r + b := by
  have h : D (matrix R (pow_pos (by omega) b) family vectors cap) ≤ b + (r + (D R + a)) := by
    apply comp_le_partition _ b (r + (D R + a)) (bin σ)
    intro p
    apply comp_le_partition_cols _ r (D R + a) (fun c => (c.2 p).1)
    intro α
    exact yes_local_upper R ha (pow_pos (by omega) b) family vectors cap σ hlegal p α
  omega

theorem matrix_any_upper (R : X → Y → Bool) {a b r L n k : ℕ}
    (hwidth : qOne a + (2 ^ b + 1) ≤ 2 ^ k)
    (family : SecondFamily a (2 ^ r) L X) (vectors : Fin n → Fin (2 ^ r) → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ 2 ^ b) :
    D (matrix R (pow_pos (by omega) b) family vectors cap) ≤ D R + k + r + b := by
  have h : D (matrix R (pow_pos (by omega) b) family vectors cap) ≤ b + (r + (D R + k)) := by
    apply comp_le_partition _ b (r + (D R + k)) (bin (fun _ => ⟨0, pow_pos (by omega) b⟩))
    intro p
    apply comp_le_partition_cols _ r (D R + k) (fun c => (c.2 p).1)
    intro α
    exact any_local_upper R hwidth (pow_pos (by omega) b) family vectors cap _ p α
  omega

theorem rawMatrix_le_matrix (R : X → Y → Bool) (a s q L nv nb : ℕ) (hs : 0 < s)
    (family : SecondFamily a q L X) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s) :
    D (rawMatrix R a s q L nv nb hs family order vectors cap) ≤
      D (matrix R hs family vectors cap) := by
  have heq : rawMatrix R a s q L nv nb hs family order vectors cap =
      fun r c => matrix R hs family vectors cap (rawRowEquiv s L nv nb order r) c := by
    funext r c
    rcases r with r | (r | r) <;> rfl
  rw [heq]
  exact D_mapNodes_le _ (rawRowEquiv s L nv nb order) id

theorem protected_yes_upper [Nonempty X] (R : X → Y → Bool) {a b r L nv nb : ℕ}
    (ha : 1 ≤ a) (hL : 0 < L) (hv : 0 < nv) (hb : 0 < nb)
    (family : SecondFamily a (2 ^ r) L X) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin (2 ^ r) → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ 2 ^ b)
    (σ : Fin (nv + nb) → Fin (2 ^ b)) (hlegal : Legal vectors Finset.univ σ) :
    D (protectedMatrix R a (2 ^ b) (2 ^ r) L nv nb (pow_pos (by omega) b)
      family order vectors cap) ≤ D R + a + r + b := by
  rw [D_protectedMatrix _ _ _ _ _ _ _ _ (by positivity) hL hv hb]
  exact (rawMatrix_le_matrix R _ _ _ _ _ _ _ family order vectors cap).trans
    (matrix_yes_upper R ha family vectors cap σ hlegal)

theorem protected_any_upper [Nonempty X] (R : X → Y → Bool) {a b r L nv nb k : ℕ}
    (hwidth : qOne a + (2 ^ b + 1) ≤ 2 ^ k)
    (hL : 0 < L) (hv : 0 < nv) (hb : 0 < nb)
    (family : SecondFamily a (2 ^ r) L X) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin (2 ^ r) → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ 2 ^ b) :
    D (protectedMatrix R a (2 ^ b) (2 ^ r) L nv nb (pow_pos (by omega) b)
      family order vectors cap) ≤ D R + k + r + b := by
  rw [D_protectedMatrix _ _ _ _ _ _ _ _ (by positivity) hL hv hb]
  exact (rawMatrix_le_matrix R _ _ _ _ _ _ _ family order vectors cap).trans
    (matrix_any_upper R hwidth family vectors cap)

end EthInapproximability.CurrentPaper.ProtectedUpper
