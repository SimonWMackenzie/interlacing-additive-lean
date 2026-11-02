import Paper2.RationalRowEstimates
import Paper2.SourceProfilesInner
import Paper2.SourceProjection

/-!
# Reference-copy capacity on original labelled rows

Frozen Paper 2 v12, restoration `res:destinations`, lines 250--310.
These adapters use one joint image of the actual retained tuple event.
They do not construct the certificate frontier or prove its weight bound.
-/

namespace Paper2.ReferenceCapacity

open Workspace.Types.CommComplexity

variable {A K Rw : Type*} [Fintype A] [Fintype K] [Fintype Rw]
  {w n : ℕ}

/-- Actual selected reference rows, retaining their original source labels. -/
def selectedRows (lift : Fin w → A → Rw) (e : Fin n → Fin w)
    (R : Set Rw) : Set (Fin n × A) :=
  {z | lift (e z.1) z.2 ∈ R}

/-- One image of the whole correlated retained tuple event. -/
def selectedColumns (e : Fin n → Fin w) (O : Set (Fin w → K)) :
    Set (Fin n → K) :=
  (fun y j => y (e j)) '' O

theorem selected_restriction
    (F : A → K → Bool) (M : Rw → (Fin w → K) → Bool)
    (lift : Fin w → A → Rw) (e : Fin n → Fin w)
    (R : Set Rw) (O : Set (Fin w → K))
    (hentry : ∀ j a, lift (e j) a ∈ R → ∀ y ∈ O,
      M (lift (e j) a) y = F a (y (e j))) :
    Compression.restrictionD (fullInterlace F n)
      (selectedRows lift e R) (selectedColumns e O) ≤
        Compression.restrictionD M R O := by
  apply SourceProjection.restrictionD_projected_le M (fullInterlace F n)
    (fun z => lift (e z.1) z.2) (fun y j => y (e j))
    R O (selectedRows lift e R)
  · intro z hz
    exact hz
  · intro z hz y hy
    exact hentry z.1 z.2 hz y hy

theorem small_two
    (μ : PositiveRationalLaw A) (ν : PositiveRationalLaw K)
    (F : A → K → Bool) (M : Rw → (Fin w → K) → Bool)
    (lift : Fin w → A → Rw) (e : Fin n → Fin w)
    (R : Set Rw) (O : Set (Fin w → K))
    (hentry : ∀ j a, lift (e j) a ∈ R → ∀ y ∈ O,
      M (lift (e j) a) y = F a (y (e j)))
    (H : ℕ) (x : ℝ) (hH : 2 ≤ H) (hx : 0 < x)
    (hscale : 2 * x ≤ 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (Q : Finset (Fin n)) (hQ : 2 ≤ Q.card)
    (hrow : ∀ j ∈ Q, 2 * x ≤ μ.toFiniteLaw.prob
      (fun a => lift (e j) a ∈ R))
    (hcol : (9 / 25 : ℝ) ≤ (ν.toFiniteLaw.iid n).prob
      (· ∈ selectedColumns e O)) :
    H + 1 ≤ Compression.restrictionD M R O := by
  classical
  let S := selectedRows lift e R
  let C := selectedColumns e O
  have hr : ∀ j ∈ Q, 2 * x ≤ μ.toFiniteLaw.prob
      (fun a => (j, a) ∈ S.toFinset) := by
    intro j hj
    simpa [S, selectedRows] using hrow j hj
  have hc : (9 / 25 : ℝ) ≤ (ν.toFiniteLaw.iid n).prob
      (· ∈ C.toFinset) := by simpa [C] using hcol
  have hh := RationalRowEstimates.small_capacity_two μ ν F H n
    hH hx hscale hprofile Q hQ S.toFinset C.toFinset hr hc
  have heq : D (NPCC.subgame (fullInterlace F n) S.toFinset C.toFinset) =
      Compression.restrictionD (fullInterlace F n) S C := by
    have hS : {z | z ∈ S.toFinset} = S := by ext z; simp
    have hC : {z | z ∈ C.toFinset} = C := by ext z; simp
    conv_rhs => rw [← hS, ← hC]
    rfl
  rw [heq] at hh
  exact hh.trans (selected_restriction F M lift e R O hentry)

theorem small_power
    (μ : PositiveRationalLaw A) (ν : PositiveRationalLaw K)
    (F : A → K → Bool) (M : Rw → (Fin w → K) → Bool)
    (lift : Fin w → A → Rw) (e : Fin n → Fin w)
    (R : Set Rw) (O : Set (Fin w → K))
    (hentry : ∀ j a, lift (e j) a ∈ R → ∀ y ∈ O,
      M (lift (e j) a) y = F a (y (e j)))
    (H l : ℕ) (x : ℝ) (hH : 2 ≤ H) (hx : 0 < x)
    (hl : 2 ≤ l) (hscale : (2 : ℝ) ^ l * x ≤ 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (Q : Finset (Fin n)) (hQ : 2 ^ (l - 1) + 1 ≤ Q.card)
    (hrow : ∀ j ∈ Q, (2 : ℝ) ^ l * x ≤ μ.toFiniteLaw.prob
      (fun a => lift (e j) a ∈ R))
    (hcol : (9 / 25 : ℝ) ≤ (ν.toFiniteLaw.iid n).prob
      (· ∈ selectedColumns e O)) :
    H + l ≤ Compression.restrictionD M R O := by
  classical
  let S := selectedRows lift e R
  let C := selectedColumns e O
  have hr : ∀ j ∈ Q, (2 : ℝ) ^ l * x ≤ μ.toFiniteLaw.prob
      (fun a => (j, a) ∈ S.toFinset) := by
    intro j hj
    simpa [S, selectedRows] using hrow j hj
  have hc : (9 / 25 : ℝ) ≤ (ν.toFiniteLaw.iid n).prob
      (· ∈ C.toFinset) := by simpa [C] using hcol
  have hh := RationalRowEstimates.small_capacity_power μ ν F H l n
    hH hx hl hscale hprofile Q hQ S.toFinset C.toFinset hr hc
  have heq : D (NPCC.subgame (fullInterlace F n) S.toFinset C.toFinset) =
      Compression.restrictionD (fullInterlace F n) S C := by
    have hS : {z | z ∈ S.toFinset} = S := by ext z; simp
    have hC : {z | z ∈ C.toFinset} = C := by ext z; simp
    conv_rhs => rw [← hS, ← hC]
    rfl
  rw [heq] at hh
  exact hh.trans (selected_restriction F M lift e R O hentry)

/-- The strong-seed lower bound on selected original reference copies. Its
column hypothesis is one joint projection of the actual retained event. -/
theorem strong_seed
    (μ : PositiveRationalLaw A) (ν : PositiveRationalLaw K)
    (F : A → K → Bool) (M : Rw → (Fin w → K) → Bool)
    (lift : Fin w → A → Rw)
    {a : ℕ} (e : Fin (StrongSeed.copies a) → Fin w)
    (R : Set Rw) (O : Set (Fin w → K))
    (hentry : ∀ j z, lift (e j) z ∈ R → ∀ y ∈ O,
      M (lift (e j) z) y = F z (y (e j)))
    (H : ℕ) (x : ℝ) (hH : 3 ≤ H) (ha : 4 ≤ a)
    (hx : 0 < x) (hscale : (2 : ℝ) ^ a * x ≤ 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (hrow : ∀ j, (2 : ℝ) ^ a * x ≤ μ.toFiniteLaw.prob
      (fun z => lift (e j) z ∈ R))
    (hcol : (2 : ℝ) ^ (-((2 : ℝ) ^ a / 1024)) ≤
      (ν.toFiniteLaw.iid (StrongSeed.copies a)).prob
        (· ∈ selectedColumns e O)) :
    H + a ≤ Compression.restrictionD M R O := by
  let S := selectedRows lift e R
  have hr : ∀ j, (2 : ℝ) ^ a * x ≤ μ.toFiniteLaw.prob
      (fun z => (j, z) ∈ S) := by
    intro j
    exact hrow j
  have hh := SourceProfilesInner.strong_member_sets μ ν F H a hH ha
    x hx hscale hprofile S (selectedColumns e O) hr hcol
  exact hh.trans (selected_restriction F M lift e R O hentry)

end Paper2.ReferenceCapacity

#print axioms Paper2.ReferenceCapacity.selected_restriction
#print axioms Paper2.ReferenceCapacity.small_two
#print axioms Paper2.ReferenceCapacity.small_power
#print axioms Paper2.ReferenceCapacity.strong_seed
