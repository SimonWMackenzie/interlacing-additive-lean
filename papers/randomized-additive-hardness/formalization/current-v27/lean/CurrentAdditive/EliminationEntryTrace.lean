import CurrentAdditive.MaterializedGauss

/-!
The actual materialized Gauss--Jordan loop can be instrumented with the
original-row permutation and its rational row-operation matrix. The support
invariant here is the required bridge to a selected original-row minor;
an unconditional bit bound is not claimed until the selected-minor transfer
is proved.
-/

namespace CurrentAdditive.EliminationEntryBounds

open CurrentAdditive.SequentialTotality

def rowLinear {m k : Nat} (U : Fin m → Fin m → ℚ)
    (A : Fin m → Fin k → ℚ) (i : Fin m) (j : Fin k) : ℚ :=
  ∑ t : Fin m, U i t * A t j

def Represents {m k : Nat} (A B : Fin m → Fin k → ℚ)
    (U : Fin m → Fin m → ℚ) : Prop :=
  ∀ i j, B i j = rowLinear U A i j

def identityRows {m : Nat} : Fin m → Fin m → ℚ :=
  fun i j => if i = j then 1 else 0

theorem identityRows_represents {m k : Nat} (A : Fin m → Fin k → ℚ) :
    Represents A A identityRows := by
  intro i j
  simp [rowLinear, identityRows]

/-- `π t` names the original input row currently in slot `t`, before
linear combinations with earlier pivot rows. -/
structure Support {m : Nat} (U : Fin m → Fin m → ℚ)
    (π : Fin m → Fin m) (r : Nat) : Prop where
  pivot : ∀ i t, i.val < r → r ≤ t.val → U i (π t) = 0
  residual : ∀ i t, r ≤ i.val → r ≤ t.val → t ≠ i → U i (π t) = 0
  diagonal : ∀ i, r ≤ i.val → U i (π i) = 1

theorem identityRows_support {m : Nat} :
    Support (m := m) identityRows (fun i => i) 0 := by
  constructor
  · intro i t hi
    omega
  · intro i t _ _ hne
    simp [identityRows, Ne.symm hne]
  · intro i _
    simp [identityRows]

def clearRows {m k : Nat} (B : Fin m → Fin k → ℚ)
    (U : Fin m → Fin m → ℚ) (r : Fin m) (c : Fin k) :
    Fin m → Fin m → ℚ :=
  fun i t =>
    if i = r then U r t / B r c
    else U i t - (B i c / B r c) * U r t

theorem clearRows_represents {m k : Nat}
    (A B : Fin m → Fin k → ℚ) (U : Fin m → Fin m → ℚ)
    (r : Fin m) (c : Fin k) (hrep : Represents A B U) :
    Represents A (clearTyped B r c) (clearRows B U r c) := by
  intro i j
  by_cases hir : i = r
  · subst i
    simp only [rowLinear, clearTyped, clearRows]
    rw [hrep r j]
    change (∑ t : Fin m, U r t * A t j) / B r c = _
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro t _
    simp only [ite_true]
    ring
  · simp only [rowLinear, clearTyped, clearRows, if_neg hir]
    rw [hrep i j, hrep r j]
    change (∑ t : Fin m, U i t * A t j) -
      (B i c / B r c) * (∑ t : Fin m, U r t * A t j) = _
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t _
    ring

theorem clearRows_support {m k : Nat}
    (B : Fin m → Fin k → ℚ) (U : Fin m → Fin m → ℚ)
    (π : Fin m → Fin m) (r : Fin m) (c : Fin k)
    (hs : Support U π r.val) :
    Support (clearRows B U r c) π (r.val + 1) := by
  constructor
  · intro i t hi ht
    by_cases hir : i = r
    · subst i
      simp [clearRows, hs.residual r t (by omega) (by omega)
        (by intro h; have := congrArg Fin.val h; omega)]
    · have ht0 : r.val ≤ t.val := by omega
      have hUr : U r (π t) = 0 :=
        hs.residual r t (by omega) ht0 (by intro h; have := congrArg Fin.val h; omega)
      have hUi : U i (π t) = 0 := by
        by_cases hip : i.val < r.val
        · exact hs.pivot i t hip ht0
        · exact hs.residual i t (by omega) ht0
            (by intro h; have := congrArg Fin.val h; omega)
      simp [clearRows, hir, hUr, hUi]
  · intro i t hi ht hti
    have hir : i ≠ r := by
      intro h
      have := congrArg Fin.val h
      omega
    have htr : t ≠ r := by
      intro h
      have := congrArg Fin.val h
      omega
    have hUi : U i (π t) = 0 := hs.residual i t (by omega) (by omega) hti
    have hUr : U r (π t) = 0 := hs.residual r t (by omega) (by omega) htr
    simp [clearRows, hir, hUi, hUr]
  · intro i hi
    have hir : i ≠ r := by
      intro h
      have := congrArg Fin.val h
      omega
    have hUi : U i (π i) = 1 := hs.diagonal i (by omega)
    have hUr : U r (π i) = 0 := hs.residual r i (by omega) (by omega)
      (by intro h; have := congrArg Fin.val h; omega)
    simp [clearRows, hir, hUi, hUr]

theorem swapRows_represents {m k : Nat}
    (A B : Fin m → Fin k → ℚ) (U : Fin m → Fin m → ℚ)
    (r s : Fin m) (hrep : Represents A B U) :
    Represents A (swapTyped B r s) (swapTyped U r s) := by
  intro i j
  exact hrep (Equiv.swap r s i) j

theorem swapRows_support {m : Nat}
    (U : Fin m → Fin m → ℚ) (π : Fin m → Fin m)
    (r s : Fin m) (hs : r.val ≤ s.val)
    (h : Support U π r.val) :
    Support (swapTyped U r s) (fun t => π (Equiv.swap r s t)) r.val := by
  let sw := Equiv.swap r s
  have hactive (t : Fin m) (ht : r.val ≤ t.val) : r.val ≤ (sw t).val := by
    by_cases htr : t = r
    · subst t
      simpa [sw] using hs
    by_cases hts : t = s
    · subst t
      simp [sw]
    simpa [sw, Equiv.swap_apply_of_ne_of_ne htr hts] using ht
  have hfixed (t : Fin m) (ht : t.val < r.val) : sw t = t := by
    have htr : t ≠ r := by
      intro heq
      have := congrArg Fin.val heq
      omega
    have hts : t ≠ s := by
      intro heq
      have := congrArg Fin.val heq
      omega
    exact Equiv.swap_apply_of_ne_of_ne htr hts
  constructor
  · intro i t hi ht
    change U (sw i) (π (sw t)) = 0
    rw [hfixed i hi]
    exact h.pivot i (sw t) hi (hactive t ht)
  · intro i t hi ht hne
    change U (sw i) (π (sw t)) = 0
    exact h.residual (sw i) (sw t) (hactive i hi) (hactive t ht)
      (sw.injective.ne hne)
  · intro i hi
    change U (sw i) (π (sw i)) = 1
    exact h.diagonal (sw i) (hactive i hi)

structure RunTrace (m k : Nat) where
  B : Fin m → Fin k → ℚ
  pivots : List (Fin m × Fin k)
  U : Fin m → Fin m → ℚ
  π : Fin m → Fin m

/-- Exactly the materialized pivot loop, with ghost row-operation and
original-row labels updated in lockstep. -/
def runTrace {m k : Nat} (B : Fin m → Fin k → ℚ)
    (U : Fin m → Fin m → ℚ) (π : Fin m → Fin m)
    (r c fuel : Nat) : RunTrace m k :=
  match fuel with
  | 0 => ⟨B, [], U, π⟩
  | fuel + 1 =>
    if hr : r < m then
      if hc : c < k then
        let rf : Fin m := ⟨r, hr⟩
        let cf : Fin k := ⟨c, hc⟩
        match pivotTyped B r cf with
        | none => runTrace B U π r (c + 1) fuel
        | some i =>
          let Bs := swapTyped B rf i
          let Us := swapTyped U rf i
          let πs := fun t => π (Equiv.swap rf i t)
          let C := CurrentAdditive.MaterializedGauss.materialize (clearTyped Bs rf cf)
          let V := clearRows Bs Us rf cf
          let out := runTrace C V πs (r + 1) (c + 1) fuel
          ⟨out.B, (rf, cf) :: out.pivots, out.U, out.π⟩
      else ⟨B, [], U, π⟩
    else ⟨B, [], U, π⟩

theorem runTrace_materialized {m k : Nat} (B : Fin m → Fin k → ℚ)
    (U : Fin m → Fin m → ℚ) (π : Fin m → Fin m) (r c fuel : Nat) :
    let out := runTrace B U π r c fuel
    (out.B, out.pivots) =
      CurrentAdditive.MaterializedGauss.echelonMaterialized B r c fuel := by
  induction fuel generalizing B U π r c with
  | zero => rfl
  | succ fuel ih =>
      simp only [runTrace, CurrentAdditive.MaterializedGauss.echelonMaterialized]
      split_ifs with hr hc <;> try rfl
      cases hp : pivotTyped B r ⟨c, hc⟩ with
      | none => exact ih B U π r (c + 1)
      | some i =>
          have hrec := ih
            (CurrentAdditive.MaterializedGauss.materialize
              (clearTyped (swapTyped B ⟨r, hr⟩ i) ⟨r, hr⟩ ⟨c, hc⟩))
            (clearRows (swapTyped B ⟨r, hr⟩ i)
              (swapTyped U ⟨r, hr⟩ i) ⟨r, hr⟩ ⟨c, hc⟩)
            (fun t => π (Equiv.swap ⟨r, hr⟩ i t)) (r + 1) (c + 1)
          simpa using congrArg
            (fun p : (Fin m → Fin k → ℚ) × List (Fin m × Fin k) =>
              (p.1, (⟨r, hr⟩, ⟨c, hc⟩) :: p.2)) hrec

theorem runTrace_invariant {m k : Nat}
    (A B : Fin m → Fin k → ℚ) (U : Fin m → Fin m → ℚ)
    (π : Fin m → Fin m) (r c fuel : Nat)
    (hrep : Represents A B U) (hs : Support U π r)
    (hπ : Function.Injective π) :
    let out := runTrace B U π r c fuel
    Represents A out.B out.U ∧
      Support out.U out.π (r + out.pivots.length) ∧
      Function.Injective out.π := by
  induction fuel generalizing B U π r c with
  | zero => simpa [runTrace] using ⟨hrep, hs, hπ⟩
  | succ fuel ih =>
      by_cases hr : r < m
      · by_cases hc : c < k
        · simp only [runTrace, dif_pos hr, dif_pos hc]
          cases hp : pivotTyped B r ⟨c, hc⟩ with
          | none => exact ih B U π r (c + 1) hrep hs hπ
          | some i =>
            let rf : Fin m := ⟨r, hr⟩
            let cf : Fin k := ⟨c, hc⟩
            let Bs := swapTyped B rf i
            let Us := swapTyped U rf i
            let πs : Fin m → Fin m := fun t => π (Equiv.swap rf i t)
            let C := CurrentAdditive.MaterializedGauss.materialize
              (clearTyped Bs rf cf)
            let V := clearRows Bs Us rf cf
            have hge : r ≤ i.val := (pivotTyped_spec B r cf i hp).1
            have hrepS : Represents A Bs Us :=
              swapRows_represents A B U rf i hrep
            have hsupS : Support Us πs r :=
              swapRows_support U π rf i hge hs
            have hrepC : Represents A C V := by
              simpa only [C, CurrentAdditive.MaterializedGauss.materialize_eq]
                using clearRows_represents A Bs Us rf cf hrepS
            have hsupC : Support V πs (r + 1) :=
              clearRows_support Bs Us πs rf cf hsupS
            have hinjS : Function.Injective πs := by
              intro a b heq
              exact (Equiv.swap rf i).injective (hπ heq)
            have hrec := ih C V πs (r + 1) (c + 1) hrepC hsupC hinjS
            simpa only [rf, cf, Bs, Us, πs, C, V,
              List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              using hrec
        · simpa [runTrace, hr, hc] using ⟨hrep, hs, hπ⟩
      · simpa [runTrace, hr] using ⟨hrep, hs, hπ⟩

theorem rowLinear_reindex {m k : Nat}
    (A : Fin m → Fin k → ℚ) (U : Fin m → Fin m → ℚ)
    (π : Fin m → Fin m) (hπ : Function.Injective π)
    (i : Fin m) (j : Fin k) :
    rowLinear U A i j = ∑ t : Fin m, U i (π t) * A (π t) j := by
  let e : Fin m ≃ Fin m :=
    Equiv.ofBijective π ⟨hπ, Finite.surjective_of_injective hπ⟩
  calc
    rowLinear U A i j = ∑ t : Fin m, U i t * A t j := rfl
    _ = ∑ t : Fin m, U i (e t) * A (e t) j := by
      exact (Fintype.sum_equiv e
        (fun t : Fin m => U i (e t) * A (e t) j)
        (fun t : Fin m => U i t * A t j)
        (by intro t; rfl)).symm
    _ = ∑ t : Fin m, U i (π t) * A (π t) j := rfl

theorem pivotRow_selected_sum {m k : Nat}
    (A B : Fin m → Fin k → ℚ) (U : Fin m → Fin m → ℚ)
    (π : Fin m → Fin m) (r : Nat)
    (hrep : Represents A B U) (hs : Support U π r)
    (hπ : Function.Injective π)
    (i : Fin m) (hi : i.val < r) (j : Fin k) :
    B i j = ∑ t : {t : Fin m // t.val < r},
      U i (π t.val) * A (π t.val) j := by
  rw [hrep i j, rowLinear_reindex A U π hπ i j]
  have hsum : (∑ t : Fin m, U i (π t) * A (π t) j) =
      ∑ t ∈ Finset.univ.filter (fun t : Fin m => t.val < r),
        U i (π t) * A (π t) j := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro t _
    by_cases ht : t.val < r
    · simp [ht]
    · have hz := hs.pivot i t hi (by omega)
      simp [ht, hz]
  rw [hsum]
  exact Finset.sum_subtype _ (by intro t; simp) _

theorem residualRow_selected_sum {m k : Nat}
    (A B : Fin m → Fin k → ℚ) (U : Fin m → Fin m → ℚ)
    (π : Fin m → Fin m) (r : Nat)
    (hrep : Represents A B U) (hs : Support U π r)
    (hπ : Function.Injective π)
    (i : Fin m) (hi : r ≤ i.val) (j : Fin k) :
    B i j = A (π i) j + ∑ t : {t : Fin m // t.val < r},
      U i (π t.val) * A (π t.val) j := by
  rw [hrep i j, rowLinear_reindex A U π hπ i j]
  have hsum : (∑ t : Fin m, U i (π t) * A (π t) j) =
      (∑ t ∈ Finset.univ.filter (fun t : Fin m => t.val < r),
        U i (π t) * A (π t) j) + A (π i) j := by
    rw [Finset.sum_filter]
    have hfull : (∑ t : Fin m, U i (π t) * A (π t) j) =
        ∑ t : Fin m, ((if t.val < r then U i (π t) * A (π t) j else 0) +
          (if t = i then A (π i) j else 0)) := by
      apply Finset.sum_congr rfl
      intro t _
      by_cases ht : t.val < r
      · have hne : t ≠ i := by
          intro h
          have := congrArg Fin.val h
          omega
        simp [ht, hne]
      · by_cases hti : t = i
        · subst t
          simp [ht, hs.diagonal i hi]
        · have hz := hs.residual i t hi (by omega) hti
          simp [ht, hti, hz]
    rw [hfull]
    rw [Finset.sum_add_distrib]
    simp
  rw [hsum, add_comm]
  congr 1
  exact Finset.sum_subtype _ (by intro t; simp) _

theorem selectedMinor_nonsingular {m k : Nat}
    (A B : Fin m → Fin k → ℚ) (U : Fin m → Fin m → ℚ)
    (π : Fin m → Fin m) (r : Nat)
    (hrep : Represents A B U) (hs : Support U π r)
    (hπ : Function.Injective π)
    (col : {t : Fin m // t.val < r} → Fin k)
    (hunit : ∀ v : {t : Fin m // t.val < r}, ∀ i : Fin m,
      B i (col v) = if i = v.val then 1 else 0) :
    (Matrix.of (fun u v : {t : Fin m // t.val < r} =>
      A (π u.val) (col v))).det ≠ 0 := by
  let ι := {t : Fin m // t.val < r}
  let M : Matrix ι ι ℚ := fun u v => A (π u.val) (col v)
  let V : Matrix ι ι ℚ := fun u v => U u.val (π v.val)
  have hleft : V * M = 1 := by
    ext u v
    have hp := pivotRow_selected_sum A B U π r hrep hs hπ
      u.val u.property (col v)
    rw [hunit v u.val] at hp
    simpa [V, M, Matrix.mul_apply, dotProduct, Matrix.one_apply,
      Subtype.val_inj] using hp.symm
  change M.det ≠ 0
  exact Matrix.det_ne_zero_of_left_inverse hleft

theorem actualPrefix_nonsingular {m k : Nat}
    (A : Fin m → Fin k → ℚ) (fuel : Nat) (hfuel : fuel ≤ k) :
    let out := runTrace A identityRows (fun i => i) 0 0 fuel
    ∃ col : {t : Fin m // t.val < out.pivots.length} → Fin k,
      (∀ v : {t : Fin m // t.val < out.pivots.length}, ∀ i : Fin m,
        out.B i (col v) = if i = v.val then 1 else 0) ∧
      (Matrix.of (fun u v : {t : Fin m // t.val < out.pivots.length} =>
        A (out.π u.val) (col v))).det ≠ 0 := by
  classical
  let out := runTrace A identityRows (fun i => i) 0 0 fuel
  have hinv := runTrace_invariant A A identityRows (fun i => i)
    0 0 fuel (identityRows_represents A) identityRows_support
    (fun _ _ h => h)
  have hrep : Represents A out.B out.U := hinv.1
  have hs : Support out.U out.π out.pivots.length := by
    simpa only [Nat.zero_add] using hinv.2.1
  have hπ : Function.Injective out.π := hinv.2.2
  have heq : (out.B, out.pivots) = echelonTyped A 0 0 fuel :=
    (runTrace_materialized A identityRows (fun i => i) 0 0 fuel).trans
      (CurrentAdditive.MaterializedGauss.echelonMaterialized_eq A 0 0 fuel)
  have hB : out.B = (echelonTyped A 0 0 fuel).1 := congrArg Prod.fst heq
  have hps : out.pivots = (echelonTyped A 0 0 fuel).2 := congrArg Prod.snd heq
  have hbelow : BelowZero A 0 0 := by
    intro i j _ hj
    omega
  have hrows := echelonTyped_pivot_rows A 0 0 fuel (by omega)
  have hunits := echelonTyped_pivot_units A 0 0 fuel
    (by simpa using hfuel) hbelow
  have hcover : ∀ v : {t : Fin m // t.val < out.pivots.length},
      ∃ p ∈ out.pivots, p.1 = v.val := by
    intro v
    have hh := hrows.2 v.val (by omega)
      (by simpa only [Nat.zero_add, ← hps] using v.property)
    simpa only [← hps] using hh
  let pick : {t : Fin m // t.val < out.pivots.length} → Fin m × Fin k :=
    fun v => Classical.choose (hcover v)
  let col : {t : Fin m // t.val < out.pivots.length} → Fin k :=
    fun v => (pick v).2
  have hunit : ∀ v : {t : Fin m // t.val < out.pivots.length},
      ∀ i : Fin m, out.B i (col v) = if i = v.val then 1 else 0 := by
    intro v i
    have hspec := Classical.choose_spec (hcover v)
    have hmem : pick v ∈ out.pivots := hspec.1
    have hrow : (pick v).1 = v.val := hspec.2
    have hu := hunits (pick v) (by simpa only [← hps] using hmem) i
    simpa only [← hB, col, hrow] using hu
  exact ⟨col, hunit, selectedMinor_nonsingular A out.B out.U out.π
    out.pivots.length hrep hs hπ col hunit⟩

end CurrentAdditive.EliminationEntryBounds
