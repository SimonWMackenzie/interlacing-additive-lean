import CurrentAdditive.SequentialFiniteLaw

/-!
Structural resource counts for the literal executable sequential source.
These count array entries and successful elimination calls; bit operations
and a physical machine clock are separate proof obligations.
-/

namespace CurrentAdditive.SequentialSourceResource

open SequentialCode SequentialSourceCode

theorem appendSource_size {Y : Type*} {q : Nat}
    (source : Array ((Fin q → Y) × ℚ))
    (alphabet : Array (Y × ℚ)) :
    (appendSource source alphabet).size = source.size * alphabet.size := by
  let step : Array ((Fin (q + 1) → Y) × ℚ) →
      ((Fin q → Y) × ℚ) → Array ((Fin (q + 1) → Y) × ℚ) :=
    fun out x => out ++ alphabet.map (fun y =>
      (appendWord x.1 y.1, x.2 * y.2))
  have hfold (xs : List ((Fin q → Y) × ℚ))
      (out : Array ((Fin (q + 1) → Y) × ℚ)) :
      (xs.foldl step out).size = out.size + xs.length * alphabet.size := by
    induction xs generalizing out with
    | nil => simp
    | cons x xs ih =>
        simp only [List.foldl_cons, List.length_cons]
        rw [ih]
        simp [step, Nat.succ_mul]
        omega
  unfold appendSource
  rw [← Array.foldl_toList]
  simpa [step] using hfold source.toList #[]

/-- Count only successful eliminations in the literal fuel recursion. -/
def compressSourceFuelCount {α : Type*}
    (n : Nat) (φ : α → Fin n → ℚ)
    (source : Array (α × ℚ)) : Nat → Option (Array (α × ℚ) × Nat)
  | 0 => if source.size ≤ n then some (source, 0) else none
  | fuel + 1 =>
      if source.size ≤ n then some (source, 0) else do
        let next ← compressSourceOnceMaterialized n φ source
        let (out, count) ← compressSourceFuelCount n φ next fuel
        some (out, count + 1)

theorem compressSourceFuelCount_iff {α : Type*}
    (n : Nat) (φ : α → Fin n → ℚ)
    (source : Array (α × ℚ)) (fuel : Nat) :
    (compressSourceFuelCount n φ source fuel).map Prod.fst =
      compressSourceFuelMaterialized n φ source fuel := by
  induction fuel generalizing source with
  | zero =>
      simp [compressSourceFuelCount, compressSourceFuelMaterialized]
  | succ fuel ih =>
      simp only [compressSourceFuelCount, compressSourceFuelMaterialized]
      split_ifs with hs
      · simp
      · cases hstep : compressSourceOnceMaterialized n φ source with
        | none => simp
        | some next =>
            simp
            cases hc : compressSourceFuelCount n φ next fuel with
            | none => simp [← ih, hc]
            | some p => simp [← ih, hc]

theorem compressSourceFuelCount_le_fuel {α : Type*}
    (n : Nat) (φ : α → Fin n → ℚ)
    (source out : Array (α × ℚ)) (fuel count : Nat)
    (h : compressSourceFuelCount n φ source fuel = some (out, count)) :
    count ≤ fuel := by
  induction fuel generalizing source out count with
  | zero =>
      simp only [compressSourceFuelCount] at h
      split_ifs at h
      cases h
      omega
  | succ fuel ih =>
      simp only [compressSourceFuelCount] at h
      split_ifs at h
      · cases h; omega
      · cases hstep : compressSourceOnceMaterialized n φ source with
        | none => simp [hstep] at h
        | some next =>
            simp [hstep] at h
            cases hc : compressSourceFuelCount n φ next fuel with
            | none => simp [hc] at h
            | some p =>
                cases p with
                | mk o c =>
                    simp [hc] at h
                    cases h
                    have := ih next o c hc
                    omega

theorem generatedFeatures_size_mono {Y : Type*}
    (q D : Nat) (alphabet : Array Y) :
    (generatedFeatures q D alphabet).size ≤
      (generatedFeatures (q + 1) D alphabet).size := by
  rw [SequentialFeatureCoverage.generatedFeatures_succ]
  unfold extendFeatures
  simp

def sequentialMaterializedCount {Y : Type*} [DecidableEq Y]
    (D : Nat) (alphabet : Array (Y × ℚ)) :
    (q : Nat) → Option (Array ((Fin q → Y) × ℚ) × Nat)
  | 0 => some (#[(Fin.elim0, 1)], 0)
  | q + 1 => do
      let (prev, previousCount) ← sequentialMaterializedCount D alphabet q
      let extended := appendSource prev alphabet
      let featuresAt := generatedFeatures (q + 1) D (alphabet.map Prod.fst)
      let n := featuresAt.size
      let features : (Fin (q + 1) → Y) → Fin n → ℚ :=
        fun v j => generatedFeatureValue v featuresAt[j]
      let (out, stepCount) ← compressSourceFuelCount n features extended extended.size
      some (out, previousCount + stepCount)

theorem sequentialMaterializedCount_iff {Y : Type*} [DecidableEq Y]
    (D : Nat) (alphabet : Array (Y × ℚ)) (q : Nat) :
    (sequentialMaterializedCount D alphabet q).map Prod.fst =
      sequentialMaterialized D alphabet q := by
  induction q with
  | zero => rfl
  | succ q ih =>
      simp only [sequentialMaterializedCount, sequentialMaterialized]
      cases hc : sequentialMaterializedCount D alphabet q with
      | none =>
          simp [hc] at ih
          simp [← ih]
      | some p =>
          cases p with
          | mk prev previousCount =>
              simp [hc] at ih
              simp [← ih]
              let extended := appendSource prev alphabet
              let featuresAt := generatedFeatures (q + 1) D (alphabet.map Prod.fst)
              let n := featuresAt.size
              let features : (Fin (q + 1) → Y) → Fin n → ℚ :=
                fun v j => generatedFeatureValue v featuresAt[j]
              have hcomp := compressSourceFuelCount_iff n features extended extended.size
              cases hs : compressSourceFuelCount n features extended extended.size with
              | none =>
                  change none = compressSourceFuelMaterialized n features extended extended.size
                  simpa [hs] using hcomp
              | some result =>
                  cases result with
                  | mk out stepCount =>
                      change some out = compressSourceFuelMaterialized n features extended extended.size
                      simpa [hs] using hcomp

theorem sequentialMaterialized_size_le_features_all {Y : Type*}
    [DecidableEq Y] (D : Nat) (alphabet : Array (Y × ℚ))
    (q : Nat) (out : Array ((Fin q → Y) × ℚ))
    (h : sequentialMaterialized D alphabet q = some out) :
    out.size ≤ (generatedFeatures q D (alphabet.map Prod.fst)).size := by
  cases q with
  | zero =>
      simp [sequentialMaterialized] at h
      cases h
      simp [generatedFeatures]
  | succ q =>
      exact sequentialMaterialized_size_le_features D alphabet q out h

theorem sequentialMaterializedCount_le {Y : Type*} [DecidableEq Y]
    (D : Nat) (alphabet : Array (Y × ℚ)) :
    ∀ q (out : Array ((Fin q → Y) × ℚ)) (count : Nat),
      sequentialMaterializedCount D alphabet q = some (out, count) →
      count ≤ q * alphabet.size *
        (generatedFeatures q D (alphabet.map Prod.fst)).size := by
  intro q
  induction q with
  | zero =>
      intro out count h
      simp [sequentialMaterializedCount] at h
      rcases h with ⟨_, rfl⟩
      simp
  | succ q ih =>
      intro out count h
      simp only [sequentialMaterializedCount] at h
      cases hprev : sequentialMaterializedCount D alphabet q with
      | none => simp [hprev] at h
      | some p =>
          cases p with
          | mk prev previousCount =>
              simp [hprev] at h
              let extended := appendSource prev alphabet
              let featuresAt := generatedFeatures (q + 1) D (alphabet.map Prod.fst)
              let n := featuresAt.size
              let features : (Fin (q + 1) → Y) → Fin n → ℚ :=
                fun v j => generatedFeatureValue v featuresAt[j]
              change (do
                let (stageOut, stepCount) ←
                  compressSourceFuelCount n features extended extended.size
                some (stageOut, previousCount + stepCount)) = some (out, count) at h
              cases hstep : compressSourceFuelCount n features extended extended.size with
              | none => simp [hstep] at h
              | some result =>
                  cases result with
                  | mk stageOut stepCount =>
                      simp [hstep] at h
                      rcases h with ⟨_, rfl⟩
                      have hprior := ih prev previousCount hprev
                      have hprevSource : sequentialMaterialized D alphabet q = some prev := by
                        have heq := sequentialMaterializedCount_iff D alphabet q
                        simpa [hprev] using heq.symm
                      have hprevsize :=
                        sequentialMaterialized_size_le_features_all D alphabet q prev hprevSource
                      have hmono := generatedFeatures_size_mono q D (alphabet.map Prod.fst)
                      have hstage :=
                        compressSourceFuelCount_le_fuel n features extended stageOut
                          extended.size stepCount hstep
                      rw [appendSource_size] at hstage
                      have hprior' : previousCount ≤ q * alphabet.size * featuresAt.size := by
                        exact hprior.trans (Nat.mul_le_mul_left _ hmono)
                      have hstage' : stepCount ≤ featuresAt.size * alphabet.size := by
                        exact hstage.trans
                          (Nat.mul_le_mul_right _ (hprevsize.trans hmono))
                      change previousCount + stepCount ≤
                        (q + 1) * alphabet.size * featuresAt.size
                      have hidentity : (q + 1) * alphabet.size * featuresAt.size =
                          q * alphabet.size * featuresAt.size +
                            featuresAt.size * alphabet.size := by ring
                      rw [hidentity]
                      omega

#print axioms appendSource_size
#print axioms compressSourceFuelCount_iff
#print axioms compressSourceFuelCount_le_fuel
#print axioms generatedFeatures_size_mono
#print axioms sequentialMaterializedCount_iff
#print axioms sequentialMaterializedCount_le

end CurrentAdditive.SequentialSourceResource
