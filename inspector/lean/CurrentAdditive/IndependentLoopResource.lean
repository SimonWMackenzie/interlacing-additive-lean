import CurrentAdditive.IndependentSupport
import CurrentAdditive.SequentialSourceResource

/-!
An exact count of eliminations in the v38 independence-stopping Code D loop.
This counts control-flow iterations; a fixed bit-machine run and its per-step
clock remain separate obligations.
-/

namespace CurrentAdditive.IndependentLoopResource

open IndependentSupport SequentialCode SequentialSourceCode
open SequentialSourceResource

def compressCount {α : Type*}
    (n : Nat) (φ : α → Fin n → ℚ)
    (source : Array (α × ℚ)) : Nat → Option (Array (α × ℚ) × Nat)
  | 0 =>
      match sourceFreeColumn n φ source with
      | none => some (source, 0)
      | some _ => none
  | fuel + 1 =>
      match sourceFreeColumn n φ source with
      | none => some (source, 0)
      | some _ => do
          let next ← compressSourceOnceMaterialized n φ source
          let (out, count) ← compressCount n φ next fuel
          some (out, count + 1)

theorem compressCount_iff {α : Type*}
    (n : Nat) (φ : α → Fin n → ℚ)
    (source : Array (α × ℚ)) (fuel : Nat) :
    (compressCount n φ source fuel).map Prod.fst =
      compressUntilIndependent n φ source fuel := by
  induction fuel generalizing source with
  | zero =>
      simp only [compressCount, compressUntilIndependent]
      cases hf : sourceFreeColumn n φ source with
      | none => simp [hf]
      | some f => simp [hf]
  | succ fuel ih =>
      simp only [compressCount, compressUntilIndependent]
      cases hf : sourceFreeColumn n φ source with
      | none => simp [hf]
      | some f =>
          simp [hf]
          cases hs : compressSourceOnceMaterialized n φ source with
          | none => simp [hs]
          | some next =>
              simp [hs]
              cases hc : compressCount n φ next fuel with
              | none => simp [← ih, hc]
              | some p => simp [← ih, hc]

theorem compressCount_le_fuel {α : Type*}
    (n : Nat) (φ : α → Fin n → ℚ)
    (source out : Array (α × ℚ)) (fuel count : Nat)
    (h : compressCount n φ source fuel = some (out, count)) :
    count ≤ fuel := by
  induction fuel generalizing source out count with
  | zero =>
      simp only [compressCount] at h
      cases hf : sourceFreeColumn n φ source with
      | none => simp [hf] at h; cases h; omega
      | some f => simp [hf] at h
  | succ fuel ih =>
      simp only [compressCount] at h
      cases hf : sourceFreeColumn n φ source with
      | none => simp [hf] at h; cases h; omega
      | some f =>
          cases hs : compressSourceOnceMaterialized n φ source with
          | none => simp [hf, hs] at h
          | some next =>
              simp [hf, hs] at h
              cases hc : compressCount n φ next fuel with
              | none => simp [hc] at h
              | some p =>
                  rcases p with ⟨o, c⟩
                  simp [hc] at h
                  cases h
                  have := ih next o c hc
                  omega

def sequentialCount {Y : Type*} [DecidableEq Y]
    (D : Nat) (alphabet : Array (Y × ℚ)) :
    (q : Nat) → Option (Array ((Fin q → Y) × ℚ) × Nat)
  | 0 => some (#[(Fin.elim0, 1)], 0)
  | q + 1 => do
      let (prev, previousCount) ← sequentialCount D alphabet q
      let extended := appendSource prev alphabet
      let featuresAt := generatedFeatures (q + 1) D (alphabet.map Prod.fst)
      let n := featuresAt.size
      let features : (Fin (q + 1) → Y) → Fin n → ℚ :=
        fun v j => generatedFeatureValue v featuresAt[j]
      let (out, stepCount) ← compressCount n features extended extended.size
      some (out, previousCount + stepCount)

theorem sequentialCount_iff {Y : Type*} [DecidableEq Y]
    (D : Nat) (alphabet : Array (Y × ℚ)) (q : Nat) :
    (sequentialCount D alphabet q).map Prod.fst =
      sequentialIndependent D alphabet q := by
  induction q with
  | zero => rfl
  | succ q ih =>
      simp only [sequentialCount, sequentialIndependent]
      cases hc : sequentialCount D alphabet q with
      | none =>
          simp [hc] at ih
          simp [← ih]
      | some p =>
          rcases p with ⟨prev, previousCount⟩
          simp [hc] at ih
          simp [← ih]
          let extended := appendSource prev alphabet
          let featuresAt := generatedFeatures (q + 1) D (alphabet.map Prod.fst)
          let n := featuresAt.size
          let features : (Fin (q + 1) → Y) → Fin n → ℚ :=
            fun v j => generatedFeatureValue v featuresAt[j]
          have hcomp := compressCount_iff n features extended extended.size
          cases hs : compressCount n features extended extended.size with
          | none =>
              change none = compressUntilIndependent n features extended extended.size
              simpa [hs] using hcomp
          | some result =>
              rcases result with ⟨out, stepCount⟩
              change some out =
                compressUntilIndependent n features extended extended.size
              simpa [hs] using hcomp

theorem sequentialIndependent_size_le_features_all {Y : Type*}
    [DecidableEq Y] (D : Nat) (alphabet : Array (Y × ℚ))
    (q : Nat) (out : Array ((Fin q → Y) × ℚ))
    (h : sequentialIndependent D alphabet q = some out) :
    out.size ≤ (generatedFeatures q D (alphabet.map Prod.fst)).size := by
  cases q with
  | zero =>
      simp [sequentialIndependent] at h
      cases h
      simp [generatedFeatures]
  | succ q =>
      exact sequentialIndependent_size_le_features D alphabet q out h

theorem sequentialCount_le {Y : Type*} [DecidableEq Y]
    (D : Nat) (alphabet : Array (Y × ℚ)) :
    ∀ q (out : Array ((Fin q → Y) × ℚ)) (count : Nat),
      sequentialCount D alphabet q = some (out, count) →
      count ≤ q * alphabet.size *
        (generatedFeatures q D (alphabet.map Prod.fst)).size := by
  intro q
  induction q with
  | zero =>
      intro out count h
      simp [sequentialCount] at h
      rcases h with ⟨_, rfl⟩
      simp
  | succ q ih =>
      intro out count h
      simp only [sequentialCount] at h
      cases hprev : sequentialCount D alphabet q with
      | none => simp [hprev] at h
      | some p =>
          rcases p with ⟨prev, previousCount⟩
          simp [hprev] at h
          let extended := appendSource prev alphabet
          let featuresAt := generatedFeatures (q + 1) D (alphabet.map Prod.fst)
          let n := featuresAt.size
          let features : (Fin (q + 1) → Y) → Fin n → ℚ :=
            fun v j => generatedFeatureValue v featuresAt[j]
          change (do
            let (stageOut, stepCount) ←
              compressCount n features extended extended.size
            some (stageOut, previousCount + stepCount)) = some (out, count) at h
          cases hstep : compressCount n features extended extended.size with
          | none => simp [hstep] at h
          | some result =>
              rcases result with ⟨stageOut, stepCount⟩
              simp [hstep] at h
              rcases h with ⟨_, rfl⟩
              have hprior := ih prev previousCount hprev
              have hprevSource : sequentialIndependent D alphabet q = some prev := by
                have heq := sequentialCount_iff D alphabet q
                simpa [hprev] using heq.symm
              have hprevsize :=
                sequentialIndependent_size_le_features_all
                  D alphabet q prev hprevSource
              have hmono := generatedFeatures_size_mono q D (alphabet.map Prod.fst)
              have hstage :=
                compressCount_le_fuel n features extended stageOut
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

#print axioms compressCount_iff
#print axioms sequentialCount_le

end CurrentAdditive.IndependentLoopResource
