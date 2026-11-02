import CurrentAdditive.IndependentLoopResource

/-!
Literal successful Gauss-test counts for v39 Code D.  Every dependence test
is counted, including the last test which finds independent columns.  These
are control-flow counts, not a physical bit-machine clock.
-/

namespace CurrentAdditive.IndependentGaussCalls

open IndependentSupport SequentialCode SequentialSourceCode
open IndependentLoopResource

def compressTests {α : Type*} (n : Nat) (φ : α → Fin n → ℚ)
    (source : Array (α × ℚ)) : Nat → Option (Array (α × ℚ) × Nat)
  | 0 =>
      match sourceFreeColumn n φ source with
      | none => some (source, 1)
      | some _ => none
  | fuel + 1 =>
      match sourceFreeColumn n φ source with
      | none => some (source, 1)
      | some _ => do
          let next ← compressSourceOnceMaterialized n φ source
          let (out, calls) ← compressTests n φ next fuel
          some (out, calls + 1)

theorem compressTests_eq {α : Type*} (n : Nat) (φ : α → Fin n → ℚ)
    (source : Array (α × ℚ)) (fuel : Nat) :
    compressTests n φ source fuel =
      (compressCount n φ source fuel).map (fun p => (p.1, p.2 + 1)) := by
  induction fuel generalizing source with
  | zero =>
      simp only [compressTests, compressCount]
      cases sourceFreeColumn n φ source <;> rfl
  | succ fuel ih =>
      simp only [compressTests, compressCount]
      cases hf : sourceFreeColumn n φ source with
      | none => simp
      | some f =>
          simp only
          cases hs : compressSourceOnceMaterialized n φ source with
          | none => simp
          | some next =>
              dsimp only [bind, Option.bind]
              rw [ih]
              cases hc : compressCount n φ next fuel with
              | none => simp
              | some p => rcases p with ⟨out, count⟩; simp

theorem compressTests_iff {α : Type*} (n : Nat) (φ : α → Fin n → ℚ)
    (source : Array (α × ℚ)) (fuel : Nat) :
    (compressTests n φ source fuel).map Prod.fst =
      compressUntilIndependent n φ source fuel := by
  rw [compressTests_eq, Option.map_map]
  exact compressCount_iff n φ source fuel

theorem compressTests_le {α : Type*} (n : Nat) (φ : α → Fin n → ℚ)
    (source out : Array (α × ℚ)) (fuel calls : Nat)
    (h : compressTests n φ source fuel = some (out, calls)) :
    1 ≤ calls ∧ calls ≤ fuel + 1 := by
  rw [compressTests_eq] at h
  cases hc : compressCount n φ source fuel with
  | none => simp [hc] at h
  | some p =>
      rcases p with ⟨o, count⟩
      simp [hc] at h
      rcases h with ⟨rfl, rfl⟩
      have hb := compressCount_le_fuel n φ source o fuel count hc
      omega

def sequentialTests {Y : Type*} [DecidableEq Y]
    (D : Nat) (alphabet : Array (Y × ℚ)) :
    (q : Nat) → Option (Array ((Fin q → Y) × ℚ) × Nat)
  | 0 => some (#[(Fin.elim0, 1)], 0)
  | q + 1 => do
      let (prev, previousCalls) ← sequentialTests D alphabet q
      let extended := appendSource prev alphabet
      let featuresAt := generatedFeatures (q + 1) D (alphabet.map Prod.fst)
      let n := featuresAt.size
      let features : (Fin (q + 1) → Y) → Fin n → ℚ :=
        fun v j => generatedFeatureValue v featuresAt[j]
      let (out, stepCalls) ← compressTests n features extended extended.size
      some (out, previousCalls + stepCalls)

/-- Each completed stage makes one more Gaussian test than successful
eliminations, independently of whether it made any elimination at all. -/
theorem sequentialTests_eq {Y : Type*} [DecidableEq Y]
    (D : Nat) (alphabet : Array (Y × ℚ)) (q : Nat) :
    sequentialTests D alphabet q =
      (sequentialCount D alphabet q).map (fun p => (p.1, p.2 + q)) := by
  induction q with
  | zero => rfl
  | succ q ih =>
      simp only [sequentialTests, sequentialCount]
      rw [ih]
      cases hp : sequentialCount D alphabet q with
      | none => simp
      | some p =>
          rcases p with ⟨prev, previousCount⟩
          simp only [Option.map_some]
          dsimp only [bind, Option.bind]
          rw [compressTests_eq]
          cases hs : compressCount
              (generatedFeatures (q + 1) D (alphabet.map Prod.fst)).size
              (fun v j => generatedFeatureValue v
                (generatedFeatures (q + 1) D (alphabet.map Prod.fst))[j])
              (appendSource prev alphabet) (appendSource prev alphabet).size with
          | none => simp
          | some p =>
              rcases p with ⟨out, count⟩
              simp only [Option.map_some]
              congr 2 <;> omega

theorem sequentialTests_iff {Y : Type*} [DecidableEq Y]
    (D : Nat) (alphabet : Array (Y × ℚ)) (q : Nat) :
    (sequentialTests D alphabet q).map Prod.fst =
      sequentialIndependent D alphabet q := by
  rw [sequentialTests_eq, Option.map_map]
  exact sequentialCount_iff D alphabet q

/-- At most q*m*P eliminations and q terminal tests are made. -/
theorem sequentialTests_le {Y : Type*} [DecidableEq Y]
    (D : Nat) (alphabet : Array (Y × ℚ))
    (q : Nat) (out : Array ((Fin q → Y) × ℚ)) (calls : Nat)
    (h : sequentialTests D alphabet q = some (out, calls)) :
    q ≤ calls ∧ calls ≤ q *
      (alphabet.size * (generatedFeatures q D (alphabet.map Prod.fst)).size + 1) := by
  rw [sequentialTests_eq] at h
  cases hc : sequentialCount D alphabet q with
  | none => simp [hc] at h
  | some p =>
      rcases p with ⟨o, count⟩
      simp [hc] at h
      rcases h with ⟨rfl, rfl⟩
      have hb := sequentialCount_le D alphabet q o count hc
      constructor
      · omega
      · calc
          count + q ≤ q * alphabet.size *
              (generatedFeatures q D (alphabet.map Prod.fst)).size + q := by omega
          _ = q * (alphabet.size *
              (generatedFeatures q D (alphabet.map Prod.fst)).size + 1) := by ring

#print axioms compressTests_eq
#print axioms compressTests_iff
#print axioms compressTests_le
#print axioms sequentialTests_eq
#print axioms sequentialTests_iff
#print axioms sequentialTests_le

end CurrentAdditive.IndependentGaussCalls
