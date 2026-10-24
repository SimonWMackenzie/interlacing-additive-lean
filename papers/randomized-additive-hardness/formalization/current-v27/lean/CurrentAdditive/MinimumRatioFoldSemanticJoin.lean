import CurrentAdditive.MinimumRatioCallbackSemantic
import CurrentAdditive.SequentialCode
import CurrentAdditive.GaussPacket

/-! The exact ordered list a future physical ratio controller must traverse.
This proves its semantic fold agrees with the source algorithm's minimum. -/

namespace CurrentAdditive.MinimumRatioFoldSemanticJoin

open CurrentAdditive.CodeDCodec

def pairAt (weights coeff : Array ℚ) (i : Nat) : RawRat × RawRat :=
  (GaussPhysical.rawOfRat (weights[i]?.getD 0),
   GaussPhysical.rawOfRat (coeff[i]?.getD 0))

def pairs (weights coeff : Array ℚ) : List (RawRat × RawRat) :=
  (List.range (min weights.size coeff.size)).map (pairAt weights coeff)

def semanticFold (xs : List (RawRat × RawRat)) : Option ℚ :=
  xs.foldl (fun best p =>
    MinimumRatioStepSpec.semanticStep best p.1.value p.2.value) none

private theorem semanticStep_eq_source (best : Option ℚ) (w c : ℚ) :
    MinimumRatioStepSpec.semanticStep best w c =
      (if 0 < c then
        let ratio := w / c
        match best with
        | none => some ratio
        | some previous => some (min previous ratio)
      else best) := by
  by_cases hc : 0 < c
  · cases best with
    | none => simp [MinimumRatioStepSpec.semanticStep, hc]
    | some old =>
        by_cases hl : w / c < old
        · simp [MinimumRatioStepSpec.semanticStep, hc, hl,
            min_eq_right (le_of_lt hl)]
        · have hle : old ≤ w / c := le_of_not_gt hl
          simp [MinimumRatioStepSpec.semanticStep, hc, hl,
            min_eq_left hle]
  · simp [MinimumRatioStepSpec.semanticStep, hc]

theorem pairs_valid (weights coeff : Array ℚ) :
    ∀ p ∈ pairs weights coeff, p.1.Valid ∧ p.2.Valid := by
  intro p hp
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
  exact ⟨GaussPhysical.rawOfRat_valid _, GaussPhysical.rawOfRat_valid _⟩

theorem semanticFold_eq_minimumRatio (weights coeff : Array ℚ) :
    semanticFold (pairs weights coeff) =
      SequentialCode.minimumRatio weights coeff := by
  let xs := List.range (min weights.size coeff.size)
  have hfold : ∀ (ys : List Nat) (best : Option ℚ),
      (ys.map (pairAt weights coeff)).foldl
        (fun b p => MinimumRatioStepSpec.semanticStep b p.1.value p.2.value)
        best =
      ys.foldl (fun b i =>
        let ai := coeff[i]?.getD 0
        if 0 < ai then
          let ratio := (weights[i]?.getD 0) / ai
          match b with
          | none => some ratio
          | some previous => some (min previous ratio)
        else b) best := by
    intro ys
    induction ys with
    | nil => intro best; rfl
    | cons i rest ih =>
        intro best
        simp only [List.map_cons, List.foldl_cons]
        rw [show (pairAt weights coeff i).1.value =
          weights[i]?.getD 0 by simp [pairAt, GaussPhysical.rawOfRat_value],
          show (pairAt weights coeff i).2.value =
          coeff[i]?.getD 0 by simp [pairAt, GaussPhysical.rawOfRat_value],
          semanticStep_eq_source]
        exact ih _
  simpa only [semanticFold, pairs, SequentialCode.minimumRatio]
    using hfold xs none

#print axioms pairs_valid
#print axioms semanticFold_eq_minimumRatio

end CurrentAdditive.MinimumRatioFoldSemanticJoin
