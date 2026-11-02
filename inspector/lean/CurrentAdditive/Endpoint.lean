import CurrentAdditive.CandidateBitsLocal
import CurrentAdditive.GaussTypedPacket
import CurrentAdditive.MaterializedGauss

/-!
Private postloop contract for the physical Gauss certificate endpoint.

The matrix and pivot list are actual finite words. This file establishes the
representation and the exact short lookup formula to be implemented by TM2.
It does not claim that a TM2 program computes the endpoint yet.
-/

namespace CurrentAdditive.GaussCertificateProbe

open CurrentAdditive.CodeDCodec
open CurrentAdditive.GaussPhysical
open CurrentAdditive.SequentialTotality
open CurrentAdditive.RationalBitBounds
open EthInapproximability.CurrentPaper

def pairBank (r c : Nat) : BitMachineBankCodec.Bank 2 :=
  ![List.replicate r true, List.replicate c true]

def encodePair (r c : Nat) : List Bool :=
  BitMachineBankCodec.encode (pairBank r c)

def decodePair (w : List Bool) : Option (Nat × Nat) := do
  let S ← BitMachineBankCodec.decode 2 w
  pure ((S 0).length, (S 1).length)

theorem decodePair_encodePair (r c : Nat) :
    decodePair (encodePair r c) = some (r, c) := by
  simp [decodePair, encodePair, pairBank,
    BitMachineBankCodec.decode_encode]

def encodePivots (ps : List (Nat × Nat)) : List Bool :=
  CodeDCodecV2.encodeItems (ps.map fun p => encodePair p.1 p.2)

def decodePivots (w : List Bool) : Option (List (Nat × Nat)) := do
  let xs ← CodeDCodecV2.decodeItems w
  xs.mapM decodePair

theorem decodePivots_encodePivots (ps : List (Nat × Nat)) :
    decodePivots (encodePivots ps) = some ps := by
  have h : ∀ xs : List (Nat × Nat),
      (xs.map (fun p => encodePair p.1 p.2)).mapM decodePair = some xs := by
    intro xs
    induction xs with
    | nil => rfl
    | cons p xs ih =>
        rcases p with ⟨r, c⟩
        simp [List.mapM_cons, decodePair_encodePair, ih]
  simpa [decodePivots, encodePivots,
    CodeDCodecV2.decodeItems_encodeItems] using h ps

def encodeTypedPivots {m k : Nat} (ps : List (Fin m × Fin k)) : List Bool :=
  encodePivots (ps.map fun p => (p.1.val, p.2.val))

theorem decodeTypedPivots {m k : Nat} (ps : List (Fin m × Fin k)) :
    decodePivots (encodeTypedPivots ps) =
      some (ps.map fun p => (p.1.val, p.2.val)) :=
  decodePivots_encodePivots _

def stateBank (matrix : List Bool) (r c : Nat) (ps : List (Nat × Nat)) :
    BitMachineBankCodec.Bank 4 :=
  ![matrix, List.replicate r true, List.replicate c true, encodePivots ps]

def encodeState (matrix : List Bool) (r c : Nat)
    (ps : List (Nat × Nat)) : List Bool :=
  BitMachineBankCodec.encode (stateBank matrix r c ps)

def decodeState (w : List Bool) :
    Option (List Bool × Nat × Nat × List (Nat × Nat)) := do
  let S ← BitMachineBankCodec.decode 4 w
  let ps ← decodePivots (S 3)
  pure (S 0, (S 1).length, (S 2).length, ps)

theorem decodeState_encodeState (matrix : List Bool) (r c : Nat)
    (ps : List (Nat × Nat)) :
    decodeState (encodeState matrix r c ps) = some (matrix, r, c, ps) := by
  simp [decodeState, encodeState, stateBank,
    BitMachineBankCodec.decode_encode, decodePivots_encodePivots]

def firstFreeNat (k : Nat) (ps : List (Nat × Nat)) : Option Nat :=
  (List.range k).find? (fun c => decide (c ∉ ps.map Prod.snd))

private theorem find_map {α β : Type*} (xs : List α) (f : α → β)
    (p : β → Bool) :
    (xs.map f).find? p = (xs.find? (p ∘ f)).map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      by_cases hp : p (f x) = true <;> simp [List.find?, hp, ih]

theorem firstFreeNat_typed {m k : Nat}
    (ps : List (Fin m × Fin k)) :
    firstFreeNat k (ps.map fun p => (p.1.val, p.2.val)) =
      (typedFree ps).map Fin.val := by
  unfold firstFreeNat typedFree
  rw [← List.map_coe_finRange_eq_range, find_map]
  congr 1
  have hp : (fun f : Fin k =>
      decide (f.val ∉ (ps.map fun p => (p.1.val, p.2.val)).map Prod.snd)) =
      (fun f : Fin k => decide (f ∉ ps.map Prod.snd)) := by
    funext f
    simp [List.mem_map, Fin.val_inj]
  exact congrArg (fun p => List.find? p (List.finRange k)) hp

/-- The coefficient can be read by one pivot-list scan and at most one
matrix getter, provided pivot columns are distinct. -/
def candidateAt {m k : Nat} (B : Fin m → Fin k → ℚ)
    (ps : List (Fin m × Fin k)) (f j : Fin k) : ℚ :=
  if j = f then 1 else
    match ps.find? (fun p => decide (p.2 = j)) with
    | some p => -B p.1 f
    | none => 0

theorem candidateAt_eq_typedCandidate {m k : Nat}
    (B : Fin m → Fin k → ℚ) (ps : List (Fin m × Fin k))
    (f : Fin k) (hfree : f ∉ ps.map Prod.snd)
    (hcol : Function.Injective (fun p : PivotIndex ps => p.val.2))
    (j : Fin k) :
    candidateAt B ps f j = typedCandidate B ps f j := by
  by_cases hjf : j = f
  · subst j
    simp [candidateAt, typedCandidate_at_free B ps f hfree]
  · cases hp : ps.find? (fun p => decide (p.2 = j)) with
    | some p =>
        have hmem : p ∈ ps := List.mem_of_find?_eq_some hp
        have hcolp : p.2 = j := by
          simpa using List.find?_some hp
        let p0 : PivotIndex ps := ⟨p, List.mem_toFinset.mpr hmem⟩
        have htyped := typedCandidate_at_pivot B ps f hfree hcol p0
        simpa [candidateAt, hjf, hp, p0, hcolp] using htyped.symm
    | none =>
        have hjnot : j ∉ ps.map Prod.snd := by
          intro hmem
          obtain ⟨p, hmem, hpj⟩ := List.mem_map.mp hmem
          have hfalse := (List.find?_eq_none.mp hp) p hmem
          simp [hpj] at hfalse
        simpa [candidateAt, hjf, hp] using
          (typedCandidate_off_pivots B ps f j hjf hjnot).symm

/-- A first-free-column scan followed by the physical pivot lookup computes
the exact array passed to the existing dependence checker. -/
def fastPostloop {m k : Nat} (B : Fin m → Fin k → ℚ)
    (ps : List (Fin m × Fin k)) : Option (Array ℚ) :=
  (typedFree ps).map fun f => Array.ofFn (candidateAt B ps f)

theorem fastPostloop_eq_on_echelon {m k : Nat}
    (A : Fin m → Fin k → ℚ) :
    let out := CurrentAdditive.MaterializedGauss.echelonMaterialized A 0 0 k
    fastPostloop out.1 out.2 =
      (CurrentAdditive.MaterializedGauss.dependenceMaterialized A).map Array.ofFn := by
  let out := CurrentAdditive.MaterializedGauss.echelonMaterialized A 0 0 k
  have hunit : ∀ p ∈ out.2, ∀ i : Fin m,
      out.1 i p.2 = if i = p.1 then 1 else 0 := by
    simpa [out, CurrentAdditive.MaterializedGauss.echelonMaterialized_eq] using
      (echelonTyped_pivot_units A 0 0 k (by simp)
        (by intro i j _ hj; omega))
  have hnodup : (out.2.map Prod.fst).Nodup := by
    simpa [out, CurrentAdditive.MaterializedGauss.echelonMaterialized_eq] using
      echelonTyped_pivot_rows_nodup A 0 0 k
  have hcol : Function.Injective (fun p : PivotIndex out.2 => p.val.2) :=
    pivot_columns_injective out.1 out.2 hunit hnodup
  dsimp only [fastPostloop, CurrentAdditive.MaterializedGauss.dependenceMaterialized]
  rw [Option.map_map]
  change (typedFree out.2).map
      (fun f => Array.ofFn (candidateAt out.1 out.2 f)) =
    (typedFree out.2).map
      (fun f => Array.ofFn (typedCandidate out.1 out.2 f))
  cases hf : typedFree out.2 with
  | none => simp
  | some f =>
      have hfree := typedFree_spec out.2 f hf
      simp only [Option.map_some, Option.some.injEq]
      congr 1
      funext j
      exact candidateAt_eq_typedCandidate out.1 out.2 f hfree hcol j

theorem fastPostloop_eq_materializedArrayDependence
    (a : Array (Array ℚ)) :
    let out := CurrentAdditive.MaterializedGauss.echelonMaterialized
      (CurrentAdditive.SequentialArrayBridge.matrixOfArray a) 0 0
      (CurrentAdditive.SequentialCode.columnCount a)
    fastPostloop out.1 out.2 =
      CurrentAdditive.MaterializedGauss.materializedArrayDependence a := by
  simpa only [CurrentAdditive.MaterializedGauss.materializedArrayDependence] using
    fastPostloop_eq_on_echelon
      (CurrentAdditive.SequentialArrayBridge.matrixOfArray a)

theorem fastPostloop_check (a : Array (Array ℚ))
    (h : a.size < CurrentAdditive.SequentialCode.columnCount a) :
    let out := CurrentAdditive.MaterializedGauss.echelonMaterialized
      (CurrentAdditive.SequentialArrayBridge.matrixOfArray a) 0 0
      (CurrentAdditive.SequentialCode.columnCount a)
    ∃ x, fastPostloop out.1 out.2 = some x ∧
      CurrentAdditive.SequentialCode.dependenceCheck a x = true := by
  dsimp only
  rw [fastPostloop_eq_materializedArrayDependence]
  rw [CurrentAdditive.MaterializedGauss.materializedArrayDependence_eq]
  exact CurrentAdditive.SequentialArrayBridge.typedArrayDependence_check a h

def checkedFastPostloop (a : Array (Array ℚ)) :
    Option {x : Array ℚ // CurrentAdditive.SequentialCode.IsDependence a x} :=
  let out := CurrentAdditive.MaterializedGauss.echelonMaterialized
    (CurrentAdditive.SequentialArrayBridge.matrixOfArray a) 0 0
    (CurrentAdditive.SequentialCode.columnCount a)
  match fastPostloop out.1 out.2 with
  | none => none
  | some x =>
      if h : CurrentAdditive.SequentialCode.dependenceCheck a x = true then
        some ⟨x, h⟩ else none

theorem checkedFastPostloop_eq (a : Array (Array ℚ)) :
    checkedFastPostloop a =
      CurrentAdditive.MaterializedGauss.certifiedMaterializedDependence a := by
  simp only [checkedFastPostloop,
    CurrentAdditive.MaterializedGauss.certifiedMaterializedDependence,
    CurrentAdditive.MaterializedGauss.materializedArrayDependence]
  rw [fastPostloop_eq_on_echelon]
  rfl

theorem checkedFastPostloop_total (a : Array (Array ℚ))
    (h : a.size < CurrentAdditive.SequentialCode.columnCount a) :
    ∃ cert, checkedFastPostloop a = some cert := by
  rw [checkedFastPostloop_eq]
  exact CurrentAdditive.MaterializedGauss.certifiedMaterializedDependence_total a h

#print axioms fastPostloop_check
#print axioms checkedFastPostloop_total

end CurrentAdditive.GaussCertificateProbe
