import CurrentAdditive.GaussAnyWidthFirstFree

namespace CurrentAdditive.GaussDependentPrefix

open CurrentAdditive.SequentialTotality
open CurrentAdditive.MaterializedGauss
open CurrentAdditive.GaussPivotPrefixPhysical
open CurrentAdditive.GaussFirstFreeArithmetic
open CurrentAdditive.GaussFirstFreeCandidate
open CurrentAdditive.RationalBitBounds
open CurrentAdditive.GaussDirectPostloop (natPivots materialized_pivot_left_zero)

/-! Exact first-free candidate facts for actual dependent Gauss outputs at any
width. The bound uses the prefix of diagonal pivots, not an arbitrary free
column, and covers dependent systems even when columns are at most rows. -/

theorem prefixFacts {m k : Nat} (A : Fin m → Fin k → ℚ)
    (hdependent : typedFree (GaussControlTrace.after A k).pivots ≠ none) :
    let s := GaussControlTrace.after A k
    let nps := natPivots s.pivots
    let f := prefixCount nps
    f ≤ m ∧ f < k ∧
      (List.range k).find? (fun c => decide (c ∉ nps.map Prod.snd)) = some f ∧
      (∀ j < f, (j,j) ∈ nps) := by
  let s := GaussControlTrace.after A k
  let nps := natPivots s.pivots
  let f := prefixCount nps
  have hselect := GaussAnyWidthFirstFree.after_typedFree_eq_prefix_or_none A
  change (typedFree s.pivots).map Fin.val =
    (if _h : f < k then some f else none) at hselect
  have hfk : f < k := by
    by_contra hn
    cases ht : typedFree s.pivots with
    | none => exact hdependent ht
    | some g => simp [ht, hn] at hselect
  have hfirst := GaussCertificateProbe.firstFreeNat_typed s.pivots
  have hf : (List.range k).find? (fun c => decide (c ∉ nps.map Prod.snd)) =
      some f := by
    simpa [GaussCertificateProbe.firstFreeNat, nps, natPivots, hfk] using
      hfirst.trans hselect
  have hcount := GaussControlTrace.after_pivotCount A k
  have hrowle := GaussControlTrace.after_row_le A k
  have hrows := GaussTraceInvariants.after_rows A k
  have hrows' : nps.map Prod.fst = List.range' 0 nps.length := by
    simpa [nps, natPivots, hcount, List.range'_eq_map_range] using hrows
  have hf_le : f ≤ nps.length := by
    unfold f prefixCount
    exact (List.takeWhile_sublist id).length_le.trans_eq (by simp [pivotFlags])
  have hfm : f ≤ m := by
    have hc : s.r = s.pivots.length := hcount
    have hm : s.r ≤ m := hrowle
    have hl : f ≤ s.pivots.length := by simpa [nps, natPivots] using hf_le
    omega
  have hdiag : ∀ j < f, (j,j) ∈ nps := by
    intro j hj
    exact GaussPivotPrefixRows.diagonal_pairs_in_prefix 0 nps hrows'
      j (by omega) (by omega)
  exact ⟨hfm, hfk, hf, hdiag⟩
theorem selectedFree {m k : Nat} (A : Fin m → Fin k → ℚ)
    (hdependent : typedFree (GaussControlTrace.after A k).pivots ≠ none) :
    let s := GaussControlTrace.after A k
    let fval := prefixCount (natPivots s.pivots)
    ∃ hlt : fval < k,
      typedFree s.pivots = some ⟨fval, hlt⟩ := by
  let s := GaussControlTrace.after A k
  let fval := prefixCount (natPivots s.pivots)
  have hfacts := prefixFacts A hdependent
  have hlt : fval < k := hfacts.2.1
  have hfirst : GaussCertificateProbe.firstFreeNat k
      (natPivots s.pivots) = some fval := by
    simpa [GaussCertificateProbe.firstFreeNat] using hfacts.2.2.1
  have hbridge : GaussCertificateProbe.firstFreeNat k
      (natPivots s.pivots) = (typedFree s.pivots).map Fin.val := by
    simpa [natPivots] using
      (GaussCertificateProbe.firstFreeNat_typed s.pivots)
  rw [hfirst] at hbridge
  cases ht : typedFree s.pivots with
  | none => simp [ht] at hbridge
  | some g =>
      have hval : g.val = fval := by simpa [ht] using hbridge.symm
      have hgf : g = (⟨fval, hlt⟩ : Fin k) := Fin.ext hval
      change ∃ hlt : fval < k, typedFree s.pivots = some ⟨fval, hlt⟩
      exact ⟨hlt, by simpa [hgf] using ht⟩

theorem directCandidate_on_materialized {m k : Nat}
    (A : Fin m → Fin k → ℚ) (hdependent : typedFree (GaussControlTrace.after A k).pivots ≠ none) :
    let out := echelonMaterialized A 0 0 k
    ∃ (f : Fin k) (hf : f.val ≤ m),
      typedFree out.2 = some f ∧
      ∀ j, directCandidate out.1 f hf j = typedCandidate out.1 out.2 f j := by
  let out := echelonMaterialized A 0 0 k
  let s := GaussControlTrace.after A k
  let fval := prefixCount (natPivots s.pivots)
  have hs := GaussControlTrace.after_k A
  have hB : s.B = out.1 := hs.1
  have hps : s.pivots = out.2 := hs.2
  have hfacts := prefixFacts A hdependent
  obtain ⟨hlt, hselected⟩ := selectedFree A hdependent
  let f : Fin k := ⟨fval, hlt⟩
  have hf : f.val ≤ m := hfacts.1
  have htyped : typedFree out.2 = some f := by
    change typedFree s.pivots = some f at hselected
    simpa [hps] using hselected
  have hfree : f ∉ out.2.map Prod.snd := typedFree_spec out.2 f htyped
  have hbelow : BelowZero A 0 0 := by
    intro i j _ hj
    omega
  have hunit : ∀ p ∈ out.2, ∀ i : Fin m,
      out.1 i p.2 = if i = p.1 then 1 else 0 := by
    simpa [out, echelonMaterialized_eq] using
      (echelonTyped_pivot_units A 0 0 k (by simp) hbelow)
  have hnodup : (out.2.map Prod.fst).Nodup := by
    simpa [out, echelonMaterialized_eq] using
      (echelonTyped_pivot_rows_nodup A 0 0 k)
  have hcol : Function.Injective (fun p : PivotIndex out.2 => p.val.2) :=
    CurrentAdditive.RationalBitBounds.pivot_columns_injective
      out.1 out.2 hunit hnodup
  have hleft : ∀ j : Fin k, j.val < f.val →
      ∃ i : Fin m, i.val = j.val ∧ (i,j) ∈ out.2 := by
    intro j hj
    have hj' : j.val < fval := hj
    have hdiag : (j.val,j.val) ∈ natPivots s.pivots :=
      hfacts.2.2.2 j.val hj'
    obtain ⟨p, hp, hval⟩ := List.mem_map.mp hdiag
    rcases p with ⟨i,c⟩
    have hi : i.val = j.val := congrArg Prod.fst hval
    have hc : c = j := Fin.ext (congrArg Prod.snd hval)
    subst c
    exact ⟨i, hi, by simpa [hps] using hp⟩
  have hzero : ∀ p ∈ out.2, f.val < p.2.val → out.1 p.1 f = 0 := by
    intro p hp hltp
    exact materialized_pivot_left_zero A p hp f hltp
  change ∃ (f : Fin k) (hf : f.val ≤ m),
    typedFree out.2 = some f ∧
    ∀ j, directCandidate out.1 f hf j = typedCandidate out.1 out.2 f j
  exact ⟨f, hf, htyped,
    fun j => directCandidate_eq out.1 out.2 f hf hfree hcol hleft hzero j⟩

#print axioms prefixFacts

#print axioms selectedFree
#print axioms directCandidate_on_materialized

end CurrentAdditive.GaussDependentPrefix
