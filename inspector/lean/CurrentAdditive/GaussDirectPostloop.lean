import CurrentAdditive.GaussFirstFreeCandidate
import CurrentAdditive.GaussPivotLeftZero
import CurrentAdditive.GaussPivotPrefixRows
import CurrentAdditive.GaussTraceInvariants
import CurrentAdditive.Endpoint

/-! A postloop formula requiring no pivot-column lookup.  The first free
column is obtained from the physical prefix selector. For columns before it,
the pivot row equals the column number; later pivot rows are zero in that
free column. -/

namespace CurrentAdditive.GaussDirectPostloop

open CurrentAdditive.SequentialTotality
open CurrentAdditive.MaterializedGauss
open CurrentAdditive.GaussPivotPrefixPhysical
open CurrentAdditive.GaussFirstFreeArithmetic
open CurrentAdditive.GaussFirstFreeCandidate
open CurrentAdditive.RationalBitBounds

def natPivots {m k : Nat} (ps : List (Fin m × Fin k)) :
    List (Nat × Nat) := ps.map fun p => (p.1.val, p.2.val)

theorem prefixFacts {m k : Nat} (A : Fin m → Fin k → ℚ)
    (hkm : m < k) :
    let s := GaussControlTrace.after A k
    let nps := natPivots s.pivots
    let f := prefixCount nps
    f ≤ m ∧ f < k ∧
      (List.range k).find? (fun c => decide (c ∉ nps.map Prod.snd)) = some f ∧
      (∀ j < f, (j,j) ∈ nps) := by
  let s := GaussControlTrace.after A k
  let nps := natPivots s.pivots
  let f := prefixCount nps
  have hcount := GaussControlTrace.after_pivotCount A k
  have hrowle := GaussControlTrace.after_row_le A k
  have hrows := GaussTraceInvariants.after_rows A k
  have hinc := GaussTraceInvariants.after_columns_pairwise A k
  have hlen : nps.length < k := by
    have hc : s.r = s.pivots.length := hcount
    have hm : s.r ≤ m := hrowle
    simp only [nps, natPivots, List.length_map]
    omega
  have hrows' : nps.map Prod.fst = List.range nps.length := by
    simpa [nps, natPivots, hcount] using hrows
  have hrows'' : nps.map Prod.fst = List.range' 0 nps.length := by
    simpa [List.range'_eq_map_range] using hrows'
  have hinc' : (nps.map Prod.snd).Pairwise (· < ·) := by
    simpa [nps, natPivots] using hinc
  have hflags := flags_eq_diagonalFrom 0 nps hrows''
  have hfirst := firstFree_eq_prefix k (nps.map Prod.snd) hinc'
    (by simpa only [List.length_map] using hlen)
  unfold diagonalPrefix at hfirst
  rw [← hflags] at hfirst
  have hf : (List.range k).find? (fun c => decide (c ∉ nps.map Prod.snd)) =
      some f := hfirst
  have hf_le : f ≤ nps.length := by
    unfold f prefixCount
    exact (List.takeWhile_sublist id).length_le.trans_eq
      (by simp [pivotFlags, nps, natPivots])
  have hfm : f ≤ m := by
    have hc : s.r = s.pivots.length := hcount
    have hm : s.r ≤ m := hrowle
    have hl : f ≤ s.pivots.length := by simpa [nps, natPivots] using hf_le
    omega
  have hdiag : ∀ j < f, (j,j) ∈ nps := by
    intro j hj
    exact GaussPivotPrefixRows.diagonal_pairs_in_prefix 0 nps hrows''
      j (by omega) (by omega)
  change f ≤ m ∧ f < k ∧
    (List.range k).find? (fun c => decide (c ∉ nps.map Prod.snd)) = some f ∧
    (∀ j < f, (j,j) ∈ nps)
  exact ⟨hfm, by omega, hf, hdiag⟩

theorem materialized_pivot_left_zero {m k : Nat}
    (A : Fin m → Fin k → ℚ) :
    let out := echelonMaterialized A 0 0 k
    ∀ p ∈ out.2, ∀ j : Fin k, j.val < p.2.val → out.1 p.1 j = 0 := by
  simpa [echelonMaterialized_eq] using
    (GaussPivotLeftZero.full_pivot_left_zero A)

theorem selectedFree {m k : Nat} (A : Fin m → Fin k → ℚ)
    (hkm : m < k) :
    let s := GaussControlTrace.after A k
    let fval := prefixCount (natPivots s.pivots)
    ∃ hlt : fval < k,
      typedFree s.pivots = some ⟨fval, hlt⟩ := by
  let s := GaussControlTrace.after A k
  let fval := prefixCount (natPivots s.pivots)
  have hfacts := prefixFacts A hkm
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
    (A : Fin m → Fin k → ℚ) (hkm : m < k) :
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
  have hfacts := prefixFacts A hkm
  obtain ⟨hlt, hselected⟩ := selectedFree A hkm
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
#print axioms materialized_pivot_left_zero
#print axioms selectedFree
#print axioms directCandidate_on_materialized

end CurrentAdditive.GaussDirectPostloop
