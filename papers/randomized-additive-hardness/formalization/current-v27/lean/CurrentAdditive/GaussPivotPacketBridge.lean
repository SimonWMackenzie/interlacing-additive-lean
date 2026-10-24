import CurrentAdditive.GaussPivotPrefixPhysical
import CurrentAdditive.GaussFirstFreeArithmetic
import CurrentAdditive.GaussTraceInvariants

/-! Byte-for-byte connection between the Gauss trace's Bank4 state and the
physical pivot-prefix scanner. -/

namespace CurrentAdditive.GaussPivotPacketBridge

open EthInapproximability.CurrentPaper

def natPivots {m k : Nat} (ps : List (Fin m × Fin k)) :
    List (Nat × Nat) := ps.map fun p => (p.1.val, p.2.val)

theorem pivotPacket_eq {m k : Nat} (p : Fin m × Fin k) :
    GaussControlTrace.pivotPacket p =
      GaussPivotPairEq.pairPacket p.1.val p.2.val := by
  unfold GaussControlTrace.pivotPacket GaussPivotPairEq.pairPacket
  congr 1
  funext j
  fin_cases j <;> simp

theorem pivotsPacket_eq {m k : Nat} (ps : List (Fin m × Fin k)) :
    GaussControlTrace.pivotsPacket ps =
      GaussPivotPrefixPhysical.pivotListPacket (natPivots ps) := by
  unfold GaussControlTrace.pivotsPacket
    GaussPivotPrefixPhysical.pivotListPacket natPivots
  congr 1
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      simp only [List.map_cons]
      rw [pivotPacket_eq]
      exact congrArg (List.cons _) ih

theorem statePacket_eq {m k : Nat} (s : GaussControlTrace.State m k) :
    GaussControlTrace.statePacket s =
      GaussPivotPrefixPhysical.stateWord
        (GaussPhysical.encodeTypedMatrix s.B) s.r s.c
        (natPivots s.pivots) := by
  unfold GaussControlTrace.statePacket
    GaussPivotPrefixPhysical.stateWord
  congr 1
  funext j
  fin_cases j <;>
    simp [GaussControlTrace.stateBank,
      GaussPivotPrefixPhysical.stateBank, pivotsPacket_eq]

theorem outputs_gauss_state {m k : Nat}
    (s : GaussControlTrace.State m k) :
    GaussPivotPrefixPhysical.machine.OutputsWithin
      (GaussControlTrace.statePacket s)
      (List.replicate
        (GaussPivotPrefixPhysical.prefixCount (natPivots s.pivots)) true)
      (12 * ((GaussControlTrace.statePacket s).length + 1) +
        2 * (GaussPivotPrefixPhysical.pivotListPacket
          (natPivots s.pivots)).length + 2 +
        SourceListMachineOuter.canonicalBound GaussPivotPairEq.machine
          (GaussPivotPrefixPhysical.pivotWords (natPivots s.pivots))
          GaussPivotPairEq.result GaussPivotPrefixPhysical.pairClock +
        2 * (EthInapproximability.CurrentPaper.EncodedCommunication.natField
          (natPivots s.pivots).length ++
          GaussPivotPrefixPhysical.pivotFlags (natPivots s.pivots)).length +
        2 +
        (2 * (EthInapproximability.CurrentPaper.EncodedCommunication.natField
          (natPivots s.pivots).length ++
          GaussPivotPrefixPhysical.pivotFlags (natPivots s.pivots)).length + 3) +
        2 * (GaussPivotPrefixPhysical.pivotFlags
          (natPivots s.pivots)).length + 2 +
        ((GaussPivotPrefixPhysical.pivotFlags
          (natPivots s.pivots)).length + 1)) := by
  rw [statePacket_eq]
  exact GaussPivotPrefixPhysical.outputs_state
    (GaussPhysical.encodeTypedMatrix s.B) s.r s.c
    (natPivots s.pivots)

theorem after_prefix_is_firstFree {m k : Nat}
    (A : Fin m → Fin k → ℚ) (hkm : m < k) :
    let ps := natPivots (GaussControlTrace.after A k).pivots
    (List.range k).find? (fun c => decide (c ∉ ps.map Prod.snd)) =
      some (GaussPivotPrefixPhysical.prefixCount ps) := by
  let s := GaussControlTrace.after A k
  let ps := natPivots s.pivots
  have hcount := GaussControlTrace.after_pivotCount A k
  have hrowle := GaussControlTrace.after_row_le A k
  have hrows := GaussTraceInvariants.after_rows A k
  have hinc := GaussTraceInvariants.after_columns_pairwise A k
  have hlen : ps.length < k := by
    have hcount' : s.r = s.pivots.length := hcount
    have hrowle' : s.r ≤ m := hrowle
    simp only [ps, natPivots, List.length_map]
    omega
  have hrows' : ps.map Prod.fst = List.range ps.length := by
    simpa [ps, natPivots, hcount] using hrows
  have hinc' : (ps.map Prod.snd).Pairwise (· < ·) := by
    simpa [ps, natPivots] using hinc
  have hflags := GaussFirstFreeArithmetic.flags_eq_diagonalFrom 0 ps (by
    simpa [List.range'_eq_map_range] using hrows')
  have hfirst := GaussFirstFreeArithmetic.firstFree_eq_prefix k
    (ps.map Prod.snd) hinc' (by simpa only [List.length_map] using hlen)
  unfold GaussFirstFreeArithmetic.diagonalPrefix at hfirst
  rw [← hflags] at hfirst
  change (List.range k).find? (fun c => decide (c ∉ ps.map Prod.snd)) =
    some ((GaussPivotPrefixPhysical.pivotFlags ps).takeWhile id).length
  exact hfirst

#print axioms outputs_gauss_state
#print axioms after_prefix_is_firstFree

end CurrentAdditive.GaussPivotPacketBridge
