import CurrentAdditive.GaussPivotPacketBridge

/-! Full-support polynomial clock for the physical first-free selector on the
actual zero-one Gauss state after all `k` columns. -/

namespace CurrentAdditive.GaussPivotPrefixClock

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open CurrentAdditive.GaussPivotPrefixPhysical
open CurrentAdditive.GaussPivotPacketBridge

def pairCap (m k : Nat) : Nat := 2 * (m + k) + 2

noncomputable def itemEnvelope (m k : Nat) : Nat :=
  let L := pairCap m k
  let T := 7 * (L + 1) + 3
  let M := GaussPivotPairEq.machine
  20 * (L + 1) * (L + 1) + T + 4 * L + 1 +
    M.stackCount * (L + T * M.pushBound + 1) + 9

noncomputable def outerEnvelope (m k : Nat) : Nat :=
  m * (itemEnvelope m k + 4 * m + 8) + 11 * m + 17

theorem pivotWord_length {m k : Nat} (p : Fin m × Fin k) :
    (GaussPivotPairEq.pairPacket p.1.val p.2.val).length ≤ pairCap m k := by
  have h := GaussControlTrace.pivotPacket_length p
  rw [GaussPivotPacketBridge.pivotPacket_eq] at h
  have hm := p.1.isLt
  have hk := p.2.isLt
  simp [pairCap, h]
  omega

theorem item_bound {m k : Nat} (p : Fin m × Fin k) :
    SourceListMachineWork.itemCost GaussPivotPairEq.machine
      (GaussPivotPairEq.pairPacket p.1.val p.2.val)
      (GaussPivotPairEq.result
        (GaussPivotPairEq.pairPacket p.1.val p.2.val))
      (pairClock (GaussPivotPairEq.pairPacket p.1.val p.2.val)) ≤
      itemEnvelope m k := by
  let x := GaussPivotPairEq.pairPacket p.1.val p.2.val
  let L := pairCap m k
  let T := 7 * (L + 1) + 3
  have hx : x.length ≤ L := pivotWord_length p
  have hb : x.length.bits.length ≤ L :=
    (UnaryBinaryEncoding.bits_length_le x.length).trans hx
  have ht : pairClock x ≤ T := by unfold pairClock T; omega
  have hout : (GaussPivotPairEq.result x).length = 1 := by
    simp [x, GaussPivotPairEq.result_pairPacket]
  unfold SourceListMachineWork.itemCost itemEnvelope
  dsimp only
  rw [hout]
  dsimp only [L, T] at hx hb ht
  gcongr

theorem outer_bound {m k : Nat}
    (ps : List (Fin m × Fin k)) (hcount : ps.length ≤ m) :
    SourceListMachineOuter.canonicalBound GaussPivotPairEq.machine
      (pivotWords (natPivots ps)) GaussPivotPairEq.result pairClock ≤
      outerEnvelope m k := by
  apply SourceListMachineOuter.canonicalBound_le_source
    GaussPivotPairEq.machine (pivotWords (natPivots ps))
    GaussPivotPairEq.result pairClock 0
    (fun _ => m) (fun _ => m) (fun _ => itemEnvelope m k)
    (fun _ => 1)
  · simpa [pivotWords, natPivots] using hcount
  · have hb := UnaryBinaryEncoding.bits_length_le
      (pivotWords (natPivots ps)).length
    have hc : (pivotWords (natPivots ps)).length ≤ m := by
      simpa [pivotWords, natPivots] using hcount
    exact hb.trans hc
  · intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    simpa [natPivots] using item_bound p
  · intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    rcases q with ⟨r,c⟩
    simp [GaussPivotPairEq.result_pairPacket]

def stateCap (m k : Nat) : Nat :=
  2 * (3 * m * (3 * k *
    (4 * ((m + 3) * (m + 1) ^ 2 + 1) + 6) + 2) + 1 +
    2 * k + (3 * k * (2 * (m + k) + 3) + 1)) + 4

noncomputable def prefixClock (m k : Nat) : Nat :=
  12 * (stateCap m k + 1) + 2 * stateCap m k + 2 +
    outerEnvelope m k +
    2 * (3 * m + 1) + 2 + (2 * (3 * m + 1) + 3) +
    2 * m + 2 + (m + 1)

theorem physical_firstFree {m k : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hkm : m < k) :
    let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
    let s := GaussControlTrace.after Aq k
    let ps := natPivots s.pivots
    ∃ f,
      (List.range k).find? (fun c => decide (c ∉ ps.map Prod.snd)) = some f ∧
      GaussPivotPrefixPhysical.machine.OutputsWithin
        (GaussControlTrace.statePacket s) (List.replicate f true)
        (prefixClock m k) := by
  let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
  let s := GaussControlTrace.after Aq k
  let ps := natPivots s.pivots
  let n := (GaussControlTrace.statePacket s).length
  have hstate : n ≤ stateCap m k := by
    simpa [n, s, Aq, stateCap] using
      GaussControlTrace.actual_statePacket_length A h01 k (by omega)
  have hcount : s.pivots.length ≤ m := by
    have h₁ := GaussControlTrace.after_pivotCount Aq k
    have h₂ := GaussControlTrace.after_row_le Aq k
    change s.r = s.pivots.length at h₁
    change s.r ≤ m at h₂
    omega
  have hps : ps.length ≤ m := by simpa [ps, natPivots] using hcount
  have hflags : (pivotFlags ps).length ≤ m := by
    simpa [pivotFlags] using hps
  have hfield : (natField ps.length).length ≤ 2*m+1 := by
    have h := EncodedGraph.natField_length_upper ps.length
    omega
  have hheader : (natField ps.length ++ pivotFlags ps).length ≤ 3*m+1 := by
    simp only [List.length_append]
    omega
  have hpacket : (pivotListPacket ps).length ≤ n := by
    have h := BitMachineBankCodec.word_length_le_encode
      (stateBank (GaussPhysical.encodeTypedMatrix s.B) s.r s.c ps)
      (3 : Fin 4)
    simpa [stateBank, stateWord, statePacket_eq, n] using h
  have houter : SourceListMachineOuter.canonicalBound
      GaussPivotPairEq.machine (pivotWords ps) GaussPivotPairEq.result
      pairClock ≤ outerEnvelope m k := by
    simpa [ps] using outer_bound s.pivots hcount
  dsimp only [ps] at hflags hfield hheader hpacket houter
  have hrun := outputs_gauss_state s
  have hfirst := after_prefix_is_firstFree Aq hkm
  refine ⟨prefixCount ps, ?_, ?_⟩
  · simpa [s, ps] using hfirst
  · obtain ⟨t, ht, hhalt, hout⟩ := hrun
    refine ⟨t, ?_, hhalt, hout⟩
    unfold prefixClock
    omega

#print axioms physical_firstFree

end CurrentAdditive.GaussPivotPrefixClock
