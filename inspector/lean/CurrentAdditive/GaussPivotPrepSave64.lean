import CurrentAdditive.GaussPivotPrepHigh64
import EthInapproximability.CurrentPaper.SourceClausePreservingBroadcast
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-! Physical high-bank backups of the row, column, raw state, and row count
before the pivot search consumes its low-bank threshold. -/

namespace CurrentAdditive.GaussPivotPrepSave64

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

abbrev Bank := Fin 64

def pR := SourceClausePreservingBroadcast.program (30 : Bank) 63 [53]
def pC := SourceClausePreservingBroadcast.program (12 : Bank) 63 [55]
def pP := SourceClausePreservingBroadcast.program (31 : Bank) 63 [56]
def pM := SourceClausePreservingBroadcast.program (13 : Bank) 63 [58]

noncomputable def afterR {m k : Nat}
    (s : GaussControlTrace.State m k) : Bank → List Bool :=
  SourceClausePreservingBroadcast.result 30 63 [53] (List.replicate s.r true)
    (GaussPivotPrepHigh64.prepared s)

noncomputable def afterC {m k : Nat}
    (s : GaussControlTrace.State m k) : Bank → List Bool :=
  SourceClausePreservingBroadcast.result 12 63 [55] (List.replicate s.c true) (afterR s)

noncomputable def afterP {m k : Nat}
    (s : GaussControlTrace.State m k) : Bank → List Bool :=
  SourceClausePreservingBroadcast.result 31 63 [56] (GaussControlTrace.statePacket s) (afterC s)

noncomputable def saved {m k : Nat}
    (s : GaussControlTrace.State m k) : Bank → List Bool :=
  SourceClausePreservingBroadcast.result 13 63 [58] (List.replicate m true) (afterP s)

private theorem r_other {m k : Nat}
    (s : GaussControlTrace.State m k) (j : Bank)
    (hj : j ≠ 30 ∧ j ≠ 63 ∧ j ≠ 53) :
    afterR s j = GaussPivotPrepHigh64.prepared s j :=
  SourceClausePreservingBroadcast.other_preserved 30 63 [53] _ _ j hj.1 hj.2.1
    (by simpa using hj.2.2)

private theorem c_other {m k : Nat}
    (s : GaussControlTrace.State m k) (j : Bank)
    (hj : j ≠ 12 ∧ j ≠ 63 ∧ j ≠ 55) :
    afterC s j = afterR s j :=
  SourceClausePreservingBroadcast.other_preserved 12 63 [55] _ _ j hj.1 hj.2.1
    (by simpa using hj.2.2)

private theorem p_other {m k : Nat}
    (s : GaussControlTrace.State m k) (j : Bank)
    (hj : j ≠ 31 ∧ j ≠ 63 ∧ j ≠ 56) :
    afterP s j = afterC s j :=
  SourceClausePreservingBroadcast.other_preserved 31 63 [56] _ _ j hj.1 hj.2.1
    (by simpa using hj.2.2)

private theorem m_other {m k : Nat}
    (s : GaussControlTrace.State m k) (j : Bank)
    (hj : j ≠ 13 ∧ j ≠ 63 ∧ j ≠ 58) :
    saved s j = afterP s j :=
  SourceClausePreservingBroadcast.other_preserved 13 63 [58] _ _ j hj.1 hj.2.1
    (by simpa using hj.2.2)

theorem afterR_row {m k : Nat}
    (s : GaussControlTrace.State m k) :
    afterR s 30 = List.replicate s.r true := by
  exact SourceClausePreservingBroadcast.source_restored 30 63 [53] (by decide)
    (List.replicate s.r true) _

theorem afterR_backup {m k : Nat}
    (s : GaussControlTrace.State m k) :
    afterR s 53 = List.replicate s.r true := by
  rw [afterR, SourceClausePreservingBroadcast.target_written 30 63 [53]
    (by decide) (by decide) (by decide)
    (List.replicate s.r true) _ 53 (by simp)]
  simp [GaussPivotPrepHigh64.prepared_high s 53 (by decide)]

theorem afterC_column {m k : Nat}
    (s : GaussControlTrace.State m k) :
    afterC s 12 = List.replicate s.c true := by
  exact SourceClausePreservingBroadcast.source_restored 12 63 [55] (by decide)
    (List.replicate s.c true) _

theorem afterC_backup {m k : Nat}
    (s : GaussControlTrace.State m k) :
    afterC s 55 = List.replicate s.c true := by
  rw [afterC, SourceClausePreservingBroadcast.target_written 12 63 [55]
    (by decide) (by decide) (by decide)
    (List.replicate s.c true) _ 55 (by simp)]
  rw [r_other s 55 (by decide)]
  simp [GaussPivotPrepHigh64.prepared_high s 55 (by decide)]

theorem afterP_packet {m k : Nat}
    (s : GaussControlTrace.State m k) :
    afterP s 31 = GaussControlTrace.statePacket s := by
  exact SourceClausePreservingBroadcast.source_restored 31 63 [56] (by decide)
    (GaussControlTrace.statePacket s) _

theorem afterP_backup {m k : Nat}
    (s : GaussControlTrace.State m k) :
    afterP s 56 = GaussControlTrace.statePacket s := by
  rw [afterP, SourceClausePreservingBroadcast.target_written 31 63 [56]
    (by decide) (by decide) (by decide)
    (GaussControlTrace.statePacket s) _ 56 (by simp)]
  rw [c_other s 56 (by decide), r_other s 56 (by decide)]
  simp [GaussPivotPrepHigh64.prepared_high s 56 (by decide)]

theorem saved_count {m k : Nat}
    (s : GaussControlTrace.State m k) :
    saved s 13 = List.replicate m true := by
  exact SourceClausePreservingBroadcast.source_restored 13 63 [58] (by decide)
    (List.replicate m true) _

theorem saved_backup_count {m k : Nat}
    (s : GaussControlTrace.State m k) :
    saved s 58 = List.replicate m true := by
  rw [saved, SourceClausePreservingBroadcast.target_written 13 63 [58]
    (by decide) (by decide) (by decide)
    (List.replicate m true) _ 58 (by simp)]
  rw [p_other s 58 (by decide), c_other s 58 (by decide),
    r_other s 58 (by decide)]
  simp [GaussPivotPrepHigh64.prepared_high s 58 (by decide)]

theorem saved_row {m k : Nat}
    (s : GaussControlTrace.State m k) :
    saved s 53 = List.replicate s.r true := by
  rw [m_other s 53 (by decide), p_other s 53 (by decide),
    c_other s 53 (by decide)]
  exact afterR_backup s

theorem saved_column {m k : Nat}
    (s : GaussControlTrace.State m k) :
    saved s 55 = List.replicate s.c true := by
  rw [m_other s 55 (by decide), p_other s 55 (by decide)]
  exact afterC_backup s

theorem saved_packet {m k : Nat}
    (s : GaussControlTrace.State m k) :
    saved s 56 = GaussControlTrace.statePacket s := by
  rw [m_other s 56 (by decide)]
  exact afterP_backup s

private theorem copy_preserves_low (source target : Bank)
    (bits : List Bool) (S : Bank → List Bool)
    (hsource : source ≠ 63)
    (htarget : 32 ≤ target.val)
    (hbits : S source = bits) (i : Fin 32) :
    SourceClausePreservingBroadcast.result source 63 [target] bits S
      (GaussPivotPrepHigh64.low i) =
      S (GaussPivotPrepHigh64.low i) := by
  let j := GaussPivotPrepHigh64.low i
  have hhigh (x : Bank) (hx : 32 ≤ x.val) : j ≠ x := by
    intro he
    have hv : i.val = x.val := by
      simpa [j, GaussPivotPrepHigh64.low] using
        congrArg (fun z : Bank => z.val) he
    omega
  by_cases hs : j = source
  · change SourceClausePreservingBroadcast.result source 63 [target]
        bits S j = S j
    rw [hs, SourceClausePreservingBroadcast.source_restored
      source 63 [target] hsource bits S]
    exact hbits.symm
  · exact SourceClausePreservingBroadcast.other_preserved
      source 63 [target] bits S j hs (hhigh 63 (by decide))
      (by simp [hhigh target htarget])

theorem saved_low {m k : Nat}
    (s : GaussControlTrace.State m k) (i : Fin 32) :
    saved s (GaussPivotPrepHigh64.low i) =
      GaussPivotPrepBank.prepared s i := by
  have hC : afterR s 12 = List.replicate s.c true :=
    (r_other s 12 (by decide)).trans
      (GaussPivotPrepHigh64.prepared_column s)
  have hP : afterC s 31 = GaussControlTrace.statePacket s :=
    (c_other s 31 (by decide)).trans
      ((r_other s 31 (by decide)).trans
        (GaussPivotPrepHigh64.prepared_original s))
  have hM : afterP s 13 = List.replicate m true :=
    (p_other s 13 (by decide)).trans
      ((c_other s 13 (by decide)).trans
        ((r_other s 13 (by decide)).trans
          (GaussPivotPrepHigh64.prepared_count s)))
  change SourceClausePreservingBroadcast.result 13 63 [58]
      (List.replicate m true) (afterP s)
      (GaussPivotPrepHigh64.low i) = _
  rw [copy_preserves_low 13 58 _ _ (by decide) (by decide) hM i]
  change SourceClausePreservingBroadcast.result 31 63 [56]
      (GaussControlTrace.statePacket s) (afterC s)
      (GaussPivotPrepHigh64.low i) = _
  rw [copy_preserves_low 31 56 _ _ (by decide) (by decide) hP i]
  change SourceClausePreservingBroadcast.result 12 63 [55]
      (List.replicate s.c true) (afterR s)
      (GaussPivotPrepHigh64.low i) = _
  rw [copy_preserves_low 12 55 _ _ (by decide) (by decide) hC i]
  change SourceClausePreservingBroadcast.result 30 63 [53]
      (List.replicate s.r true) (GaussPivotPrepHigh64.prepared s)
      (GaussPivotPrepHigh64.low i) = _
  rw [copy_preserves_low 30 53 _ _ (by decide) (by decide)
    (GaussPivotPrepHigh64.prepared_row s) i]
  exact GaussPivotPrepHigh64.prepared_low s i

theorem r_run {m k : Nat}
    (s : GaussControlTrace.State m k) :
    ((advance pR)^[2 * s.r + 3])
      (⟨some .scan, ((),none), GaussPivotPrepHigh64.prepared s⟩ :
        TM2.Cfg (fun _ : Bank => Bool) _ _) =
      ⟨none, ((),none), afterR s⟩ := by
  simpa only [pR, afterR, List.length_replicate] using
    SourceClausePreservingBroadcast.run_halt
      (30 : Bank) 63 [53] (by decide) (by decide)
      (by decide) (by decide) (List.replicate s.r true)
      (GaussPivotPrepHigh64.prepared s)
      (GaussPivotPrepHigh64.prepared_row s)
      (GaussPivotPrepHigh64.prepared_high s 63 (by decide))

theorem c_run {m k : Nat}
    (s : GaussControlTrace.State m k) :
    ((advance pC)^[2 * s.c + 3])
      (⟨some .scan, ((),none), afterR s⟩ :
        TM2.Cfg (fun _ : Bank => Bool) _ _) =
      ⟨none, ((),none), afterC s⟩ := by
  have hc : afterR s 12 = List.replicate s.c true :=
    (r_other s 12 (by decide)).trans
      (GaussPivotPrepHigh64.prepared_column s)
  have htemp : afterR s 63 = [] :=
    SourceClausePreservingBroadcast.temp_empty 30 63 [53]
      (List.replicate s.r true) _
  simpa only [pC, afterC, List.length_replicate] using
    SourceClausePreservingBroadcast.run_halt
      (12 : Bank) 63 [55] (by decide) (by decide)
      (by decide) (by decide) (List.replicate s.c true)
      (afterR s) hc htemp

theorem p_run {m k : Nat}
    (s : GaussControlTrace.State m k) :
    ((advance pP)^[2 * (GaussControlTrace.statePacket s).length + 3])
      (⟨some .scan, ((),none), afterC s⟩ :
        TM2.Cfg (fun _ : Bank => Bool) _ _) =
      ⟨none, ((),none), afterP s⟩ := by
  have hp : afterC s 31 = GaussControlTrace.statePacket s :=
    (c_other s 31 (by decide)).trans
      ((r_other s 31 (by decide)).trans
        (GaussPivotPrepHigh64.prepared_original s))
  have htemp : afterC s 63 = [] :=
    SourceClausePreservingBroadcast.temp_empty 12 63 [55]
      (List.replicate s.c true) _
  simpa only [pP, afterP] using
    SourceClausePreservingBroadcast.run_halt
      (31 : Bank) 63 [56] (by decide) (by decide)
      (by decide) (by decide) (GaussControlTrace.statePacket s)
      (afterC s) hp htemp

theorem m_run {m k : Nat}
    (s : GaussControlTrace.State m k) :
    ((advance pM)^[2 * m + 3])
      (⟨some .scan, ((),none), afterP s⟩ :
        TM2.Cfg (fun _ : Bank => Bool) _ _) =
      ⟨none, ((),none), saved s⟩ := by
  have hm : afterP s 13 = List.replicate m true :=
    (p_other s 13 (by decide)).trans
      ((c_other s 13 (by decide)).trans
        ((r_other s 13 (by decide)).trans
          (GaussPivotPrepHigh64.prepared_count s)))
  have htemp : afterP s 63 = [] :=
    SourceClausePreservingBroadcast.temp_empty 31 63 [56]
      (GaussControlTrace.statePacket s) _
  simpa only [pM, saved, List.length_replicate] using
    SourceClausePreservingBroadcast.run_halt
      (13 : Bank) 63 [58] (by decide) (by decide)
      (by decide) (by decide) (List.replicate m true)
      (afterP s) hm htemp

def pRC := BitMachineRawSequence.program pR pC
  .scan ((),none) ((),none)

theorem rc_run {m k : Nat}
    (s : GaussControlTrace.State m k) :
    ∃ t ≤ (2 * s.r + 3) + (2 * s.c + 3) + 1,
      ((advance pRC)^[t])
        (⟨some (BitMachineRawSequence.leftLabel .scan),
          (((),none),((),none)), GaussPivotPrepHigh64.prepared s⟩ :
          TM2.Cfg (fun _ : Bank => Bool) _ _) =
        ⟨none, (((),none),((),none)), afterC s⟩ := by
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    pR pC .scan .scan ((),none) ((),none) ((),none) ((),none)
    (GaussPivotPrepHigh64.prepared s) (afterR s) (afterC s)
    (2*s.r+3) (2*s.c+3) (r_run s) (c_run s)
  exact ⟨t, ht, by simpa only [pRC] using hr⟩

def pRCP := BitMachineRawSequence.program pRC pP
  .scan (((),none),((),none)) ((),none)

theorem rcp_run {m k : Nat}
    (s : GaussControlTrace.State m k) :
    ∃ t ≤ ((2 * s.r + 3) + (2 * s.c + 3) + 1) +
      (2 * (GaussControlTrace.statePacket s).length + 3) + 1,
      ((advance pRCP)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel .scan)),
          ((((),none),((),none)),((),none)),
          GaussPivotPrepHigh64.prepared s⟩ :
          TM2.Cfg (fun _ : Bank => Bool) _ _) =
        ⟨none, ((((),none),((),none)),((),none)), afterP s⟩ := by
  obtain ⟨u, hu, hr⟩ := rc_run s
  obtain ⟨t, ht, he⟩ := BitMachineRawSequence.runs
    pRC pP (BitMachineRawSequence.leftLabel .scan) .scan
    (((),none),((),none)) (((),none),((),none))
    ((),none) ((),none)
    (GaussPivotPrepHigh64.prepared s) (afterC s) (afterP s)
    u (2*(GaussControlTrace.statePacket s).length+3)
    (by simpa only [pRC] using hr) (p_run s)
  exact ⟨t, by omega, by simpa only [pRCP] using he⟩

def copyProgram := BitMachineRawSequence.program pRCP pM
  .scan ((((),none),((),none)),((),none)) ((),none)

theorem copy_run {m k : Nat}
    (s : GaussControlTrace.State m k) :
    ∃ t ≤ 2 * s.r + 2 * s.c +
      2 * (GaussControlTrace.statePacket s).length + 2 * m + 15,
      ((advance copyProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel .scan))),
          (((((),none),((),none)),((),none)),((),none)),
          GaussPivotPrepHigh64.prepared s⟩ :
          TM2.Cfg (fun _ : Bank => Bool) _ _) =
        ⟨none, (((((),none),((),none)),((),none)),((),none)),
          saved s⟩ := by
  obtain ⟨u, hu, hr⟩ := rcp_run s
  obtain ⟨t, ht, he⟩ := BitMachineRawSequence.runs
    pRCP pM
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel .scan)) .scan
    ((((),none),((),none)),((),none))
    ((((),none),((),none)),((),none))
    ((),none) ((),none)
    (GaussPivotPrepHigh64.prepared s) (afterP s) (saved s)
    u (2*m+3) (by simpa only [pRCP] using hr) (m_run s)
  exact ⟨t, by omega, by simpa only [copyProgram] using he⟩

def program := BitMachineRawSequence.program
  GaussPivotPrepHigh64.program copyProgram
  (BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel .scan)))
  (.copy ((),none))
  (((((),none),((),none)),((),none)),((),none))

theorem physical_prep_save {m k : Nat}
    (s : GaussControlTrace.State m k) :
    ∃ t ≤ GaussPivotPrepRun.clock s + 1 +
      (2 * s.r + 2 * s.c +
        2 * (GaussControlTrace.statePacket s).length + 2 * m + 15) + 1,
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel (.copy .scan)),
          (.copy ((),none),
            (((((),none),((),none)),((),none)),((),none))),
          (GaussPivotPrepHigh64.start s).stk⟩ :
          TM2.Cfg (fun _ : Bank => Bool) _ _) =
        ⟨none, (.copy ((),none),
          (((((),none),((),none)),((),none)),((),none))), saved s⟩ := by
  obtain ⟨a, ha, hp⟩ := GaussPivotPrepHigh64.physical_prep s
  obtain ⟨b, hb, hc⟩ := copy_run s
  obtain ⟨t, ht, he⟩ := BitMachineRawSequence.runs
    GaussPivotPrepHigh64.program copyProgram
    (.copy .scan)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel .scan)))
    (.copy ((),none)) (.fields ((),none))
    (((((),none),((),none)),((),none)),((),none))
    (((((),none),((),none)),((),none)),((),none))
    (GaussPivotPrepHigh64.start s).stk
    (GaussPivotPrepHigh64.prepared s) (saved s)
    a b (by simpa only [GaussPivotPrepHigh64.start] using hp)
    (by simpa only [copyProgram] using hc)
  exact ⟨t, by omega, by simpa only [program] using he⟩

#print axioms r_run
#print axioms c_run
#print axioms p_run
#print axioms m_run
#print axioms physical_prep_save

end
end CurrentAdditive.GaussPivotPrepSave64
