import CurrentAdditive.GaussPivotHeaderJoinClock32
import CurrentAdditive.GaussStepPivotAppendExactRun32
import CurrentAdditive.GaussStepWriterResetRun32

/-! Physically append one correctly framed pivot pair to the old V2 body,
reset the header worker, and finish the exact Bank4 successor packet. -/

namespace CurrentAdditive.GaussPivotAppendClock32

noncomputable section

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open CurrentAdditive.GaussStepFields32

def appendPhaseBound (body payload : List Bool) : Nat :=
  (2*body.length+3)+(4*body.length+2*payload.length+7)+1

def prefixBound (body payload : List Bool) (charge : Nat) : Nat :=
  let A := appendPhaseBound body payload
  A + 1 + 8 * (charge + GaussPivotClockGrowth32.pushConstant * A)
    + 10 + 1

def clock {m k : Nat} (B' : Fin m → Fin k → ℚ) (c : Nat)
    (ps : List (Fin m × Fin k)) (p : Fin m × Fin k)
    (charge : Nat) : Nat :=
  let body := SourceListEncoding.fields
    (ps.map GaussControlTrace.pivotPacket)
  let payload := natField (GaussControlTrace.pivotPacket p).length ++
    GaussControlTrace.pivotPacket p
  prefixBound body payload charge +
    GaussPivotHeaderJoinClock32.uniformClock B' c (ps ++ [p])
      (charge + GaussPivotClockGrowth32.pushConstant *
        prefixBound body payload charge)

private theorem fields_append_one (xs : List (List Bool)) (p : List Bool) :
    SourceListEncoding.fields (xs ++ [p]) =
      SourceListEncoding.fields xs ++ natField p.length ++ p := by
  induction xs with
  | nil => simp [SourceListEncoding.fields]
  | cons x xs ih =>
      simp only [List.cons_append, SourceListEncoding.fields]
      rw [ih]
      simp [List.append_assoc]

private theorem append_preserves (body payload : List Bool)
    (S : Stack → List Bool)
    (j : Stack) (hj : j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 30) :
    (GaussStepPivotAppendExactRun32.result body payload S).stk j = S j := by
  apply GaussStepPivotAppendExactRun32.result_preserves body payload S j
  · rcases hj with rfl | rfl | rfl | rfl <;> decide
  · rcases hj with rfl | rfl | rfl | rfl <;> decide
  · rcases hj with rfl | rfl | rfl | rfl <;> decide
  · rcases hj with rfl | rfl | rfl | rfl <;> decide

theorem append_to_packet_bound {m k : Nat}
    (B' : Fin m → Fin k → ℚ) (c : Nat)
    (ps : List (Fin m × Fin k)) (p : Fin m × Fin k)
    (S : Stack → List Bool)
    (h4 : S 4 = GaussPhysical.encodeTypedMatrix B')
    (h5 : S 5 = List.replicate (ps ++ [p]).length true)
    (h6 : S 6 = List.replicate c true)
    (h23 : S 23 = SourceListEncoding.fields
      (ps.map GaussControlTrace.pivotPacket))
    (h26 : S 26 = natField (GaussControlTrace.pivotPacket p).length ++
      GaussControlTrace.pivotPacket p)
    (h27 : S 27 = []) (h24 : S 24 = [])
    (h30 : S 30 = []) (h31 : S 31 = [])
    (charge : Nat) (hcharge : ∀ j : Stack, (S j).length ≤ charge) :
    ∃ t ≤ clock B' c ps p charge,
      (run t ⟨some (.append (.copyBodyDirect .scan)),
        eAppend ((),none),S⟩).l = some .done ∧
      (run t ⟨some (.append (.copyBodyDirect .scan)),
        eAppend ((),none),S⟩).stk 14 =
        GaussControlTrace.statePacket
          (⟨B',(ps ++ [p]).length,c,ps ++ [p]⟩ :
            GaussControlTrace.State m k) := by
  let body := SourceListEncoding.fields
    (ps.map GaussControlTrace.pivotPacket)
  let payload := natField (GaussControlTrace.pivotPacket p).length ++
    GaussControlTrace.pivotPacket p
  let start : Config := ⟨some (.append (.copyBodyDirect .scan)),
    eAppend ((),none),S⟩
  obtain ⟨a,ha,happend⟩ :=
    GaussStepPivotAppendExactRun32.append_exact body payload S
      h23 h26 h27 h24 h31
  let C := GaussStepPivotAppendExactRun32.result body payload S
  have hrunA : run a start = C := happend
  have hnextA : run 1 C =
      ⟨some (.resetWriter (.inl 0)),eResetWriter ((),none),C.stk⟩ := by
    change run 1 (GaussStepPivotAppendExactRun32.result body payload S) = _
    rfl
  obtain ⟨b,hb,hreset⟩ := GaussStepWriterResetRun32.reset_phase C.stk
  have ha' : a ≤ appendPhaseBound body payload := by
    simpa [appendPhaseBound] using ha
  have hresetClock : GaussWorkerReset32.clock C.stk + 1 ≤
      8 * (charge + GaussPivotClockGrowth32.pushConstant *
        appendPhaseBound body payload) + 10 := by
    have hg := GaussPivotClockGrowth32.reset_writer_clock_le
      start a charge (by simpa [start] using hcharge)
    rw [hrunA] at hg
    have hm := Nat.mul_le_mul_left
      GaussPivotClockGrowth32.pushConstant ha'
    omega
  have hprefix : a+1+b+1 ≤ prefixBound body payload charge := by
    dsimp [prefixBound]
    omega
  let R := GaussStepWriterResetRun32.cleared C.stk
  have hrunR : run b
      ⟨some (.resetWriter (.inl 0)),eResetWriter ((),none),C.stk⟩ =
      ⟨some .afterResetWriter,eResetWriter ((),none),R⟩ := hreset
  have hnextR : run 1
      ⟨some .afterResetWriter,eResetWriter ((),none),R⟩ =
      ⟨some (.header (.copyIn .scan)),
        eHeader (((),none),
          (SourceListMachineWriter.framingMachine false).initial),R⟩ := by
    rfl
  have hprefixRun : run (a+1+b+1) start =
      ⟨some (.header (.copyIn .scan)),
        eHeader (((),none),
          (SourceListMachineWriter.framingMachine false).initial),R⟩ := by
    rw [show a+1+b+1 = a+(1+(b+1)) by omega,
      run_add hrunA (1+(b+1)),run_add hnextA (b+1),
      run_add hrunR 1]
    exact hnextR
  have hchargeR : ∀ j : Stack,
      (R j).length ≤ charge + GaussPivotClockGrowth32.pushConstant *
        prefixBound body payload charge := by
    intro j
    have hg := GaussPivotClockGrowth32.bank_growth_from_charge
      start (a+1+b+1) charge (by simpa [start] using hcharge) j
    rw [hprefixRun] at hg
    have hm := Nat.mul_le_mul_left
      GaussPivotClockGrowth32.pushConstant hprefix
    exact hg.trans (Nat.add_le_add_left hm charge)
  have h4R : R 4 = GaussPhysical.encodeTypedMatrix B' := by
    unfold R
    rw [GaussStepWriterResetRun32.preserves C.stk 4 (Or.inl (by decide)),
      append_preserves body payload S 4 (Or.inl rfl),h4]
  have h5R : R 5 = List.replicate (ps ++ [p]).length true := by
    unfold R
    rw [GaussStepWriterResetRun32.preserves C.stk 5 (Or.inl (by decide)),
      append_preserves body payload S 5 (Or.inr (Or.inl rfl)),h5]
  have h6R : R 6 = List.replicate c true := by
    unfold R
    rw [GaussStepWriterResetRun32.preserves C.stk 6 (Or.inl (by decide)),
      append_preserves body payload S 6 (Or.inr (Or.inr (Or.inl rfl))),h6]
  have h27R : R 27 = SourceListEncoding.fields
      ((ps ++ [p]).map GaussControlTrace.pivotPacket) := by
    unfold R
    rw [GaussStepWriterResetRun32.preserves C.stk 27 (Or.inr (by decide)),
      GaussStepPivotAppendExactRun32.result27]
    simp [body,payload,List.map_append,fields_append_one,List.append_assoc]
  have h24R : R 24 = [] := by
    unfold R
    rw [GaussStepWriterResetRun32.preserves C.stk 24 (Or.inr (by decide))]
    exact GaussStepPivotAppendExactRun32.result24 body payload S h24
  have h30R : R 30 = [] := by
    unfold R
    rw [GaussStepWriterResetRun32.preserves C.stk 30 (Or.inr (by decide)),
      append_preserves body payload S 30 (Or.inr (Or.inr (Or.inr rfl))),h30]
  have h31R : R 31 = [] := by
    unfold R
    rw [GaussStepWriterResetRun32.preserves C.stk 31 (Or.inr (by decide))]
    exact GaussStepPivotAppendExactRun32.result31 body payload S
  have hempty : ∀ j : Fin
      (SourceListMachineWriter.framingMachine false).stackCount,
      R (GaussPivotFraming32.locate j) = [] := by
    intro j
    exact GaussStepWriterResetRun32.worker_empty C.stk j
  obtain ⟨d,hd,hdone,hpacket⟩ :=
    GaussPivotHeaderJoinClock32.header_join_finish_uniform B' c
      (ps ++ [p]) R h4R h5R h6R h27R h24R h30R h31R hempty
      (charge + GaussPivotClockGrowth32.pushConstant *
        prefixBound body payload charge) hchargeR
  refine ⟨a+1+b+1+d, ?_, ?_, ?_⟩
  · change a+1+b+1+d ≤ prefixBound body payload charge +
      GaussPivotHeaderJoinClock32.uniformClock B' c (ps ++ [p])
        (charge + GaussPivotClockGrowth32.pushConstant *
          prefixBound body payload charge)
    omega
  · rw [show a+1+b+1+d = a+(1+(b+(1+d))) by omega,
      run_add hrunA (1+(b+(1+d))),run_add hnextA (b+(1+d)),
      run_add hrunR (1+d),run_add hnextR d]
    exact hdone
  · rw [show a+1+b+1+d = a+(1+(b+(1+d))) by omega,
      run_add hrunA (1+(b+(1+d))),run_add hnextA (b+(1+d)),
      run_add hrunR (1+d),run_add hnextR d]
    exact hpacket

#print axioms append_to_packet_bound

end
end CurrentAdditive.GaussPivotAppendClock32
