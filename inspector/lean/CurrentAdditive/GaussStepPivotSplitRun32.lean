import CurrentAdditive.GaussStepInactivePacket32

/-! The fixed controller's first pivot-list stage physically strips the V2 header. -/

namespace CurrentAdditive.GaussStepPivotSplitRun32

noncomputable section

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open Turing BitMachineEncoding
open CurrentAdditive.GaussStepFields32

def result {m k : Nat} (ps : List (Fin m × Fin k))
    (S : Stack → List Bool) (v : ProtocolBinaryHeader.Control) : Config :=
  let c := GaussPivotBodySplit32.parserFrame
    (GaussPivotBodySplit32.copied
      (GaussControlTrace.pivotsPacket ps) S)
    (ProtocolBinaryHeader.cfg none v
      (GaussPivotBodySplit32.body ps) [] (true::ps.length.bits))
  ⟨some .afterSplit,eSplit c.var,c.stk⟩

theorem split_phase {m k : Nat}
    (ps : List (Fin m × Fin k)) (S : Stack → List Bool)
    (h19 : S 19 = GaussControlTrace.pivotsPacket ps)
    (h23 : S 23 = []) (h24 : S 24 = []) (h25 : S 25 = [])
    (h31 : S 31 = []) :
    ∃ t ≤ 2*(GaussControlTrace.pivotsPacket ps).length+3+
        (3*ps.length.bits.length+2)+1,
      ∃ v : ProtocolBinaryHeader.Control,
        run t ⟨some (.split (.copy .scan)),
          eSplit (((),none),(none,none)),S⟩ = result ps S v := by
  obtain ⟨a,ha,v,hlocal⟩ :=
    GaussPivotBodySplit32.physical_split ps S h19 h23 h24 h25 h31
  let target := GaussPivotBodySplit32.parserFrame
    (GaussPivotBodySplit32.copied
      (GaussControlTrace.pivotsPacket ps) S)
    (ProtocolBinaryHeader.cfg none v
      (GaussPivotBodySplit32.body ps) [] (true::ps.length.bits))
  have hhalt : GaussPivotBodySplit32.run (a+1)
      ⟨some (.copy .scan),(((),none),(none,none)),S⟩ =
      ⟨none,target.var,target.stk⟩ := by
    change ((advance GaussPivotBodySplit32.program)^[a+1]) _ = _
    rw [Function.iterate_succ_apply',
      ← GaussPivotBodySplit32.run,hlocal]
    rfl
  obtain ⟨u,hu,hglobal⟩ :=
    GaussStepPhaseLift32.split_lift
      (⟨some (.copy .scan),(((),none),(none,none)),S⟩)
      (a+1) (by rw [hhalt])
  have he : run u ⟨some (.split (.copy .scan)),
      eSplit (((),none),(none,none)),S⟩ =
      ⟨some .afterSplit,eSplit target.var,target.stk⟩ := by
    simpa [BitMachineInline.cfg,hhalt] using hglobal
  exact ⟨u, by omega, v, by simpa [result,target] using he⟩

theorem result_body {m k : Nat}
    (ps : List (Fin m × Fin k))
    (S : Stack → List Bool) (v : ProtocolBinaryHeader.Control) :
    (result ps S v).stk 23 =
      SourceListEncoding.fields (ps.map GaussControlTrace.pivotPacket) := by
  simpa [result,GaussPivotBodySplit32.body] using
    GaussPivotBodySplit32.split_body_at_23 ps
      (GaussPivotBodySplit32.copied
        (GaussControlTrace.pivotsPacket ps) S) v

theorem result_preserves {m k : Nat}
    (ps : List (Fin m × Fin k))
    (S : Stack → List Bool) (v : ProtocolBinaryHeader.Control)
    (j : Stack) (h19 : j ≠ 19) (h23 : j ≠ 23)
    (h24 : j ≠ 24) (h25 : j ≠ 25) (h31 : j ≠ 31) :
    (result ps S v).stk j = S j := by
  change (BitMachineStackEmbedding.bank
    GaussPivotBodySplit32.parserSlot
    (GaussPivotBodySplit32.copied
      (GaussControlTrace.pivotsPacket ps) S)
    (ProtocolBinaryHeader.cfg none v
      (GaussPivotBodySplit32.body ps) []
        (true::ps.length.bits)).stk) j = S j
  rw [BitMachineStackEmbedding.bank_outside
    GaussPivotBodySplit32.parserSlot _ _ j (by
      rintro ⟨q,hq⟩
      fin_cases q <;> simp [GaussPivotBodySplit32.parserSlot] at hq <;>
        simp_all)]
  change SourceClausePreservingBroadcast.result 19 31 [23]
    (GaussControlTrace.pivotsPacket ps) S j = S j
  exact SourceClausePreservingBroadcast.other_preserved
    (19 : Stack) 31 [23] (GaussControlTrace.pivotsPacket ps)
    S j h19 h31 (by simpa using h23)

theorem result24_empty {m k : Nat}
    (ps : List (Fin m × Fin k))
    (S : Stack → List Bool) (v : ProtocolBinaryHeader.Control) :
    (result ps S v).stk 24 = [] := by
  change (BitMachineStackEmbedding.bank
    GaussPivotBodySplit32.parserSlot
    (GaussPivotBodySplit32.copied
      (GaussControlTrace.pivotsPacket ps) S)
    (ProtocolBinaryHeader.cfg none v
      (GaussPivotBodySplit32.body ps) []
        (true::ps.length.bits)).stk)
      (GaussPivotBodySplit32.parserSlot (1:Fin 3)) = []
  rw [BitMachineStackEmbedding.bank_at]
  rfl

theorem result31_empty {m k : Nat}
    (ps : List (Fin m × Fin k))
    (S : Stack → List Bool) (v : ProtocolBinaryHeader.Control) :
    (result ps S v).stk 31 = [] := by
  change (BitMachineStackEmbedding.bank
    GaussPivotBodySplit32.parserSlot
    (GaussPivotBodySplit32.copied
      (GaussControlTrace.pivotsPacket ps) S)
    (ProtocolBinaryHeader.cfg none v
      (GaussPivotBodySplit32.body ps) []
        (true::ps.length.bits)).stk) 31 = []
  rw [BitMachineStackEmbedding.bank_outside
    GaussPivotBodySplit32.parserSlot _ _ 31 (by
      rintro ⟨q,hq⟩
      fin_cases q <;> simp [GaussPivotBodySplit32.parserSlot] at hq)]
  exact SourceClausePreservingBroadcast.temp_empty
    (19 : Stack) 31 [23] (GaussControlTrace.pivotsPacket ps) S

#print axioms split_phase
#print axioms result_body
#print axioms result_preserves
#print axioms result24_empty
#print axioms result31_empty

end
end CurrentAdditive.GaussStepPivotSplitRun32
