import CurrentAdditive.GaussStepPivotHeaderRun32

/-! The fixed controller installs the completed V2 pivot-list packet. -/

namespace CurrentAdditive.GaussStepPivotJoinRun32

noncomputable section

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open Turing BitMachineEncoding
open CurrentAdditive.GaussStepFields32

private theorem done_step (c : GaussPivotJoin32.Config)
    (h : c.l = some .done) :
    GaussPivotJoin32.run 1 c = ⟨none,c.var,c.stk⟩ := by
  cases c with
  | mk l v S =>
    cases l with
    | none => cases h
    | some l =>
      cases l <;> try cases h
      rfl

theorem join_phase {m k : Nat}
    (ps : List (Fin m × Fin k)) (S : Stack → List Bool)
    (h30 : S 30 = natField ps.length)
    (h27 : S 27 = SourceListEncoding.fields
      (ps.map GaussControlTrace.pivotPacket))
    (h24 : S 24 = []) (h31 : S 31 = []) :
    ∃ t ≤ (S 7).length+1 + (2*(natField ps.length).length+3) +
        (4*(natField ps.length).length+2*
          (SourceListEncoding.fields
            (ps.map GaussControlTrace.pivotPacket)).length+7)+1,
      (run t ⟨some (.join .clear7),eJoin ((),none),S⟩).l =
        some .afterJoin ∧
      (run t ⟨some (.join .clear7),eJoin ((),none),S⟩).stk 7 =
        GaussControlTrace.pivotsPacket ps ∧
      ∀ j : Fin 3,
        (run t ⟨some (.join .clear7),eJoin ((),none),S⟩).stk
          (⟨j.val+4,by omega⟩ : Stack) =
          S (⟨j.val+4,by omega⟩ : Stack) := by
  let c0 : GaussPivotJoin32.Config := ⟨some .clear7,((),none),S⟩
  obtain ⟨a,ha,hl,hout,hpres⟩ :=
    GaussPivotJoin32.physical_join_pivots ps S h30 h27 h24 h31
  have hlocal : GaussPivotJoin32.run (a+1) c0 =
      ⟨none,(GaussPivotJoin32.run a c0).var,
        (GaussPivotJoin32.run a c0).stk⟩ := by
    rw [GaussPivotJoin32.run_add (show
      GaussPivotJoin32.run a c0 = GaussPivotJoin32.run a c0
      from rfl) 1]
    exact done_step _ hl
  obtain ⟨u,hu,hglobal⟩ :=
    GaussStepPhaseLift32.join_lift c0 (a+1) (by rw [hlocal])
  have he : run u ⟨some (.join .clear7),eJoin ((),none),S⟩ =
      ⟨some .afterJoin,eJoin (GaussPivotJoin32.run a c0).var,
        (GaussPivotJoin32.run a c0).stk⟩ := by
    simpa [BitMachineInline.cfg,hlocal,c0] using hglobal
  refine ⟨u, by omega, ?_, ?_, ?_⟩
  · rw [he]
  · rw [he]
    exact hout
  · intro j
    rw [he]
    exact hpres j

#print axioms join_phase

end
end CurrentAdditive.GaussStepPivotJoinRun32
