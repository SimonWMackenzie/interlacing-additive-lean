import CurrentAdditive.GaussStepPivotJoinRun32
import CurrentAdditive.GaussStepFinish32

/-! Close the physical pivot-list join into the exact Bank4 state packet.
The input fields are the results produced by the earlier fixed pivot stages. -/

namespace CurrentAdditive.GaussPivotJoinFinish32

noncomputable section

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open CurrentAdditive.GaussStepFields32

theorem pivot_join_finish {m k : Nat}
    (B' : Fin m → Fin k → ℚ)
    (r c : Nat) (ps : List (Fin m × Fin k))
    (S : Stack → List Bool)
    (h4 : S 4 = GaussPhysical.encodeTypedMatrix B')
    (h5 : S 5 = List.replicate r true)
    (h6 : S 6 = List.replicate c true)
    (h30 : S 30 = natField ps.length)
    (h27 : S 27 = SourceListEncoding.fields
      (ps.map GaussControlTrace.pivotPacket))
    (h24 : S 24 = []) (h31 : S 31 = []) :
    ∃ t,
      (run t ⟨some (.join .clear7), eJoin ((),none), S⟩).l = some .done ∧
      (run t ⟨some (.join .clear7), eJoin ((),none), S⟩).stk 14 =
        GaussControlTrace.statePacket
          (⟨B',r,c,ps⟩ : GaussControlTrace.State m k) := by
  let s' : GaussControlTrace.State m k := ⟨B',r,c,ps⟩
  let start : Config := ⟨some (.join .clear7), eJoin ((),none), S⟩
  obtain ⟨a,ha,hl,h7,hpres⟩ :=
    GaussStepPivotJoinRun32.join_phase ps S h30 h27 h24 h31
  let C := run a start
  have hC : C.l = some .afterJoin := hl
  have hbank : GaussBranchFields32.preparedBank C.stk =
      GaussControlTrace.stateBank s' := by
    funext p
    fin_cases p
    · simpa [GaussBranchFields32.preparedBank,
        GaussBranchFields32.dest,s',GaussControlTrace.stateBank]
        using (hpres (0 : Fin 3)).trans h4
    · simpa [GaussBranchFields32.preparedBank,
        GaussBranchFields32.dest,s',GaussControlTrace.stateBank]
        using (hpres (1 : Fin 3)).trans h5
    · simpa [GaussBranchFields32.preparedBank,
        GaussBranchFields32.dest,s',GaussControlTrace.stateBank]
        using (hpres (2 : Fin 3)).trans h6
    · simpa [GaussBranchFields32.preparedBank,
        GaussBranchFields32.dest,s',GaussControlTrace.stateBank]
        using h7
  obtain ⟨b,hb,hend,hpacket⟩ :=
    GaussStepFinish32.finish_state s' C.stk C.var hbank
  have hfull : run (a+b) start =
      run b ⟨some .afterJoin,C.var,C.stk⟩ := by
    rw [run_add (show run a start = C from rfl) b]
    have heq : C = ⟨some .afterJoin,C.var,C.stk⟩ := by
      cases hcfg : C with
      | mk l var stk =>
          have hl' : l = some .afterJoin := by simpa only [hcfg] using hC
          cases hl'
          rfl
    rw [heq]
  exact ⟨a+b, by rw [hfull]; exact hend,
    by rw [hfull]; exact hpacket⟩

#print axioms pivot_join_finish

end
end CurrentAdditive.GaussPivotJoinFinish32
