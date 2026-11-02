import EthInapproximability.CurrentPaper.SourceValidDispatch

namespace EthInapproximability.CurrentPaper.SourceValidAcceptance

open Turing BitMachineEncoding BitMachineInline
open scoped Classical

theorem combined_positive {a q : Nat}
    (P : EncodedETHSource.ConstraintInstance a q)
    (hn : 0 < P.vertices) :
    ∃ t v S,
      t ≤ SourceCSPGuardDispatchSequence.bound a q
        (EncodedETHSource.constraintBits P).length ∧
      ((advance (SourceCSPGuardOutputCombined.program a q))^[t])
        (SourceCSPGuardOutputCombined.initial a q
          (EncodedETHSource.constraintBits P)) =
        (⟨some .route, (v, none), S⟩ :
          TM2.Cfg (fun _ : SourceCSPInputFrame.Stack => Bool)
            (SourceCSPGuardOutputCombined.Label a q)
            SourceCSPGuardOutputCombined.Control) ∧
      v.2.2 = some .positive := by
  obtain ⟨tp, Sp, vp, htp, hrp, hvp⟩ := dispatch_positive P hn
  let localCfg : TM2.Cfg (fun _ : SourceCSPInputFrame.Stack => Bool)
      (SourceCSPGuardOutputCombined.PrefixLabel a q)
      SourceCSPGuardOutputCombined.PrefixControl :=
    ⟨some (.inl (SourceCSPGuardDispatchSequence.headerStart a q)),
      (SourceCSPGuardDispatchSequence.headerInitial,
        SourceCSPGuardDispatch.initialControl),
      SourceCSPInputFrame.initial (EncodedETHSource.constraintBits P)⟩
  have hhalt : (((advance (SourceCSPGuardDispatchSequence.program a q))^[tp])
      localCfg).l = none := by
    simpa only [localCfg] using congrArg (fun c => c.l) hrp
  obtain ⟨t, ht, hr⟩ := BitMachineInline.outputs
    SourceCSPGuardOutputCombined.Label.prefix
    (fun v => (v, none)) Prod.fst (fun _ => rfl) (some .route)
    (SourceCSPGuardDispatchSequence.program a q)
    (SourceCSPGuardOutputCombined.program a q)
    (fun _ => rfl) localCfg tp hhalt
  rw [hrp] at hr
  refine ⟨t,
    (SourceCSPGuardDispatchSequence.headerInitial, vp),
    Sp, ht.trans htp, ?_, hvp⟩
  simpa only [SourceCSPGuardOutputCombined.initial,
    SourceCSPGuardOutputCombined.initialControl, localCfg,
    BitMachineInline.cfg, Option.map_none] using hr

#print axioms combined_positive

end EthInapproximability.CurrentPaper.SourceValidAcceptance
