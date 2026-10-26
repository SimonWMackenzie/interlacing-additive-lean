import EthInapproximability.CurrentPaper.SourceOriginalCNFPacketizerBanks

/-! Physically sequenced capture, cited sparsification, and canonical branch packetization. -/

namespace EthInapproximability.CurrentPaper.SourceOriginalCNFPacketizer

open Turing BitMachineEncoding BitMachineStackEmbedding

variable {η : ℚ} (S : EncodedETHSource.Sparsification η)

abbrev Label := BitMachineRawSequence.Label
  (SourceLabel S) SourceOriginalListPacketizer.Label
abbrev Control := BitMachineRawSequence.Control
  (SourceControl S) SourceOriginalListPacketizer.Control
abbrev Config := TM2.Cfg (fun _ : Stack S => Bool) (Label S) (Control S)

noncomputable def entry (input : List Bool) : Config S :=
  ⟨some (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel SourceOriginalVariableCapture.Label.scan)),
    ((none,S.machine.initial),SourceOriginalListPacketizer.initialControl),
    bank (sourceSlots S) (emptyBank S)
      (SourceOriginalSparsificationMachine.startBank S input)⟩

noncomputable def outputStack : Stack S :=
  packetSlots S (.inr 9)

noncomputable def run (t : ℕ) (c : Config S) : Config S :=
  ((advance (program S))^[t]) c

noncomputable def totalTime (f : EncodedETHSource.ValidFormula) : ℕ :=
  SourceOriginalSparsificationMachine.totalTime S f +
    SourceOriginalListPacketizer.canonicalTime f.val.variables
      ((S.branches f).map fun g => EncodedCNF.encode g.val) + 1

theorem outputStack_fresh : outputStack S = .inr (.inr 9) := by
  exact packetSlots_other S (.inr 9) (by decide) (by decide)

theorem canonical_run (f : EncodedETHSource.ValidFormula) :
    ∃ t ≤ totalTime S f,
      (run S t (entry S (EncodedCNF.encode f.val))).l = none ∧
      (run S t (entry S (EncodedCNF.encode f.val))).stk (outputStack S) =
        SourceOriginalBranchPackets.packetList S f := by
  let input := EncodedCNF.encode f.val
  let T := SourceOriginalSparsificationMachine.sparseTime S input
  let c := (S.machine).run T ((S.machine).init input)
  obtain ⟨a, ha, hsource⟩ :=
    SourceOriginalSparsificationMachine.canonical_run S f
  have hsource' : ((advance (SourceOriginalSparsificationMachine.program S))^[a])
      (SourceOriginalSparsificationMachine.entry S input) =
      ⟨none,(none,c.var),
        SourceOriginalSparsificationMachine.finalBank S input f.val.variables T⟩ := by
    simpa only [input, T, c] using hsource
  have hA := BitMachineStackRun.run (sourceSlots S) (emptyBank S)
    (SourceOriginalSparsificationMachine.program S)
    (SourceOriginalSparsificationMachine.entry S input) a
  rw [hsource'] at hA
  have hA' : ((advance (sourceOn S))^[a])
      (⟨some (BitMachineRawSequence.leftLabel
          SourceOriginalVariableCapture.Label.scan),
        (none,S.machine.initial),
        bank (sourceSlots S) (emptyBank S)
          (SourceOriginalSparsificationMachine.startBank S input)⟩ :
          TM2.Cfg (fun _ : Stack S => Bool) (SourceLabel S) (SourceControl S)) =
      ⟨none,(none,c.var),sourceFinalBank S f⟩ := by
    simpa only [sourceOn, SourceOriginalSparsificationMachine.entry,
      BitMachineStackEmbedding.stackCfg, sourceFinalBank, input, T] using hA
  obtain ⟨b, hb, hhalt, hout⟩ :=
    SourceOriginalListPacketizer.source_canonical_run S f
  let p0 := SourceOriginalListPacketizer.startCfg f.val.variables
    (EncodedETHSource.formulaListBits (S.branches f))
  let p1 := SourceOriginalListPacketizer.run b p0
  have hB := BitMachineStackRun.run (packetSlots S) (sourceFinalBank S f)
    SourceOriginalListPacketizer.program p0 b
  have hB' : ((advance (packetOn S))^[b])
      (⟨some (SourceOriginalListPacketizer.adminLabel .startInit),
        SourceOriginalListPacketizer.initialControl,sourceFinalBank S f⟩ :
        TM2.Cfg (fun _ : Stack S => Bool)
          SourceOriginalListPacketizer.Label SourceOriginalListPacketizer.Control) =
      ⟨none,p1.var,bank (packetSlots S) (sourceFinalBank S f) p1.stk⟩ := by
    change ((advance (packetOn S))^[b])
      (stackCfg (packetSlots S) (sourceFinalBank S f) p0) =
      stackCfg (packetSlots S) (sourceFinalBank S f) p1 at hB
    simpa only [BitMachineStackEmbedding.stackCfg,
      SourceOriginalCNFPacketizer.packetStart_eq_sourceFinal S f,
      p0, p1, hhalt] using hB
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (sourceOn S) (packetOn S)
    (BitMachineRawSequence.leftLabel SourceOriginalVariableCapture.Label.scan)
    (SourceOriginalListPacketizer.adminLabel .startInit)
    (none,S.machine.initial) (none,c.var)
    SourceOriginalListPacketizer.initialControl p1.var
    (bank (sourceSlots S) (emptyBank S)
      (SourceOriginalSparsificationMachine.startBank S input))
    (sourceFinalBank S f)
    (bank (packetSlots S) (sourceFinalBank S f) p1.stk)
    a b hA' hB'
  refine ⟨t, by dsimp [totalTime]; omega, ?_, ?_⟩
  · change (((advance (program S))^[t]) (entry S input)).l = none
    simpa only [program, entry, run, input] using congrArg TM2.Cfg.l hr
  · have hfinal : (bank (packetSlots S) (sourceFinalBank S f) p1.stk)
        (outputStack S) = SourceOriginalBranchPackets.packetList S f := by
      rw [outputStack, bank_at]
      exact hout
    change (((advance (program S))^[t]) (entry S input)).stk
      (outputStack S) = _
    rw [show ((advance (program S))^[t]) (entry S input) =
      ⟨none,((none,S.machine.initial),p1.var),
        bank (packetSlots S) (sourceFinalBank S f) p1.stk⟩ from by
      simpa only [program, entry, input] using hr]
    exact hfinal

noncomputable def envelopeTime (f : EncodedETHSource.ValidFormula) : ℕ :=
  (5*(S.branches f).length.bits.length+7) +
  (S.branches f).length *
    SourceOriginalListPacketizer.itemEnvelope f.val.variables
      (S.branches f).length.bits.length
      (SourceOriginalListPacketizer.branchLimit S f) +
  ((4*(S.branches f).length.bits.length+5)+1+1+
    (3*(S.branches f).length*
      (2*(f.val.variables+SourceOriginalListPacketizer.branchLimit S f)+3)+2)+1)

theorem totalTime_le_envelope (f : EncodedETHSource.ValidFormula)
    (hn : 1 ≤ f.val.variables) :
    totalTime S f ≤
      SourceOriginalSparsificationMachine.totalTime S f +
        envelopeTime S f + 1 := by
  have h := SourceOriginalListPacketizer.source_time_le_count S f hn
  unfold totalTime envelopeTime
  omega

end EthInapproximability.CurrentPaper.SourceOriginalCNFPacketizer
