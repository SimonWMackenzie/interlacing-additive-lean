import Paper2.A4T10Front
import EthInapproximability.CurrentPaper.SourceOriginalPacketWriter
import EthInapproximability.CurrentPaper.BitMachineRawSequence

namespace Paper2.Unit4Shell.PairMapGlue

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

abbrev Stack := Fin 5

def captureSlots : SourceOriginalVariableCapture.Stack ↪ Stack where
  toFun := ![1, 2, 0]
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all

def captureProgram (l : SourceOriginalVariableCapture.Label) :
    TM2.Stmt (fun _ : Stack => Bool) SourceOriginalVariableCapture.Label
      SourceOriginalVariableCapture.Control :=
  BitMachineStackEmbedding.stmt captureSlots id id id none
    (SourceOriginalVariableCapture.program l)

def captureInput (word : List Bool) : Stack → List Bool :=
  ![[], word, [], [], []]

def writerInput (n : ℕ) (word : List Bool) : Stack → List Bool :=
  ![List.replicate n true, word, [], [], []]

theorem capture_initial (word : List Bool) :
    BitMachineStackEmbedding.cfg captureSlots (fun _ => []) id id none
      (SourceOriginalVariableCapture.cfg (some .scan) none word [] []) =
    ⟨some SourceOriginalVariableCapture.Label.scan, none, captureInput word⟩ := by
  unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg captureInput SourceOriginalVariableCapture.cfg
  congr 1
  funext k
  fin_cases k
  · simpa [captureSlots] using
      (BitMachineStackEmbedding.bank_at captureSlots (fun _ => [])
        (![word, [], []] : Fin 3 → List Bool) (2 : Fin 3))
  · simpa [captureSlots] using
      (BitMachineStackEmbedding.bank_at captureSlots (fun _ => [])
        (![word, [], []] : Fin 3 → List Bool) (0 : Fin 3))
  · simpa [captureSlots] using
      (BitMachineStackEmbedding.bank_at captureSlots (fun _ => [])
        (![word, [], []] : Fin 3 → List Bool) (1 : Fin 3))
  · rw [BitMachineStackEmbedding.bank_outside]
    · rfl
    · rintro ⟨j,hj⟩; fin_cases j <;> simp [captureSlots] at hj
  · rw [BitMachineStackEmbedding.bank_outside]
    · rfl
    · rintro ⟨j,hj⟩; fin_cases j <;> simp [captureSlots] at hj

theorem capture_final (f : EncodedCNF.Formula) :
    BitMachineStackEmbedding.cfg captureSlots (fun _ => []) id id none
      (SourceOriginalVariableCapture.cfg none none (EncodedCNF.encode f) []
        (List.replicate f.variables true)) =
    ⟨none, none, writerInput f.variables (EncodedCNF.encode f)⟩ := by
  unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg writerInput SourceOriginalVariableCapture.cfg
  congr 1
  funext k
  fin_cases k
  · simpa [captureSlots] using
      (BitMachineStackEmbedding.bank_at captureSlots (fun _ => [])
        (![EncodedCNF.encode f, [], List.replicate f.variables true] : Fin 3 → List Bool)
        (2 : Fin 3))
  · simpa [captureSlots] using
      (BitMachineStackEmbedding.bank_at captureSlots (fun _ => [])
        (![EncodedCNF.encode f, [], List.replicate f.variables true] : Fin 3 → List Bool)
        (0 : Fin 3))
  · simpa [captureSlots] using
      (BitMachineStackEmbedding.bank_at captureSlots (fun _ => [])
        (![EncodedCNF.encode f, [], List.replicate f.variables true] : Fin 3 → List Bool)
        (1 : Fin 3))
  · rw [BitMachineStackEmbedding.bank_outside]
    · rfl
    · rintro ⟨j,hj⟩; fin_cases j <;> simp [captureSlots] at hj
  · rw [BitMachineStackEmbedding.bank_outside]
    · rfl
    · rintro ⟨j,hj⟩; fin_cases j <;> simp [captureSlots] at hj

theorem capture_run (f : EncodedCNF.Formula) :
    ∃ t ≤ 2*f.variables+3,
      ((advance captureProgram)^[t])
        (⟨some SourceOriginalVariableCapture.Label.scan, none,
          captureInput (EncodedCNF.encode f)⟩ :
          TM2.Cfg (fun _ : Stack => Bool) SourceOriginalVariableCapture.Label
            SourceOriginalVariableCapture.Control) =
        ⟨none, none, writerInput f.variables (EncodedCNF.encode f)⟩ := by
  have hr := SourceOriginalVariableCapture.canonical_raw_run f
  have hi : rawInit (0 : SourceOriginalVariableCapture.Stack)
      SourceOriginalVariableCapture.Label.scan none (EncodedCNF.encode f) =
      SourceOriginalVariableCapture.cfg (some .scan) none (EncodedCNF.encode f) [] [] := by
    unfold rawInit SourceOriginalVariableCapture.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  rw [hi] at hr
  have hh : (SourceOriginalVariableCapture.run (2*f.variables+3)
      (SourceOriginalVariableCapture.cfg (some .scan) none (EncodedCNF.encode f) [] [])).l = none :=
    by rw [hr]; rfl
  obtain ⟨t,ht,he⟩ := BitMachineStackEmbedding.outputs captureSlots (fun _ => [])
    id id id (by intro v; rfl) none SourceOriginalVariableCapture.program
    captureProgram (by intro l; rfl)
    (SourceOriginalVariableCapture.cfg (some .scan) none (EncodedCNF.encode f) [] [])
    (2*f.variables+3) (by simpa only [SourceOriginalVariableCapture.run] using hh)
  refine ⟨t,ht,?_⟩
  rw [← capture_initial, he]
  simp only [SourceOriginalVariableCapture.run] at hr
  rw [hr, capture_final]

def program : BitMachineRawSequence.Label SourceOriginalVariableCapture.Label
    SourceOriginalPacketWriter.Label →
    TM2.Stmt (fun _ : Stack => Bool)
      (BitMachineRawSequence.Label SourceOriginalVariableCapture.Label
        SourceOriginalPacketWriter.Label)
      (SourceOriginalVariableCapture.Control × SourceOriginalPacketWriter.Control) :=
  BitMachineRawSequence.program captureProgram SourceOriginalPacketWriter.program
    .scanN none none

noncomputable def packetizer : BitMachine.Machine :=
  ofFinite (1 : Stack) (4 : Stack)
    (BitMachineRawSequence.leftLabel SourceOriginalVariableCapture.Label.scan)
    (none, none) program

theorem packetizer_run (f : EncodedCNF.Formula) :
    ∃ t ≤ 6*f.variables + 3*(EncodedCNF.encode f).length + 10,
      ((advance program)^[t])
        (rawInit (1 : Stack)
          (BitMachineRawSequence.leftLabel SourceOriginalVariableCapture.Label.scan)
          (none, none) (EncodedCNF.encode f)) =
        ⟨none, (none, none),
          ![List.replicate f.variables true, [], [], [],
            SourceOriginalBranchPackets.packet f.variables (EncodedCNF.encode f)]⟩ := by
  obtain ⟨a,ha,hcapture⟩ := capture_run f
  let w := EncodedCNF.encode f
  have hwriter := SourceOriginalPacketWriter.unary_packet_run f.variables w
  have hA : ((advance captureProgram)^[a])
      (⟨some SourceOriginalVariableCapture.Label.scan, none, captureInput w⟩ :
        TM2.Cfg (fun _ : Stack => Bool) SourceOriginalVariableCapture.Label
          SourceOriginalVariableCapture.Control) =
      ⟨none, none, writerInput f.variables w⟩ := hcapture
  have hB : ((advance SourceOriginalPacketWriter.program)^[4*f.variables+3*w.length+6])
      (⟨some SourceOriginalPacketWriter.Label.scanN, none, writerInput f.variables w⟩ :
        SourceOriginalPacketWriter.Config) =
      ⟨none, none,
        ![List.replicate f.variables true, [], [], [],
          SourceOriginalBranchPackets.packet f.variables w]⟩ := hwriter
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs captureProgram
    SourceOriginalPacketWriter.program
    SourceOriginalVariableCapture.Label.scan SourceOriginalPacketWriter.Label.scanN
    (none : SourceOriginalVariableCapture.Control) none
    (none : SourceOriginalPacketWriter.Control) none
    (captureInput w) (writerInput f.variables w)
    (![List.replicate f.variables true, [], [], [],
      SourceOriginalBranchPackets.packet f.variables w] : Stack → List Bool)
    a (4*f.variables+3*w.length+6) hA hB
  refine ⟨t, by dsimp [w] at ht ⊢; omega, ?_⟩
  have hi : rawInit (1 : Stack)
      (BitMachineRawSequence.leftLabel
        (LB := SourceOriginalPacketWriter.Label) SourceOriginalVariableCapture.Label.scan)
      ((none, none) : SourceOriginalVariableCapture.Control × SourceOriginalPacketWriter.Control) w =
      (⟨some (BitMachineRawSequence.leftLabel
          (LB := SourceOriginalPacketWriter.Label) SourceOriginalVariableCapture.Label.scan),
        (none, none), captureInput w⟩ :
        TM2.Cfg (fun _ : Stack => Bool)
          (BitMachineRawSequence.Label SourceOriginalVariableCapture.Label
            SourceOriginalPacketWriter.Label)
          (SourceOriginalVariableCapture.Control × SourceOriginalPacketWriter.Control)) := by
    unfold rawInit captureInput
    congr 1
    funext k
    fin_cases k <;> rfl
  simpa only [program, hi, w] using hr

theorem packetizer_outputs (f : EncodedCNF.Formula) :
    packetizer.OutputsWithin (EncodedCNF.encode f)
      (SourceOriginalBranchPackets.packet f.variables (EncodedCNF.encode f))
      (10 * ((EncodedCNF.encode f).length + 1)^2) := by
  obtain ⟨t, ht, hr⟩ := packetizer_run f
  have hn := SourceOriginalVariableCapture.original_n_le_input f
  have hclock : 6*f.variables + 3*(EncodedCNF.encode f).length + 10 ≤
      10 * ((EncodedCNF.encode f).length + 1)^2 := by
    nlinarith [Nat.zero_le ((EncodedCNF.encode f).length ^ 2)]
  apply outputsWithin_of_raw_run (1 : Stack) (4 : Stack)
    (BitMachineRawSequence.leftLabel SourceOriginalVariableCapture.Label.scan)
    ((none, none) : SourceOriginalVariableCapture.Control × SourceOriginalPacketWriter.Control)
    program (EncodedCNF.encode f)
    (SourceOriginalBranchPackets.packet f.variables (EncodedCNF.encode f)) t
    (10 * ((EncodedCNF.encode f).length + 1)^2) (ht.trans hclock)
  all_goals rw [hr] <;> rfl

/-- The valid-CNF packetizer premise of the T10 front, discharged by one
fixed finite Boolean-stack machine. -/
theorem H_Packetizer_holds : T10Front.H_Packetizer := by
  refine ⟨packetizer, 10, 2, ?_⟩
  intro Φ
  exact packetizer_outputs Φ.val

#print axioms H_Packetizer_holds

end Paper2.Unit4Shell.PairMapGlue
