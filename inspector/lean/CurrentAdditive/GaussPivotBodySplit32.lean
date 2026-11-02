import CurrentAdditive.GaussBranchFields32
import EthInapproximability.CurrentPaper.SourceListMachineFields

/-!
A physical copy retains the old V2 pivot-list packet on bank 19 while
placing it on bank 23. The fixed canonical binary-field parser then removes
the count header from bank 23, leaving the exact sequence of framed pivot
pairs there. Banks 24 and 25 are parser scratch/header output.
-/

namespace CurrentAdditive.GaussPivotBodySplit32

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open Turing Turing.TM2.Stmt BitMachineEncoding

abbrev Stack := Fin 32
abbrev Control := (Unit × Option Bool) ×
  ProtocolBinaryHeader.Control

inductive Label where
  | copy (l : SourceClausePreservingBroadcast.Label)
  | parse (l : ProtocolBinaryHeader.Label)
  | done
  deriving DecidableEq, Fintype

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def parserSlot : Fin 3 ↪ Stack where
  toFun j := ![23, 24, 25] j
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .copy l => BitMachineInline.stmt Label.copy
      (fun v => (v, (none, none))) Prod.fst
      (some (.parse .scan))
      (SourceClausePreservingBroadcast.program (19 : Stack) 31 [23] l)
  | .parse l => BitMachineStackEmbedding.stmt parserSlot Label.parse
      (fun v => (((), none), v)) Prod.snd (some .done)
      (ProtocolBinaryHeader.program l)
  | .done => .halt

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c c' : Config} {n : Nat} (h : run n c = c') (u : Nat) :
    run (n + u) c = run u c' := by
  rw [Nat.add_comm, run, Function.iterate_add_apply]
  exact congrArg (run u) h

def copied (packet : List Bool) (S : Stack → List Bool) :
    Stack → List Bool :=
  SourceClausePreservingBroadcast.result (19 : Stack) 31 [23] packet S

theorem physical_copy (packet : List Bool) (S : Stack → List Bool)
    (hpacket : S 19 = packet) (hscratch : S 31 = []) :
    ∃ t ≤ 2 * packet.length + 3,
      run t ⟨some (.copy .scan), (((), none), (none, none)), S⟩ =
        ⟨some (.parse .scan), (((), none), (none, none)),
          copied packet S⟩ := by
  have hcore := SourceClausePreservingBroadcast.run_halt
    (19 : Stack) 31 [23] (by decide) (by simp) (by simp)
    (by simp) packet S hpacket hscratch
  obtain ⟨u, hu, hr⟩ := BitMachineInline.outputs
    Label.copy (fun v => (v, (none, none))) Prod.fst
    (by intro v; rfl) (some (.parse .scan))
    (SourceClausePreservingBroadcast.program (19 : Stack) 31 [23])
    program (by intro l; rfl)
    (⟨some .scan, ((), none), S⟩ :
      TM2.Cfg (fun _ : Stack => Bool)
        SourceClausePreservingBroadcast.Label (Unit × Option Bool))
    (2 * packet.length + 3) (by rw [hcore])
  refine ⟨u, hu, ?_⟩
  change run u _ = _ at hr
  rw [hcore] at hr
  simpa [copied, BitMachineInline.cfg] using hr

noncomputable def parserFrame (S : Stack → List Bool)
    (c : TM2.Cfg (fun _ : Fin 3 => Bool)
      ProtocolBinaryHeader.Label ProtocolBinaryHeader.Control) : Config :=
  BitMachineStackEmbedding.cfg parserSlot S Label.parse
    (fun v => (((), none), v)) (some .done) c

theorem copied_input (packet : List Bool) (S : Stack → List Bool)
    (h23 : S 23 = []) (h24 : S 24 = []) (h25 : S 25 = []) :
    (copied packet S) 23 = packet ∧
    (copied packet S) 24 = [] ∧
    (copied packet S) 25 = [] := by
  constructor
  · have ht := SourceClausePreservingBroadcast.target_written
      (19 : Stack) 31 [23] (by simp) (by simp) (by decide)
      packet S 23 (by simp)
    simpa [copied, h23] using ht
  constructor
  · have ht := SourceClausePreservingBroadcast.other_preserved
      (19 : Stack) 31 [23] packet S 24
      (by decide) (by decide) (by simp)
    simpa [copied, h24] using ht
  · have ht := SourceClausePreservingBroadcast.other_preserved
      (19 : Stack) 31 [23] packet S 25
      (by decide) (by decide) (by simp)
    simpa [copied, h25] using ht

theorem parserFrame_start (packet : List Bool)
    (S : Stack → List Bool)
    (h23 : S 23 = packet) (h24 : S 24 = []) (h25 : S 25 = []) :
    parserFrame S
      (ProtocolBinaryHeader.cfg (some .scan) (none, none)
        packet [] []) =
      ⟨some (.parse .scan), (((), none), (none, none)), S⟩ := by
  unfold parserFrame
  simp only [BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    ProtocolBinaryHeader.cfg]
  congr 1
  apply BitMachineStackEmbedding.bank_eq_self
  intro j
  fin_cases j <;>
    simp [ProtocolBinaryHeader.stackContents, parserSlot, h23, h24, h25]

def body {m k : Nat} (ps : List (Fin m × Fin k)) : List Bool :=
  SourceListEncoding.fields
    (ps.map CurrentAdditive.GaussControlTrace.pivotPacket)

theorem physical_parse {m k : Nat}
    (ps : List (Fin m × Fin k))
    (foreign : Stack → List Bool) :
    let packet := CurrentAdditive.GaussControlTrace.pivotsPacket ps
    ∃ t ≤ 3 * ps.length.bits.length + 2,
      ∃ v : ProtocolBinaryHeader.Control,
      run t (parserFrame foreign
        (ProtocolBinaryHeader.cfg (some .scan) (none, none)
          packet [] [])) =
      parserFrame foreign
        (ProtocolBinaryHeader.cfg none v (body ps) []
          (true :: ps.length.bits)) := by
  dsimp only
  have hpacket : CurrentAdditive.GaussControlTrace.pivotsPacket ps =
      natField ps.length ++ body ps := by
    simp [CurrentAdditive.GaussControlTrace.pivotsPacket,
      body, SourceListEncoding.encode]
  obtain ⟨v, hcore⟩ := SourceListMachineFields.header_natField
    ps.length (body ps)
  rw [← hpacket] at hcore
  have hh : (ProtocolBinaryHeader.run
      (3 * ps.length.bits.length + 2)
      (ProtocolBinaryHeader.cfg (some .scan) (none, none)
        (CurrentAdditive.GaussControlTrace.pivotsPacket ps) [] [])).l = none := by
    rw [hcore]
    rfl
  obtain ⟨u, hu, hr⟩ := BitMachineStackEmbedding.outputs
    parserSlot foreign Label.parse (fun v => (((), none), v)) Prod.snd
    (by intro v; rfl) (some .done) ProtocolBinaryHeader.program
    program (by intro l; rfl)
    (ProtocolBinaryHeader.cfg (some .scan) (none, none)
      (CurrentAdditive.GaussControlTrace.pivotsPacket ps) [] [])
    (3 * ps.length.bits.length + 2) hh
  refine ⟨u, hu, v, ?_⟩
  change run u (parserFrame foreign _) =
    parserFrame foreign (ProtocolBinaryHeader.run _ _) at hr
  rw [hcore] at hr
  exact hr

theorem physical_split {m k : Nat}
    (ps : List (Fin m × Fin k)) (S : Stack → List Bool)
    (hpacket : S 19 =
      CurrentAdditive.GaussControlTrace.pivotsPacket ps)
    (h23 : S 23 = []) (h24 : S 24 = []) (h25 : S 25 = [])
    (hscratch : S 31 = []) :
    ∃ t ≤ 2 * (CurrentAdditive.GaussControlTrace.pivotsPacket ps).length + 3 +
      (3 * ps.length.bits.length + 2),
      ∃ v : ProtocolBinaryHeader.Control,
      run t ⟨some (.copy .scan), (((), none), (none, none)), S⟩ =
        parserFrame
          (copied (CurrentAdditive.GaussControlTrace.pivotsPacket ps) S)
          (ProtocolBinaryHeader.cfg none v (body ps) []
            (true :: ps.length.bits)) := by
  let packet := CurrentAdditive.GaussControlTrace.pivotsPacket ps
  obtain ⟨a, ha, hcopy⟩ := physical_copy packet S hpacket hscratch
  obtain ⟨hcopied23, hcopied24, hcopied25⟩ :=
    copied_input packet S h23 h24 h25
  have hstart : run a ⟨some (.copy .scan), (((), none), (none, none)), S⟩ =
      parserFrame (copied packet S)
        (ProtocolBinaryHeader.cfg (some .scan) (none, none)
          packet [] []) := by
    rw [hcopy]
    exact (parserFrame_start packet (copied packet S)
      hcopied23 hcopied24 hcopied25).symm
  obtain ⟨b, hb, v, hparse⟩ := physical_parse ps (copied packet S)
  refine ⟨a + b, ?_, v, ?_⟩
  · change a + b ≤ 2 * packet.length + 3 +
      (3 * ps.length.bits.length + 2)
    omega
  · exact (run_add hstart b).trans hparse

theorem split_body_at_23 {m k : Nat}
    (ps : List (Fin m × Fin k))
    (foreign : Stack → List Bool) (v : ProtocolBinaryHeader.Control) :
    (parserFrame foreign
      (ProtocolBinaryHeader.cfg none v (body ps) []
        (true :: ps.length.bits))).stk 23 = body ps := by
  exact BitMachineStackEmbedding.bank_at parserSlot foreign _ 0

theorem split_old_packet_at_19 {m k : Nat}
    (ps : List (Fin m × Fin k)) (S : Stack → List Bool)
    (v : ProtocolBinaryHeader.Control)
    (hpacket : S 19 =
      CurrentAdditive.GaussControlTrace.pivotsPacket ps) :
    (parserFrame
      (copied (CurrentAdditive.GaussControlTrace.pivotsPacket ps) S)
      (ProtocolBinaryHeader.cfg none v (body ps) []
        (true :: ps.length.bits))).stk 19 = S 19 := by
  simp only [parserFrame, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg]
  rw [BitMachineStackEmbedding.bank_outside parserSlot _ _ 19 (by
    rintro ⟨j, hj⟩
    fin_cases j <;> cases hj)]
  exact (SourceClausePreservingBroadcast.source_restored
    (19 : Stack) 31 [23] (by decide)
    (CurrentAdditive.GaussControlTrace.pivotsPacket ps) S).trans hpacket.symm

#print axioms physical_copy
#print axioms copied_input
#print axioms physical_split
#print axioms split_body_at_23
#print axioms split_old_packet_at_19

end CurrentAdditive.GaussPivotBodySplit32
