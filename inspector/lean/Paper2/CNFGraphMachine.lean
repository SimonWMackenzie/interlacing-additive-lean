import Paper2.CNFGraphGuard
import Paper2.A4T10Envelope
import Paper2.A4Packetizer
import EthInapproximability.CurrentPaper.BankFieldProjection

/-!
Paper A, lock v12 `appendices/C-parameters.tex:204-206`, physical graph-word
compiler on every raw CNF input. All constituent machines are admitted; the
router, packetizer, T10 chain, and graph-field projection are physically
composed with charged handoffs. No graph decider is assumed here.
-/

namespace Paper2.CNFGraphGuard

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2.Unit4Shell
open Paper2.Unit4Shell.T10Finite
open AFront.T10

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- The all-input semantic graph word. -/
noncomputable def graphWord {N : ℕ} (hN : 1 ≤ N) (w : List Bool) : List Bool :=
  EncodedGraph.encode (t10Graph D B (routed hN w))

/-- The fixed physical controller: validate and route CNF, write its original-size
packet, run the Paper B T10 chain, then extract the graph field. -/
noncomputable def graphMachine (N : ℕ) : BitMachine.Machine :=
  BitMachineComposition.composition
    (BitMachineComposition.composition CNFValidator.machine (Front.scanMachine N))
    (BitMachineComposition.composition Unit4Shell.PairMapGlue.packetizer
      (BitMachineComposition.composition (Unit4Shell.T10Machine.chain D B)
        (BankFieldProjection.machine (1 : Fin 2))))

private def scanTime (w : List Bool) : ℕ :=
  250 * (w.length + 1)^3 + 2 * (CNFValidator.result w).length + 2 +
    (2 * w.length + 3)

private noncomputable def graphTime {N : ℕ} (hN : 1 ≤ N) (w : List Bool) : ℕ :=
  let Φ := routed hN w
  let scanned := EncodedCNF.encode Φ.val
  let packet := SourceOriginalBranchPackets.packet Φ.val.variables scanned
  let graphPacket := SourceOriginalBranchPackets.packet Φ.val.variables
    (graphWord D B hN w)
  scanTime w + 2 * scanned.length + 2 +
    (10 * (scanned.length + 1)^2 + 2 * packet.length + 2 +
      (Unit4Shell.T10Machine.chainTime D B Φ + 2 * graphPacket.length + 2 +
        8 * (graphPacket.length + 1)))

theorem graphMachine_outputs {N : ℕ} (hN : 1 ≤ N) (w : List Bool) :
    (graphMachine D B N).OutputsWithin w (graphWord D B hN w)
      (graphTime D B hN w) := by
  let Φ := routed hN w
  let scanned := EncodedCNF.encode Φ.val
  let packet := SourceOriginalBranchPackets.packet Φ.val.variables scanned
  let graphPacket := SourceOriginalBranchPackets.packet Φ.val.variables
    (graphWord D B hN w)
  have hscan0 := BitMachineComposition.composition_outputsWithin CNFValidator.machine
    (Front.scanMachine N) (CNFValidator.Runtime.outputs w) (Front.scan_outputs hN w)
  have hscan : (BitMachineComposition.composition CNFValidator.machine
      (Front.scanMachine N)).OutputsWithin w scanned (scanTime w) := by
    simpa only [scanTime, scanned, Φ, AFront.Route.scanTarget_eq_encode] using hscan0
  have hp : Unit4Shell.PairMapGlue.packetizer.OutputsWithin scanned packet
      (10 * (scanned.length + 1)^2) := by
    exact Unit4Shell.PairMapGlue.packetizer_outputs Φ.val
  have hc : (Unit4Shell.T10Machine.chain D B).OutputsWithin packet graphPacket
      (Unit4Shell.T10Machine.chainTime D B Φ) := by
    exact Unit4Shell.T10Machine.chain_outputs D B Φ
  have he : (BankFieldProjection.machine (1 : Fin 2)).OutputsWithin graphPacket
      (graphWord D B hN w) (8 * (graphPacket.length + 1)) := by
    simpa only [graphPacket, graphWord, SourceOriginalBranchPackets.packet,
      SourceOriginalBranchPackets.bank, BankFieldProjection.result_encode, Matrix.cons_val_one,
      Matrix.cons_val_zero] using BankFieldProjection.outputs (1 : Fin 2) graphPacket
  have hcomp := BitMachineComposition.composition_outputsWithin
    (BitMachineComposition.composition CNFValidator.machine (Front.scanMachine N))
    (BitMachineComposition.composition Unit4Shell.PairMapGlue.packetizer
      (BitMachineComposition.composition (Unit4Shell.T10Machine.chain D B)
        (BankFieldProjection.machine (1 : Fin 2)))) hscan
      (BitMachineComposition.composition_outputsWithin Unit4Shell.PairMapGlue.packetizer
        (BitMachineComposition.composition (Unit4Shell.T10Machine.chain D B)
          (BankFieldProjection.machine (1 : Fin 2))) hp
        (BitMachineComposition.composition_outputsWithin (Unit4Shell.T10Machine.chain D B)
          (BankFieldProjection.machine (1 : Fin 2)) hc he))
  simpa only [graphMachine, graphTime, Φ, scanned, packet, graphPacket] using hcomp

private theorem routed_length_poly {N : ℕ} (hN : 1 ≤ N) :
    Unit4Shell.Poly.PolyIn (fun w : List Bool => w.length)
      (fun w => (EncodedCNF.encode (routed hN w).val).length) := by
  let K := (Front.phi N true).length + (Front.phi N false).length
  apply Unit4Shell.Poly.mono (b := fun w : List Bool => w.length + K)
  · intro w
    have h := Front.scanTarget_length hN w
    rw [AFront.Route.scanTarget_eq_encode N w] at h
    simpa only [routed, K, Nat.add_assoc] using h
  · exact Unit4Shell.Poly.add Unit4Shell.Poly.self (Unit4Shell.Poly.const K)

private theorem lift_routed_poly {N : ℕ} (hN : 1 ≤ N)
    {a : ValidFormula → ℕ} (ha : Unit4Shell.Poly.PolyIn Unit4Shell.T10Envelope.L a) :
    Unit4Shell.Poly.PolyIn (fun w : List Bool => w.length)
      (fun w => a (routed hN w)) := by
  obtain ⟨C, E, h⟩ := ha
  exact Unit4Shell.Poly.transfer (routed_length_poly hN)
    ⟨C, E, fun w => h (routed hN w)⟩

private theorem scanTime_poly :
    Unit4Shell.Poly.PolyIn (fun w : List Bool => w.length) scanTime := by
  open Unit4Shell.Poly in
  have hr : PolyIn (fun w : List Bool => w.length)
      (fun w => (CNFValidator.result w).length) :=
    mono (fun w => AFront.Route.result_length w) (add self (const 1))
  unfold scanTime
  exact add
    (add (add (mul (const 250) (pow (add self (const 1)) 3))
      (mul (const 2) hr)) (const 2))
    (add (mul (const 2) self) (const 3))

private theorem graphTime_poly {N : ℕ} (hN : 1 ≤ N) :
    Unit4Shell.Poly.PolyIn (fun w : List Bool => w.length)
      (graphTime D B hN) := by
  open Unit4Shell.Poly in
  let sz : List Bool → ℕ := fun w => w.length
  let s : List Bool → ℕ := fun w => (EncodedCNF.encode (routed hN w).val).length
  let p : List Bool → ℕ := fun w =>
    (SourceOriginalBranchPackets.packet (routed hN w).val.variables
      (EncodedCNF.encode (routed hN w).val)).length
  let q : List Bool → ℕ := fun w =>
    (SourceOriginalBranchPackets.packet (routed hN w).val.variables
      (graphWord D B hN w)).length
  let c : List Bool → ℕ := fun w => Unit4Shell.T10Machine.chainTime D B (routed hN w)
  have hs : PolyIn sz s := routed_length_poly hN
  have hp : PolyIn sz p :=
    lift_routed_poly hN (Unit4Shell.T10Envelope.x0_poly)
  have hq : PolyIn sz q :=
    lift_routed_poly hN (Unit4Shell.T10Envelope.chainOutput_poly D B)
  have hc : PolyIn sz c :=
    lift_routed_poly hN (Unit4Shell.T10Envelope.chainTime_poly D B)
  have htime : PolyIn sz (fun w => scanTime w + 2 * s w + 2 +
      (10 * (s w + 1)^2 + 2 * p w + 2 +
        (c w + 2 * q w + 2 + 8 * (q w + 1)))) :=
    add (add (add scanTime_poly (mul (const 2) hs)) (const 2))
      (add (add (add (mul (const 10) (pow (add hs (const 1)) 2))
        (mul (const 2) hp)) (const 2))
        (add (add (add hc (mul (const 2) hq)) (const 2))
          (mul (const 8) (add hq (const 1)))))
  simpa only [graphTime, s, p, q, c, sz] using htime

/-- The physical graph compiler is polynomial-time on every raw CNF word. -/
theorem graphWord_polytime {N : ℕ} (hN : 1 ≤ N) :
    BitMachine.Polytime (graphWord D B hN) := by
  obtain ⟨C, E, hclock⟩ := graphTime_poly D B hN
  exact ⟨graphMachine D B N, C, E, fun w =>
    BitMachine.outputsWithin_mono _ (graphMachine_outputs D B hN w) (hclock w)⟩

/-- The concrete physical all-input many-one reduction to exact three-colourability. -/
theorem cnf_reduces_graph_three (D : DinurReduction)
    (B : BOTReduction (booleanOccurrence D)) {N : ℕ} (hN : 1 ≤ N) :
    EncodedComplexity.Reduces EncodedCNF.Language GraphThreeLanguage :=
  ⟨graphWord D B hN, graphWord_polytime D B hN,
    fun w => (routed_graph_mem_iff D B hN w).symm⟩

#print axioms graphMachine_outputs
#print axioms graphWord_polytime
#print axioms cnf_reduces_graph_three

end Paper2.CNFGraphGuard
