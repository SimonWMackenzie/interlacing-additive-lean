import EthInapproximability.CurrentPaper.SignedMidpointCapPacket

/-!
# Exact cap-packet decisions and framed OR semantics

This is the correctness interface for the eventual source-list mapper. Each
branch bit comes from the physical cap-construction/comparison packet machine.
The final OR is also a fixed Boolean-stack machine. The intervening list
mapper, approximation invocation and source encoder are not supplied here.
-/

namespace EthInapproximability.CurrentPaper.SignedMidpointCapOR

open EncodedETHTail

def packetBit (answer : List Bool → ℤ) (k : ℕ) (b : Branch) : Bool :=
  (BankFieldProjection.result (4 : Fin 5)
    (SignedMidpointCapPacket.finalPacket
      (encodeInteger (answer b.table)) b.threshold k)).headD false

def packetInputs (answer : List Bool → ℤ) (k : ℕ)
    (branches : List Branch) : List Bool :=
  SourceListEncoding.encode
    (branches.map (SignedMidpointCapPacket.branchPacket answer k))

def packetOutputs (answer : List Bool → ℤ) (k : ℕ)
    (branches : List Branch) : List Bool :=
  SourceListEncoding.encode
    ((branches.map (packetBit answer k)).map fun bit => [bit])

/-- The generic mapper must charge this sum of individual callback times,
not a power of the (possibly exponential) list count. -/
noncomputable def itemWork (answer : List Bool → ℤ) (k : ℕ)
    (branches : List Branch) : ℕ :=
  (branches.map fun b => SignedMidpointCapPacket.decisionTimeBound
    (SignedMidpointCapPacket.branchPacket answer k b).length).sum

theorem packetInputs_decode (answer : List Bool → ℤ) (k : ℕ)
    (branches : List Branch) :
    SourceListEncoding.decode (packetInputs answer k branches) =
      some (branches.map (SignedMidpointCapPacket.branchPacket answer k)) := by
  exact SourceListEncoding.decode_encode _

theorem packetOutputs_decode (answer : List Bool → ℤ) (k : ℕ)
    (branches : List Branch) :
    SourceListEncoding.decode (packetOutputs answer k branches) =
      some ((branches.map (packetBit answer k)).map fun bit => [bit]) := by
  exact SourceListEncoding.decode_encode _

theorem packetBit_correct (answer : List Bool → ℤ) (k : ℕ) (b : Branch) :
    packetBit answer k b = branchAccept answer k b := by
  rw [packetBit, SignedMidpointCapPacket.final_decision]
  simp [branchAccept]

theorem packetBit_run (answer : List Bool → ℤ) (k : ℕ) (b : Branch) :
    SignedMidpointCapPacket.decisionMachine.OutputsWithin
      (SignedMidpointCapPacket.branchPacket answer k b)
      [packetBit answer k b]
      (SignedMidpointCapPacket.decisionTimeBound
        (SignedMidpointCapPacket.branchPacket answer k b).length) := by
  rw [packetBit_correct]
  simpa only [SignedMidpointSemantics.branchBit_correct] using
    SignedMidpointCapPacket.branch_outputs_polynomial answer k b

theorem framed_list_correct (input : List Bool) (branches : List Branch)
    (answer : List Bool → ℤ) (k A : ℕ)
    (herror : ∀ b ∈ branches, |answer b.table - (b.cost : ℤ)| ≤ (A : ℤ))
    (hgap : 2*A < k)
    (hyes : input ∈ EncodedCNF.Language → ∃ b ∈ branches, b.cost ≤ b.threshold)
    (hno : input ∉ EncodedCNF.Language → ∀ b ∈ branches,
      b.cost = b.threshold + k) :
    SourceListOR.result
      (packetOutputs answer k branches) =
      [satAnswer input] := by
  have hf : packetBit answer k = SignedMidpointSemantics.branchBit answer k := by
    funext b
    rw [packetBit_correct, SignedMidpointSemantics.branchBit_correct]
  rw [packetOutputs, hf]
  exact SignedMidpointSemantics.physical_bits_list_correct
    input branches answer k A herror hgap hyes hno

end EthInapproximability.CurrentPaper.SignedMidpointCapOR
