import EthInapproximability.CurrentPaper.SignedMidpointApproxCanonical
import EthInapproximability.CurrentPaper.BitMachineComposition

/-!
# Composition interface for the signed callback list and Boolean OR

This theorem composes an actual, separately proved list-mapper run with the
fixed all-input OR machine. It does not construct the mapper or assume a
per-item runtime certificate. In particular, the mapper's time is passed
through unchanged; the only extra charge is linear in its framed bit-list
output.
-/

namespace EthInapproximability.CurrentPaper.SignedMidpointApproxORComposition

open EncodedETHTail

theorem bitList_length_le (answer : List Bool → ℤ) (k : ℕ)
    (branches : List Branch) :
    (SignedMidpointApproxListBridge.bitList answer k branches).length ≤
      6 * branches.length + 1 := by
  have h := SourceListEncoding.encode_map_length_le branches
    (fun b => [branchAccept answer k b]) 1 (by intro b hb; simp)
  simp only [SignedMidpointApproxListBridge.bitList, List.map_map,
    Function.comp_def] at *
  omega

theorem mapped_list_or_outputs (Mmap : BitMachine.Machine)
    (M : BitMachine.Machine) (answer : List Bool → ℤ)
    (input : List Bool) (branches : List Branch) (k A t : ℕ)
    (hmap : Mmap.OutputsWithin
      (SignedMidpointApproxCanonical.packetList M k branches)
      (SignedMidpointApproxListBridge.bitList answer k branches) t)
    (herror : ∀ b ∈ branches, |answer b.table - (b.cost : ℤ)| ≤ (A : ℤ))
    (hgap : 2 * A < k)
    (hyes : input ∈ EncodedCNF.Language → ∃ b ∈ branches, b.cost ≤ b.threshold)
    (hno : input ∉ EncodedCNF.Language → ∀ b ∈ branches,
      b.cost = b.threshold + k) :
    (BitMachineComposition.composition Mmap SourceListOR.machine).OutputsWithin
      (SignedMidpointApproxCanonical.packetList M k branches)
      [satAnswer input]
      (t + 2*(SignedMidpointApproxListBridge.bitList answer k branches).length +
        2 + ((SignedMidpointApproxListBridge.bitList answer k branches).length + 1)) := by
  have hor := SourceListOR.outputs
    (SignedMidpointApproxListBridge.bitList answer k branches)
  rw [SignedMidpointApproxListBridge.bitList_OR_correct input branches answer k A
    herror hgap hyes hno] at hor
  exact BitMachineComposition.composition_outputsWithin Mmap SourceListOR.machine
    hmap hor

theorem mapped_list_or_linear (Mmap : BitMachine.Machine)
    (M : BitMachine.Machine) (answer : List Bool → ℤ)
    (input : List Bool) (branches : List Branch) (k A t : ℕ)
    (hmap : Mmap.OutputsWithin
      (SignedMidpointApproxCanonical.packetList M k branches)
      (SignedMidpointApproxListBridge.bitList answer k branches) t)
    (herror : ∀ b ∈ branches, |answer b.table - (b.cost : ℤ)| ≤ (A : ℤ))
    (hgap : 2 * A < k)
    (hyes : input ∈ EncodedCNF.Language → ∃ b ∈ branches, b.cost ≤ b.threshold)
    (hno : input ∉ EncodedCNF.Language → ∀ b ∈ branches,
      b.cost = b.threshold + k) :
    (BitMachineComposition.composition Mmap SourceListOR.machine).OutputsWithin
      (SignedMidpointApproxCanonical.packetList M k branches)
      [satAnswer input] (t + 18 * branches.length + 6) := by
  have h := mapped_list_or_outputs Mmap M answer input branches k A t
    hmap herror hgap hyes hno
  have hlen := bitList_length_le answer k branches
  apply BitMachine.outputsWithin_mono _ h
  omega

end EthInapproximability.CurrentPaper.SignedMidpointApproxORComposition
