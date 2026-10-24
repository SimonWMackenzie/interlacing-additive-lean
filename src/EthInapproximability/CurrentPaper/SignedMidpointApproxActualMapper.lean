import EthInapproximability.CurrentPaper.SignedMidpointApproxORComposition
import EthInapproximability.CurrentPaper.SourceListMachineOuterFramed

/-!
# Actual canonical list mapper for signed approximation callbacks

This instantiates the fixed generic list machine with the actual midpoint
decision machine, physically frames every one-bit callback output, and then
runs the fixed OR machine. The source producer's branch list and its clock
remain separate obligations.
-/

namespace EthInapproximability.CurrentPaper.SignedMidpointApproxActualMapper

open EncodedETHTail

variable (M : BitMachine.Machine) (c d : ℕ)

noncomputable def callbackBound (packet : List Bool) : ℕ :=
  SignedMidpointApproxPolynomial.decisionCoefficient M c *
    (packet.length+1)^(d+2)

noncomputable def callbackOutput (packet : List Bool) : List Bool :=
  let C := SignedMidpointApproxPacket.decisionMachine M
  (C.run (callbackBound M c d packet) (C.init packet)).stk C.output

noncomputable def mapper : BitMachine.Machine :=
  SourceListMachineOuterFramed.machine
    (SignedMidpointApproxPacket.decisionMachine M)

noncomputable def satMachine : BitMachine.Machine :=
  BitMachineComposition.composition (mapper M) SourceListOR.machine

noncomputable def mapTime (k : ℕ) (branches : List Branch) : ℕ :=
  SourceListMachineOuter.canonicalBound
    (SourceListMachineOuterFramed.itemMachine
      (SignedMidpointApproxPacket.decisionMachine M))
    (branches.map fun b =>
      SignedMidpointApproxCanonical.packet M b.table b.threshold k)
    (SourceListMachineOuterFramed.framedOutput (callbackOutput M c d))
    (SourceListMachineOuterFramed.framedBound
      (callbackOutput M c d) (callbackBound M c d))

private theorem callback_on_branch
    (answer : List Bool → ℤ)
    (hM : M.ComputesWithin
      (fun table => EncodedETHTail.encodeInteger (answer table))
      (fun n => c * (n+1)^d))
    (k : ℕ) (b : Branch) :
    callbackOutput M c d
      (SignedMidpointApproxCanonical.packet M b.table b.threshold k) =
      [branchAccept answer k b] := by
  have h := SignedMidpointApproxCanonical.callback_fixed_polynomial M
    answer c d hM b.table b.threshold k
  have ho := BitMachine.outputsWithin_at_bound _ h
  exact ho.2

private theorem callback_item
    (answer : List Bool → ℤ)
    (hM : M.ComputesWithin
      (fun table => EncodedETHTail.encodeInteger (answer table))
      (fun n => c * (n+1)^d))
    (k : ℕ) (b : Branch) :
    (SignedMidpointApproxPacket.decisionMachine M).OutputsWithin
      (SignedMidpointApproxCanonical.packet M b.table b.threshold k)
      (callbackOutput M c d
        (SignedMidpointApproxCanonical.packet M b.table b.threshold k))
      (callbackBound M c d
        (SignedMidpointApproxCanonical.packet M b.table b.threshold k)) := by
  rw [callback_on_branch M c d answer hM k b]
  exact SignedMidpointApproxCanonical.callback_fixed_polynomial M
    answer c d hM b.table b.threshold k

theorem mapped_outputs (answer : List Bool → ℤ)
    (hM : M.ComputesWithin
      (fun table => EncodedETHTail.encodeInteger (answer table))
      (fun n => c * (n+1)^d))
    (k : ℕ) (branches : List Branch) :
    (mapper M).OutputsWithin
      (SignedMidpointApproxCanonical.packetList M k branches)
      (SignedMidpointApproxListBridge.bitList answer k branches)
      (mapTime M c d k branches) := by
  let xs := branches.map fun b =>
    SignedMidpointApproxCanonical.packet M b.table b.threshold k
  have hitem : ∀ x ∈ xs,
      (SignedMidpointApproxPacket.decisionMachine M).OutputsWithin x
        (callbackOutput M c d x) (callbackBound M c d x) := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    exact callback_item M c d answer hM k b
  have hmap := SourceListMachineOuterFramed.outputsWithin
    (SignedMidpointApproxPacket.decisionMachine M) xs
    (callbackOutput M c d) (callbackBound M c d) hitem
  have hout : xs.map (callbackOutput M c d) =
      (branches.map (branchAccept answer k)).map fun bit => [bit] := by
    dsimp [xs]
    simp only [List.map_map]
    apply List.map_congr_left
    intro b _
    exact callback_on_branch M c d answer hM k b
  rw [hout] at hmap
  simpa only [mapper, mapTime, SignedMidpointApproxCanonical.packetList,
    SignedMidpointApproxListBridge.bitList] using hmap

noncomputable def uniformFramedBound (L : ℕ) : ℕ :=
  SignedMidpointApproxPolynomial.decisionCoefficient M c * (L+1)^(d+2) +
    4 + 4*(UnaryBinaryEncoding.coefficient+7)

noncomputable def itemEnvelope (L : ℕ) : ℕ :=
  let F := SourceListMachineOuterFramed.itemMachine
    (SignedMidpointApproxPacket.decisionMachine M)
  let T := uniformFramedBound M c d L
  20*(L+1)*(L+1)+T+4*L+4+F.stackCount*(L+T*F.pushBound+1)+9

set_option maxHeartbeats 1000000 in
/-- A source branch-count bound multiplies one uniform packet cost once. In
particular, the approximation exponent is applied to packet length `L`, not
to the number of branches. -/
theorem mapTime_le_count (answer : List Bool → ℤ)
    (hM : M.ComputesWithin
      (fun table => EncodedETHTail.encodeInteger (answer table))
      (fun n => c * (n+1)^d))
    (k L : ℕ) (branches : List Branch)
    (hpacket : ∀ b ∈ branches,
      (SignedMidpointApproxCanonical.packet M b.table b.threshold k).length ≤ L) :
    mapTime M c d k branches ≤
      5*branches.length.bits.length+7 +
      (branches.length*itemEnvelope M c d L +
        branches.length*(4*branches.length.bits.length+7)) +
      (4*branches.length.bits.length +
        (EncodedCommunication.natField branches.length).length +
        branches.length*4+9) := by
  let C := SignedMidpointApproxPacket.decisionMachine M
  let F := SourceListMachineOuterFramed.itemMachine C
  let xs := branches.map fun b =>
    SignedMidpointApproxCanonical.packet M b.table b.threshold k
  let f := callbackOutput M c d
  let T := uniformFramedBound M c d L
  have hitem : ∀ x ∈ xs,
      SourceListMachineWork.itemCost F x
        (SourceListMachineOuterFramed.framedOutput f x)
        (SourceListMachineOuterFramed.framedBound f (callbackBound M c d) x) ≤
        itemEnvelope M c d L := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    let p := SignedMidpointApproxCanonical.packet M b.table b.threshold k
    have hbit : (f p).length = 1 := by
      change (callbackOutput M c d
        (SignedMidpointApproxCanonical.packet M b.table b.threshold k)).length = 1
      rw [callback_on_branch M c d answer hM k b]
      rfl
    have hframe : (SourceListMachineOuterFramed.framedOutput f p).length ≤ 4 := by
      unfold SourceListMachineOuterFramed.framedOutput
      rw [List.length_append, hbit]
      have hh := EncodedGraph.natField_length_upper 1
      omega
    have hclock : SourceListMachineOuterFramed.framedBound f
        (callbackBound M c d) p ≤ T := by
      have hlen : p.length ≤ L := hpacket b hb
      have hpow : (p.length+1)^(d+2) ≤ (L+1)^(d+2) :=
        Nat.pow_le_pow_left (by omega) _
      have hmul := Nat.mul_le_mul_left
        (SignedMidpointApproxPolynomial.decisionCoefficient M c) hpow
      change callbackBound M c d p + 2*(f p).length+2 +
        (UnaryBinaryEncoding.coefficient+7)*((f p).length+1)^2 ≤ T
      rw [hbit]
      change SignedMidpointApproxPolynomial.decisionCoefficient M c *
        (p.length+1)^(d+2) + 2*1+2 +
        (UnaryBinaryEncoding.coefficient+7)*(1+1)^2 ≤
        SignedMidpointApproxPolynomial.decisionCoefficient M c *
          (L+1)^(d+2) + 4 + 4*(UnaryBinaryEncoding.coefficient+7)
      omega
    simpa only [itemEnvelope, F, T] using
      SourceListMachineWork.itemCost_le_envelope F p
      (SourceListMachineOuterFramed.framedOutput f p)
      (SourceListMachineOuterFramed.framedBound f (callbackBound M c d) p)
      L 4 T (hpacket b hb) hframe hclock
  have hout : ∀ x ∈ xs,
      (SourceListMachineOuterFramed.framedOutput f x).length ≤ 4 := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    have hbit : (f (SignedMidpointApproxCanonical.packet M b.table b.threshold k)).length = 1 := by
      change (callbackOutput M c d
        (SignedMidpointApproxCanonical.packet M b.table b.threshold k)).length = 1
      rw [callback_on_branch M c d answer hM k b]
      rfl
    unfold SourceListMachineOuterFramed.framedOutput
    rw [List.length_append, hbit]
    have hh := EncodedGraph.natField_length_upper 1
    omega
  have h := SourceListMachineOuter.canonicalBound_le_count F xs
    (SourceListMachineOuterFramed.framedOutput f)
    (SourceListMachineOuterFramed.framedBound f (callbackBound M c d))
    (itemEnvelope M c d L) 4 hitem hout
  simpa only [mapTime, xs, List.length_map] using h

theorem sat_outputs (answer : List Bool → ℤ)
    (hM : M.ComputesWithin
      (fun table => EncodedETHTail.encodeInteger (answer table))
      (fun n => c * (n+1)^d))
    (input : List Bool) (branches : List Branch) (k A : ℕ)
    (herror : ∀ b ∈ branches, |answer b.table - (b.cost : ℤ)| ≤ (A : ℤ))
    (hgap : 2*A < k)
    (hyes : input ∈ EncodedCNF.Language → ∃ b ∈ branches,
      b.cost ≤ b.threshold)
    (hno : input ∉ EncodedCNF.Language → ∀ b ∈ branches,
      b.cost = b.threshold + k) :
    (satMachine M).OutputsWithin
      (SignedMidpointApproxCanonical.packetList M k branches)
      [satAnswer input]
      (mapTime M c d k branches +
        2*(SignedMidpointApproxListBridge.bitList answer k branches).length +
        2 + ((SignedMidpointApproxListBridge.bitList answer k branches).length+1)) := by
  exact SignedMidpointApproxORComposition.mapped_list_or_outputs
    (mapper M) M answer input branches k A (mapTime M c d k branches)
    (mapped_outputs M c d answer hM k branches)
    herror hgap hyes hno

theorem sat_outputs_linear (answer : List Bool → ℤ)
    (hM : M.ComputesWithin
      (fun table => EncodedETHTail.encodeInteger (answer table))
      (fun n => c * (n+1)^d))
    (input : List Bool) (branches : List Branch) (k A : ℕ)
    (herror : ∀ b ∈ branches, |answer b.table - (b.cost : ℤ)| ≤ (A : ℤ))
    (hgap : 2*A < k)
    (hyes : input ∈ EncodedCNF.Language → ∃ b ∈ branches,
      b.cost ≤ b.threshold)
    (hno : input ∉ EncodedCNF.Language → ∀ b ∈ branches,
      b.cost = b.threshold + k) :
    (satMachine M).OutputsWithin
      (SignedMidpointApproxCanonical.packetList M k branches)
      [satAnswer input] (mapTime M c d k branches + 18*branches.length+6) := by
  exact SignedMidpointApproxORComposition.mapped_list_or_linear
    (mapper M) M answer input branches k A (mapTime M c d k branches)
    (mapped_outputs M c d answer hM k branches)
    herror hgap hyes hno

end EthInapproximability.CurrentPaper.SignedMidpointApproxActualMapper
