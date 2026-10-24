import EthInapproximability.CurrentPaper.SignedMidpointApproxPolynomial

/-!
# Framed branch-list interface for the actual approximation callback

This module names the exact canonical input/output lists expected by the
generic list mapper. Each item invokes the actual finite approximation
machine and physical midpoint callback. Mapper execution and upstream list
production remain separate obligations.
-/

namespace EthInapproximability.CurrentPaper.SignedMidpointApproxListBridge

open EncodedETHTail

noncomputable def packetItem (M : BitMachine.Machine) (k : ℕ) (b : Branch) : List Bool :=
  SignedMidpointApproxPacket.packet M b.table b.threshold k

noncomputable def packetList (M : BitMachine.Machine) (k : ℕ)
    (branches : List Branch) : List Bool :=
  SourceListEncoding.encode (branches.map (packetItem M k))

def bitList (answer : List Bool → ℤ) (k : ℕ)
    (branches : List Branch) : List Bool :=
  SourceListEncoding.encode
    ((branches.map (branchAccept answer k)).map fun bit => [bit])

noncomputable def callbackWork (M : BitMachine.Machine) (c d k : ℕ)
    (branches : List Branch) : ℕ :=
  (branches.map fun b => SignedMidpointApproxPolynomial.decisionCoefficient M c *
    ((packetItem M k b).length+1)^(d+2)).sum

theorem packetList_decode (M : BitMachine.Machine) (k : ℕ)
    (branches : List Branch) :
    SourceListEncoding.decode (packetList M k branches) =
      some (branches.map (packetItem M k)) := by
  exact SourceListEncoding.decode_encode _

theorem bitList_decode (answer : List Bool → ℤ) (k : ℕ)
    (branches : List Branch) :
    SourceListEncoding.decode (bitList answer k branches) =
      some ((branches.map (branchAccept answer k)).map fun bit => [bit]) := by
  exact SourceListEncoding.decode_encode _

theorem callback_item (M : BitMachine.Machine)
    (answer : List Bool → ℤ) (c d k : ℕ)
    (hM : M.ComputesWithin
      (fun table => encodeInteger (answer table)) (fun n => c*(n+1)^d))
    (b : Branch) :
    (SignedMidpointApproxPacket.decisionMachine M).OutputsWithin
      (packetItem M k b) [branchAccept answer k b]
      (SignedMidpointApproxPolynomial.decisionCoefficient M c *
        ((packetItem M k b).length+1)^(d+2)) := by
  simpa [packetItem, branchAccept] using
    SignedMidpointApproxPolynomial.callback_decision_fixed_polynomial
      M c d answer hM b.table b.threshold k

theorem callbackWork_le_count (M : BitMachine.Machine) (c d k L : ℕ)
    (branches : List Branch)
    (hpacket : ∀ b ∈ branches, (packetItem M k b).length ≤ L) :
    callbackWork M c d k branches ≤
      branches.length *
        (SignedMidpointApproxPolynomial.decisionCoefficient M c * (L+1)^(d+2)) := by
  induction branches with
  | nil => simp [callbackWork]
  | cons b rest ih =>
      have hb := hpacket b (by simp)
      have hr : ∀ x ∈ rest, (packetItem M k x).length ≤ L := by
        intro x hx
        exact hpacket x (by simp [hx])
      have hp : ((packetItem M k b).length+1)^(d+2) ≤ (L+1)^(d+2) :=
        Nat.pow_le_pow_left (by omega) _
      have hitem := Nat.mul_le_mul_left
        (SignedMidpointApproxPolynomial.decisionCoefficient M c) hp
      have hrest := ih hr
      simp only [callbackWork, List.map_cons, List.sum_cons,
        List.length_cons] at *
      rw [Nat.succ_mul]
      omega

theorem packetList_length (M : BitMachine.Machine) (k L : ℕ)
    (branches : List Branch)
    (hpacket : ∀ b ∈ branches, (packetItem M k b).length ≤ L) :
    (packetList M k branches).length ≤
      3*branches.length*(L+1)+1 := by
  exact SourceListEncoding.encode_map_length_le branches (packetItem M k) L hpacket

theorem bitList_OR_correct (input : List Bool) (branches : List Branch)
    (answer : List Bool → ℤ) (k A : ℕ)
    (herror : ∀ b ∈ branches, |answer b.table - (b.cost : ℤ)| ≤ (A : ℤ))
    (hgap : 2*A < k)
    (hyes : input ∈ EncodedCNF.Language → ∃ b ∈ branches, b.cost ≤ b.threshold)
    (hno : input ∉ EncodedCNF.Language → ∀ b ∈ branches,
      b.cost = b.threshold + k) :
    SourceListOR.result (bitList answer k branches) = [satAnswer input] := by
  rw [bitList, SourceListOR.result_canonical]
  congr 1
  simpa only [List.any_map] using
    listAccept_correct input branches answer k A herror hgap hyes hno

end EthInapproximability.CurrentPaper.SignedMidpointApproxListBridge
