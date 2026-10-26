import EthInapproximability.CurrentPaper.SignedMidpointApproxListBridge

/-!
# Computable canonical packet for the approximation callback

The proof-facing callback packet uses an abstract finite-bank embedding to
recycle general simulation lemmas. The bank below gives the same bit string
by an explicit case split; this is the representation an upstream concrete
encoder can target without classically choosing inverse stack locations.
-/

namespace EthInapproximability.CurrentPaper.SignedMidpointApproxCanonical

variable (M : BitMachine.Machine)

def bank (table : List Bool) (Y k : ℕ) :
    Fin (SignedMidpointApproxPacket.Width M) → List Bool :=
  fun j => match (SignedMidpointApproxPacket.stackEquiv M).symm j with
    | .inl x => if x = M.input then table else []
    | .inr i => ![List.replicate Y true, List.replicate k true, [], []] i

def packet (table : List Bool) (Y k : ℕ) : List Bool :=
  BitMachineBankCodec.encode (bank M table Y k)

theorem bank_eq (table : List Bool) (Y k : ℕ) :
    bank M table Y k = SignedMidpointApproxPacket.inputBank M table Y k := by
  funext j
  have hkey : (SignedMidpointApproxPacket.stackEquiv M)
      ((SignedMidpointApproxPacket.stackEquiv M).symm j) = j :=
    (SignedMidpointApproxPacket.stackEquiv M).apply_symm_apply j
  cases h : (SignedMidpointApproxPacket.stackEquiv M).symm j with
  | inl x =>
      rw [← hkey, h]
      simp only [bank, SignedMidpointApproxPacket.inputBank,
        Equiv.symm_apply_apply, SignedMidpointApproxCore.start,
        BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
        BitMachineInline.cfg]
      change (if x = M.input then table else []) =
        BitMachineStackEmbedding.bank (SignedMidpointApproxCore.localStack M)
          (SignedMidpointApproxCore.foreign M Y k) (M.init table).stk
          ((SignedMidpointApproxCore.localStack M) x)
      rw [BitMachineStackEmbedding.bank_at]
      rfl
  | inr x =>
      rw [← hkey, h]
      simp only [bank, SignedMidpointApproxPacket.inputBank,
        Equiv.symm_apply_apply, SignedMidpointApproxCore.start,
        BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
        BitMachineInline.cfg]
      change (![List.replicate Y true, List.replicate k true, [], []] x) =
        BitMachineStackEmbedding.bank (SignedMidpointApproxCore.localStack M)
          (SignedMidpointApproxCore.foreign M Y k) (M.init table).stk (.inr x)
      rw [BitMachineStackEmbedding.bank_outside]
      · rfl
      · intro hx
        obtain ⟨v,hv⟩ := hx
        cases hv

theorem packet_eq (table : List Bool) (Y k : ℕ) :
    packet M table Y k = SignedMidpointApproxPacket.packet M table Y k := by
  rw [packet, SignedMidpointApproxPacket.packet, bank_eq]

def packetList (k : ℕ) (branches : List EncodedETHTail.Branch) : List Bool :=
  SourceListEncoding.encode
    (branches.map fun b => packet M b.table b.threshold k)

theorem packetList_eq (k : ℕ) (branches : List EncodedETHTail.Branch) :
    packetList M k branches =
      SignedMidpointApproxListBridge.packetList M k branches := by
  simp only [packetList, SignedMidpointApproxListBridge.packetList]
  congr 1
  apply List.map_congr_left
  intro b _
  exact packet_eq M b.table b.threshold k

theorem callback_fixed_polynomial
    (answer : List Bool → ℤ) (c d : ℕ)
    (hM : M.ComputesWithin
      (fun table => EncodedETHTail.encodeInteger (answer table))
      (fun n => c*(n+1)^d))
    (table : List Bool) (Y k : ℕ) :
    (SignedMidpointApproxPacket.decisionMachine M).OutputsWithin
      (packet M table Y k)
      [decide (2*answer table < (2*Y+k : ℤ))]
      (SignedMidpointApproxPolynomial.decisionCoefficient M c *
        ((packet M table Y k).length+1)^(d+2)) := by
  rw [packet_eq]
  exact SignedMidpointApproxPolynomial.callback_decision_fixed_polynomial
    M c d answer hM table Y k

end EthInapproximability.CurrentPaper.SignedMidpointApproxCanonical
