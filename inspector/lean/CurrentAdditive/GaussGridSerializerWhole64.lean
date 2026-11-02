import CurrentAdditive.GaussSearchGridInput64

namespace CurrentAdditive.GaussGridSerializerWhole64
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open GaussSearchGridInput64

private theorem inline_id {K L V : Type*} [DecidableEq K]
    (q : TM2.Stmt (fun _ : K => Bool) L V) :
    BitMachineInline.stmt id id id none q = q := by
  induction q <;> simp [BitMachineInline.stmt, *]

theorem physical_serialize (S : Bank → List Bool)
    (h60 : S 60=[]) (h61 : S 61=[]) (h62 : S 62=[]) :
    ∃ t≤2*(packet S).length+2,∃ sf : Fin 4 → List Bool,
      ((advance program)^[t]) (initial S)=
      BitMachineStackEmbedding.cfg location S id id none
        (BitMachineBankSerialize.cfg none none sf [] [] (packet S)) := by
  let w := words S
  obtain ⟨t, sf, ht, hr⟩ := BitMachineBankSerialize.serialize w [] []
  let c := BitMachineBankSerialize.cfg (some (.emit 0)) none w [] [] []
  have hhalt : (((advance (BitMachineBankSerialize.program 4))^[t]) c).l = none := by
    change (BitMachineBankSerialize.run t c).l = none
    change (BitMachineBankSerialize.run t
      (BitMachineBankSerialize.cfg (some (.emit 0)) none w [] [] [])).l = none
    rw [hr]
    rfl
  obtain ⟨u, hu, he⟩ := BitMachineStackEmbedding.outputs location S
    id id id (by intro v; rfl) none
    (BitMachineBankSerialize.program 4) program
    (by intro l; simp [program, BitMachineStackEmbedding.stmt, inline_id])
    c t hhalt
  have hstart : BitMachineStackEmbedding.cfg location S id id none c = initial S := by
    have hb : BitMachineStackEmbedding.bank location S c.stk = S := by
      apply BitMachineStackEmbedding.bank_eq_self
      intro j
      cases j with
      | inl j => rfl
      | inr j =>
          fin_cases j <;>
            simp [c, BitMachineBankSerialize.cfg, BitMachineBankSerialize.contents,
              location, h60, h61, h62]
    simpa [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg, c, BitMachineBankSerialize.cfg, initial] using
      congrArg (fun bank => (⟨some (.emit 0),none,bank⟩ :
        TM2.Cfg (fun _ : Bank => Bool) (BitMachineBankSerialize.Label 4) (Option Bool))) hb
  have hfinish : ((advance program)^[u]) (initial S) =
      BitMachineStackEmbedding.cfg location S id id none
        (BitMachineBankSerialize.cfg none none sf [] []
          (BitMachineBankSerialize.encode (List.ofFn w))) := by
    rw [hstart] at he
    change ((advance program)^[u]) (initial S) =
      BitMachineStackEmbedding.cfg location S id id none
        (BitMachineBankSerialize.run t c) at he
    have hr' : BitMachineBankSerialize.run t c =
        BitMachineBankSerialize.cfg none none sf [] []
          (BitMachineBankSerialize.encode (List.ofFn w)) := by
      simpa only [c, List.append_nil] using hr
    rw [hr'] at he
    exact he
  have hpacket : BitMachineBankSerialize.encode (List.ofFn w) = packet S := by
    simp [packet, BitMachineBankCodec.encode_eq_list,
      BitMachineBankSerialize.encode, w]
  have ht' : t ≤ 2 * (packet S).length + 2 := by
    rw [← hpacket]
    exact ht
  rw [hpacket] at hfinish
  exact ⟨u,hu.trans ht',sf,hfinish⟩

#print axioms physical_serialize
end
end CurrentAdditive.GaussGridSerializerWhole64
