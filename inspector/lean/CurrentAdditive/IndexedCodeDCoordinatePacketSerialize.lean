import CurrentAdditive.IndexedCodeDCoordinatePacketCopies
import EthInapproximability.CurrentPaper.BitMachineBankSerialize
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-! Fixed physical serialization of the V2 getter's ten-cell input bank.
The separate copy theorem loads cells 17 and 18 from retained sources. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineBankCodec
open EthInapproximability.CurrentPaper.BitMachineBankSerialize
open CurrentAdditive.GaussListContext
open Turing BitMachineEncoding

def coordinatePacketBank (word : List Bool) (p : ℕ) :
    BitMachineBankSerialize.Bank 10 :=
  PreservingV2Program.initialBank word p

theorem coordinatePacketBank_bytes (word : List Bool) (p : ℕ) :
    BitMachineBankSerialize.encode (List.ofFn (coordinatePacketBank word p)) =
      codeDGetterPacket word p := by
  unfold codeDGetterPacket coordinatePacketBank
  rw [BitMachineBankCodec.encode_eq_list]
  rfl

def packetLocate : BitMachineBankSerialize.Stack 10 ↪ packetStack where
  toFun
    | .inl i => ⟨10 + i.val, by omega⟩
    | .inr i => ![21, 22, 5] i
  inj' := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        apply congrArg Sum.inl
        apply Fin.ext
        have hv := congrArg Fin.val h
        dsimp at hv
        omega
      | inr b =>
        fin_cases b <;> have hv := congrArg Fin.val h <;>
          dsimp at hv <;> omega
    | inr a =>
      cases b with
      | inl b =>
        fin_cases a <;> have hv := congrArg Fin.val h <;>
          dsimp at hv <;> omega
      | inr b => fin_cases a <;> fin_cases b <;> simp_all

abbrev PacketLabel := BitMachineBankSerialize.Label 10 ⊕ Unit
abbrev PacketControl := Option Bool
abbrev PacketConfig := TM2.Cfg (fun _ : packetStack => Bool)
  PacketLabel PacketControl

def packetSerializeProgram : PacketLabel →
    TM2.Stmt (fun _ : packetStack => Bool) PacketLabel PacketControl
  | .inl l => BitMachineStackEmbedding.stmt packetLocate Sum.inl id id
      (some (.inr ())) (BitMachineBankSerialize.program 10 l)
  | .inr () => .halt

def packetSerializeRun (t : ℕ) (c : PacketConfig) :=
  ((advance packetSerializeProgram)^[t]) c

noncomputable def packetFrame (foreign : packetStack → List Bool)
    (c : TM2.Cfg (fun _ : BitMachineBankSerialize.Stack 10 => Bool)
      (BitMachineBankSerialize.Label 10) (Option Bool)) : PacketConfig :=
  BitMachineStackEmbedding.cfg packetLocate foreign Sum.inl id
    (some (.inr ())) c

theorem coordinate_packet_serialize (word : List Bool) (p : ℕ)
    (foreign : packetStack → List Bool) (suffix : List Bool) :
    ∃ t ≤ 2*(codeDGetterPacket word p).length+2,
      ∃ S' : BitMachineBankSerialize.Bank 10,
        packetSerializeRun t (packetFrame foreign
          (BitMachineBankSerialize.cfg (some (.emit 0)) none
            (coordinatePacketBank word p) [] [] suffix)) =
          packetFrame foreign
            (BitMachineBankSerialize.cfg none none S' [] []
              (codeDGetterPacket word p ++ suffix)) := by
  obtain ⟨t, S', ht, hr⟩ :=
    BitMachineBankSerialize.serialize (coordinatePacketBank word p) [] suffix
  have hh : (BitMachineBankSerialize.run t
      (BitMachineBankSerialize.cfg (some (.emit 0)) none
        (coordinatePacketBank word p) [] [] suffix)).l = none := by
    rw [hr]
    rfl
  obtain ⟨u, hu, he⟩ := BitMachineStackEmbedding.outputs
    packetLocate foreign Sum.inl id id (by intro v; rfl)
    (some (.inr ())) (BitMachineBankSerialize.program 10)
    packetSerializeProgram (by intro l; rfl)
    (BitMachineBankSerialize.cfg (some (.emit 0)) none
      (coordinatePacketBank word p) [] [] suffix) t hh
  refine ⟨u, ?_, S', ?_⟩
  · rw [coordinatePacketBank_bytes] at ht
    omega
  · change packetSerializeRun u (packetFrame foreign _) =
      packetFrame foreign (BitMachineBankSerialize.run t _) at he
    rw [hr] at he
    simpa only [coordinatePacketBank_bytes] using he

#print axioms coordinatePacketBank_bytes
#print axioms coordinate_packet_serialize

end CurrentAdditive.IndexedExecutableStepRecovery
