import EthInapproximability.CurrentPaper.BitMachineBankCodec

set_option autoImplicit false
namespace CurrentAdditive.V40LawPacket
open EthInapproximability.CurrentPaper

def bank (header word : List Bool) : Fin 2 → List Bool :=
  fun i => if i=0 then header else word

def packet (header word : List Bool) : List Bool :=
  BitMachineBankCodec.encode (bank header word)

theorem packet_decode (header word : List Bool) :
    BitMachineBankCodec.decode 2 (packet header word)=some (bank header word) := by
  exact BitMachineBankCodec.decode_encode _

theorem packet_length (header word : List Bool) :
    (packet header word).length=2*(header.length+word.length)+2 := by
  simp [packet,BitMachineBankCodec.encode_length,bank,Fin.sum_univ_succ]

end CurrentAdditive.V40LawPacket
