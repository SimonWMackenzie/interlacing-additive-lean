import CurrentAdditive.GaussVectorPacketClock

/-! Per-column work-packet layout for the physical vector outer loop.  Each
item repeats the materialized matrix and the free-column index, alongside one
current column.  The repetition is polynomially bounded; an actual TM2
producer from the single Gauss state remains to be built. -/

namespace CurrentAdditive.GaussCertificateWorkList

open EthInapproximability.CurrentPaper
open CurrentAdditive.GaussFirstFreeCandidate
open CurrentAdditive.GaussCertificateVectorABI

def workBank {m k : Nat} (B : Fin m → Fin k → ℚ)
    (f j : Fin k) : BitMachineBankCodec.Bank 3 :=
  ![CurrentAdditive.GaussPhysical.encodeTypedMatrix B,
    List.replicate j.val true, List.replicate f.val true]

def workPacket {m k : Nat} (B : Fin m → Fin k → ℚ)
    (f j : Fin k) : List Bool :=
  BitMachineBankCodec.encode (workBank B f j)

def workPackets {m k : Nat} (B : Fin m → Fin k → ℚ)
    (f : Fin k) : List (List Bool) :=
  (List.finRange k).map (workPacket B f)

theorem workPacket_length {m k : Nat} (B : Fin m → Fin k → ℚ)
    (f j : Fin k) :
    (workPacket B f j).length =
      2 * ((CurrentAdditive.GaussPhysical.encodeTypedMatrix B).length +
        j.val + f.val) + 3 := by
  rw [workPacket, BitMachineBankCodec.encode_length]
  simp [workBank, Fin.sum_univ_succ, Nat.add_assoc]

theorem workPacket_length_le {m k : Nat} (B : Fin m → Fin k → ℚ)
    (f j : Fin k) :
    (workPacket B f j).length ≤
      2 * ((CurrentAdditive.GaussPhysical.encodeTypedMatrix B).length +
        2 * k) + 3 := by
  rw [workPacket_length]
  have hf := f.isLt
  have hj := j.isLt
  omega

theorem workPackets_length {m k : Nat} (B : Fin m → Fin k → ℚ)
    (f : Fin k) :
    (SourceListEncoding.encode (workPackets B f)).length ≤
      3 * k *
        (2 * ((CurrentAdditive.GaussPhysical.encodeTypedMatrix B).length +
          2 * k) + 4) + 1 := by
  have h := SourceListEncoding.encode_map_length_le
    (List.finRange k) (workPacket B f)
    (2 * ((CurrentAdditive.GaussPhysical.encodeTypedMatrix B).length +
      2 * k) + 3) (by
      intro j hj
      exact workPacket_length_le B f j)
  simpa [workPackets] using h

theorem workPackets_count {m k : Nat} (B : Fin m → Fin k → ℚ)
    (f : Fin k) : (workPackets B f).length = k := by
  simp [workPackets]

#print axioms workPackets_length

end CurrentAdditive.GaussCertificateWorkList
