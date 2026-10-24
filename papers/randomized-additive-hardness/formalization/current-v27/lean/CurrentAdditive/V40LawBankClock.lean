import CurrentAdditive.V40LawBankMap

set_option autoImplicit false
namespace CurrentAdditive.V40LawBankMap
open EthInapproximability.CurrentPaper

theorem output_packet_size (M : BitMachine.Machine) (header word output : List Bool)
    (T : ℕ) (h : M.OutputsWithin word output T) :
    (V40LawPacket.packet header output).length≤(V40LawPacket.packet header word).length+
      2*T*M.pushBound := by
  have ho:=BitMachine.output_length_bound M h
  rw [V40LawPacket.packet_length,V40LawPacket.packet_length]
  calc
    2*(header.length+output.length)+2≤2*(header.length+word.length+T*M.pushBound)+2 := by omega
    _ = 2*(header.length+word.length)+2+2*T*M.pushBound := by ring

theorem outputs_charged (M : BitMachine.Machine) (header word output : List Bool)
    (T : ℕ) (h : M.OutputsWithin word output T) :
    (liftMachine M).OutputsWithin (V40LawPacket.packet header word)
      (V40LawPacket.packet header output)
      (7*((V40LawPacket.packet header word).length+2)+(1+4*M.pushBound)*T) := by
  have hr:=outputs_canonical M header word output T h
  apply BitMachine.outputsWithin_mono _ hr
  have hs:=output_packet_size M header word output T h
  have he : 2*T*M.pushBound=2*(T*M.pushBound) := by ring
  rw [he] at hs
  have he' : (1+4*M.pushBound)*T=T+4*(T*M.pushBound) := by ring
  rw [he']
  omega

theorem outputs_polynomial (M : BitMachine.Machine) (c d : ℕ)
    (header word output : List Bool)
    (h : M.OutputsWithin word output (c*(word.length+1)^d)) :
    (liftMachine M).OutputsWithin (V40LawPacket.packet header word)
      (V40LawPacket.packet header output)
      (10*(c+1)*(M.pushBound+1)*((V40LawPacket.packet header word).length+3)^(d+1)) := by
  let I:=(V40LawPacket.packet header word).length
  let p:=M.pushBound
  let b:=I+3
  let q:=b^(d+1)
  have hword : word.length+1≤b := by
    have hp:=V40LawPacket.packet_length header word
    dsimp [I,b]
    omega
  have hpow : (word.length+1)^d≤q :=
    (Nat.pow_le_pow_left hword d).trans
      (Nat.pow_le_pow_right (by dsimp [b,I]; omega) (by omega))
  have hbase : I+2≤q := by
    have hp : b≤q := by
      simpa only [pow_one] using
        (Nat.pow_le_pow_right (by dsimp [b,I]; omega) (show 1≤d+1 by omega))
    dsimp [b] at hp
    omega
  have htime : c*(word.length+1)^d≤c*q:=Nat.mul_le_mul_left c hpow
  have hrun:=outputs_charged M header word output (c*(word.length+1)^d) h
  apply BitMachine.outputsWithin_mono _ hrun
  change 7*(I+2)+(1+4*p)*(c*(word.length+1)^d)≤10*(c+1)*(p+1)*q
  have hterm : (1+4*p)*(c*(word.length+1)^d)≤(1+4*p)*(c*q):=
    Nat.mul_le_mul_left _ htime
  have hcoeff : 7+(1+4*p)*c≤10*(c+1)*(p+1) := by nlinarith [Nat.zero_le (c*p)]
  calc
    7*(I+2)+(1+4*p)*(c*(word.length+1)^d)≤7*q+(1+4*p)*(c*q):=
      Nat.add_le_add (Nat.mul_le_mul_left 7 hbase) hterm
    _ = (7+(1+4*p)*c)*q := by ring
    _ ≤ (10*(c+1)*(p+1))*q := Nat.mul_le_mul_right q hcoeff
    _ = 10*(c+1)*(p+1)*q := by ring

end CurrentAdditive.V40LawBankMap
