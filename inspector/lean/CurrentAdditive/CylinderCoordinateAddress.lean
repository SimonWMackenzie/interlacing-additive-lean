import EthInapproximability.CurrentPaper.ProtocolBoundedUnary

/-! The inherited literal bounded binary-to-unary machine, specialized to a
feature coordinate inside a q-symbol tuple.  This is the address consumed by
the physical indexed framed-field selector. -/

namespace CurrentAdditive.CylinderCoordinateAddress

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

theorem coordinate_address (q i : Nat) (hi : i < q) :
    ∃ (t : Nat) (c : Turing.TM2.Cfg (fun _ : Fin 4 => Bool)
      ProtocolBoundedUnary.Label ProtocolBoundedUnary.Control),
      t ≤ (q + 1) * (4 * i.bits.length + 5) ∧
      ProtocolBoundedUnary.run t
        (ProtocolBoundedUnary.cfg (some .zeroScan) (none, false)
          i.bits (List.replicate q true) [] []) = c ∧
      c.l = none ∧
      c.stk 3 = true :: List.replicate i true := by
  obtain ⟨t, c, ht, hc, hh, ho⟩ :=
    ProtocolBoundedUnary.bounded_run i.bits (List.replicate q true) []
  refine ⟨t, c, by simpa using ht, hc, hh, ?_⟩
  have hle : i ≤ q := Nat.le_of_lt hi
  simpa [ProtocolBoundedUnary.result,
    EncodedCommunication.bitsValue_bits, Nat.min_eq_left hle, hle] using ho

#print axioms coordinate_address

end CurrentAdditive.CylinderCoordinateAddress
