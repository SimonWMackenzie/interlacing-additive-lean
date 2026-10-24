import CurrentAdditive.QuarticEncodedOutput

/-! Transport a literal fair-bit tape through the public v27 selector's
good-branch equality. This identifies the same serialized table object used
by `selectedInstance27`, not just an isomorphic matrix. -/

namespace Paper2.GenericQuarticGoodTransport

open Paper2.CurrentAdditive.QuarticConstructor
open EthInapproximability.CurrentPaper

private theorem table_bits_transport
    {a b : TotalFiniteConstructorScratch.SelectedOutput}
    (h : a = b) (t : b.Tape) :
    (a.table (h.symm ▸ t)).bits = (b.table t).bits := by
  cases h
  rfl

private theorem output_bits_transport
    {a b : TotalFiniteConstructorScratch.SelectedOutput}
    (h : a = b) (t : b.Tape) :
    EncodedCommunication.encodeInstance
      (EncodedSelectedOutput.instanceOf (a.table (h.symm ▸ t)) a.budget) =
    EncodedCommunication.encodeInstance
      (EncodedSelectedOutput.instanceOf (b.table t) b.budget) := by
  cases h
  rfl

def selectedTape {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ)
    (bits : (scheduledOutput27 hn edge Δ γ k hc).Tape) :
    (select27 hn edge Δ γ k).Tape :=
  (select27_good hn edge Δ γ k hc).symm ▸ bits

theorem selected_good_table_bits {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ)
    (bits : (scheduledOutput27 hn edge Δ γ k hc).Tape) :
    ((select27 hn edge Δ γ k).table
      (selectedTape hn edge Δ γ k hc bits)).bits =
      (scheduledTable27 hn edge (Nat.clog 2 n) Δ γ k hc bits).bits := by
  exact table_bits_transport (select27_good hn edge Δ γ k hc) bits

#print axioms selected_good_table_bits

theorem selected_good_output_bits {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ)
    (bits : (scheduledOutput27 hn edge Δ γ k hc).Tape) :
    outputBits27 hn edge Δ γ k
      (selectedTape hn edge Δ γ k hc bits) =
      EncodedCommunication.encodeInstance
        (EncodedSelectedOutput.instanceOf
          (scheduledTable27 hn edge (Nat.clog 2 n) Δ γ k hc bits)
          (scheduledOutput27 hn edge Δ γ k hc).budget) := by
  exact output_bits_transport (select27_good hn edge Δ γ k hc) bits

#print axioms selected_good_output_bits

end Paper2.GenericQuarticGoodTransport
