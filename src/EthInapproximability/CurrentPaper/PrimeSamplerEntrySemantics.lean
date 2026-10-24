import EthInapproximability.CurrentPaper.PrimeSamplerDigits
import EthInapproximability.CurrentPaper.PrimeSamplerHornerMachine

/-!
# Agreement of the physical digit stream and the indexed family

Source: frozen v8 `B-effectivity-details.tex`, the explicit balanced-family
accessor. These identities bind the two physical stages to the original
prime-family index, including every leading zero coefficient.
-/

namespace EthInapproximability.CurrentPaper.PrimeSamplerEntrySemantics

open PrimeSamplerEntryAlgorithm

theorem digits_eq_encode (p t l : ℕ) (old : List Bool) :
    PrimeSamplerDigits.digits p t l old =
      PrimeSamplerHornerMachine.encode (coefficients p t l) ++ old := by
  induction t generalizing l old with
  | zero => rfl
  | succ t ih =>
      simp [PrimeSamplerDigits.digits, coefficients, ih,
        PrimeSamplerHornerMachine.encode, PrimeSamplerHornerMachine.encodeDigit, List.append_assoc]

theorem encode_length_le (p : ℕ) (as : List ℕ) (h : ∀ a ∈ as,a<p) :
    (PrimeSamplerHornerMachine.encode as).length ≤ as.length*p := by
  induction as with
  | nil => simp [PrimeSamplerHornerMachine.encode]
  | cons a as ih =>
      have ha := h a (by simp)
      have ht := ih (fun a ha => h a (by simp [ha]))
      simp only [PrimeSamplerHornerMachine.encode, List.flatMap_cons, List.length_append,
        PrimeSamplerHornerMachine.encodeDigit,List.length_replicate,List.length_cons,List.length_nil]
      change a+1+(PrimeSamplerHornerMachine.encode as).length ≤ (as.length+1)*p
      nlinarith

theorem digit_stream_length (p t l : ℕ) (hp : 0<p) :
    (PrimeSamplerDigits.digits p t l []).length ≤ t*p := by
  rw [digits_eq_encode,List.append_nil]
  simpa only [coefficients_length] using
    encode_length_le p (coefficients p t l) (coefficients_lt p t l hp)

theorem evaluated_entry (p t m l j : ℕ) :
    evaluate p j (coefficients p t l) 0 % m=PrimeSampler.entry p t m l j := by
  rw [evaluate_coefficients]
  exact entry_eq p t m l j

end EthInapproximability.CurrentPaper.PrimeSamplerEntrySemantics
