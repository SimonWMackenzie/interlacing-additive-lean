import CurrentAdditive.QuarticFaithfulSelectedLiteral

/-! Codec and announced public fields for the private faithful selector. -/

namespace Paper2.GenericQuarticFaithful

open Paper2.CurrentAdditive.QuarticConstructor
open EthInapproximability.CurrentPaper
open Workspace.Types.CommComplexity

theorem selected_public_fields_eq_old {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ) :
    (select27Faithful hn edge Δ γ k).rows = (select27 hn edge Δ γ k).rows ∧
    (select27Faithful hn edge Δ γ k).cols = (select27 hn edge Δ γ k).cols ∧
    (select27Faithful hn edge Δ γ k).budget = (select27 hn edge Δ γ k).budget ∧
    (select27Faithful hn edge Δ γ k).inputBits =
      (select27 hn edge Δ γ k).inputBits := by
  by_cases hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ
  · rw [select27Faithful_good hn edge Δ γ k hc,
      select27_good hn edge Δ γ k hc]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rw [select27Faithful_bad hn edge Δ γ k hc,
      select27_bad hn edge Δ γ k hc]
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem select27Faithful_dimensions_pos {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ) :
    0 < (select27Faithful hn edge Δ γ k).rows ∧
    0 < (select27Faithful hn edge Δ γ k).cols := by
  have h := selected_public_fields_eq_old hn edge Δ γ k
  rw [h.1, h.2.1]
  exact select27_dimensions_pos hn edge Δ γ k

def selectedInstance27Faithful {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (t : (select27Faithful hn edge Δ γ k).Tape) :
    EncodedCommunication.Instance :=
  EncodedSelectedOutput.instanceOf ((select27Faithful hn edge Δ γ k).table t)
    (select27Faithful hn edge Δ γ k).budget

theorem outputBits27Faithful_decode {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (t : (select27Faithful hn edge Δ γ k).Tape) :
    EncodedCommunication.decodeInstance
      (outputBits27Faithful hn edge Δ γ k t) =
      some (selectedInstance27Faithful hn edge Δ γ k t) := by
  have hp := select27Faithful_dimensions_pos hn edge Δ γ k
  exact EncodedCommunication.decode_encode _
    (EncodedSelectedOutput.instanceOf_valid _ _ hp.1 hp.2)

#print axioms selected_public_fields_eq_old
#print axioms outputBits27Faithful_decode

end Paper2.GenericQuarticFaithful
