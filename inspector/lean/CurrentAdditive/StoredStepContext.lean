import CurrentAdditive.StoredWeightedState
import EthInapproximability.CurrentPaper.BankFieldProjection

namespace CurrentAdditive.StoredStepContext

open Paper2
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineBankCodec
open CurrentAdditive.V39GeneratedConstruction

def activityValue {ni q₂ s : ℕ} (activity : Fin ni → Fin q₂ → Option (Fin s))
    (i : Fin ni) (a : Fin q₂) : ℕ :=
  match activity i a with | some p => p.val | none => s

theorem activityValue_le {ni q₂ s : ℕ} (activity : Fin ni → Fin q₂ → Option (Fin s))
    (i : Fin ni) (a : Fin q₂) : activityValue activity i a ≤ s := by
  unfold activityValue
  split <;> omega

def activityWords {ni q₂ s : ℕ} (activity : Fin ni → Fin q₂ → Option (Fin s)) : List Bool :=
  SourceListEncoding.encode (List.ofFn (fun i : Fin ni =>
    SourceListEncoding.encode (List.ofFn (fun a : Fin q₂ => (activityValue activity i a).bits))))

def context {ni q₂ s : ℕ} (q₁ w Q : ℕ) (μI : PositiveRationalLaw (Fin ni))
    (activity : Fin ni → Fin q₂ → Option (Fin s)) : List Bool :=
  encode ![List.replicate q₁ true,List.replicate q₂ true,List.replicate s true,
    List.replicate w true,List.replicate Q true,StoredWeightedState.lawBytes μI,activityWords activity]

def packet {ni q₂ s : ℕ} (q₁ w Q : ℕ) (μI : PositiveRationalLaw (Fin ni))
    (activity : Fin ni → Fin q₂ → Option (Fin s)) (R : StoredMatrix) : List Bool :=
  encode ![context q₁ w Q μI activity,StoredWeightedState.encode R]

theorem packet_context {ni q₂ s : ℕ} (q₁ w Q : ℕ) (μI : PositiveRationalLaw (Fin ni))
    (activity : Fin ni → Fin q₂ → Option (Fin s)) (R : StoredMatrix) :
    BankFieldProjection.result (0 : Fin 2) (packet q₁ w Q μI activity R)=context q₁ w Q μI activity := by
  simp [packet,BankFieldProjection.result_encode]

theorem packet_state {ni q₂ s : ℕ} (q₁ w Q : ℕ) (μI : PositiveRationalLaw (Fin ni))
    (activity : Fin ni → Fin q₂ → Option (Fin s)) (R : StoredMatrix) :
    BankFieldProjection.result (1 : Fin 2) (packet q₁ w Q μI activity R)=StoredWeightedState.encode R := by
  simp [packet,BankFieldProjection.result_encode]

end CurrentAdditive.StoredStepContext

#print axioms CurrentAdditive.StoredStepContext.activityValue_le
#print axioms CurrentAdditive.StoredStepContext.packet_state
