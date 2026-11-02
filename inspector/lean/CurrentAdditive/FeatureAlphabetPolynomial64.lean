import CurrentAdditive.FeatureAlphabetItemClock64

set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 100
noncomputable section
namespace CurrentAdditive.FeatureAlphabetPolynomial64
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CylinderFeatureCodec FeatureInnerAlphabetRun64 FeatureBoundedAlphabet64
open GaussListContext Wide64ContextListScheduler FeatureAlphabetClockBounds64
open FeatureAlphabetItemClock64

theorem cycle_arithmetic (g T L getter time cleanup : Nat)
    (hg : getter ≤ 50*(L+1)^3) (ht : time ≤ T)
    (hc : cleanup ≤ 10*(L+g*T)) :
    getter+(time+1)+1+(cleanup+11)+1 ≤
      50*(L+1)^3+(1+10*g)*T+10*L+14 := by
  nlinarith

local notation "callbackStart" => BitMachineRawSequence.leftLabel
  (BitMachineRawSequence.leftLabel FeaturePairRaw64.start)
local notation "callbackControl" => ((FeaturePairRaw64.control,(((),none),
  (V2ItemFrameCore.control V2FeatureFrameLayout64.slots,((),none)))),((),none))

def cycleAt (n a g : Nat) :=
  50*(n+1)^3+(1+10*g)*(a*(64*(n+1)+1)^4)+10*n+14

def coefficientAt (a g : Nat) := 50+(1+10*g)*a*65^4+25

def cycleCap (n : Nat) := cycleAt n FeatureExtensionPolynomial64.coefficient growth

theorem cycleBudget_le (j : Nat) (c : List (Nat × Nat)) (ys : List Nat)
    (body : List Bool) (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (hsplit : pre++word::suffix=original ys) :
    SourceContextScheduler64.cycleBudget FeatureExtensionCompose64.cleanedProgram
      callbackStart callbackControl (piece j c) body j.bits (original ys)
      (contract j c ys body) pre word suffix ≤ cycleCap (inputSize j c ys body) := by
  let L := inputSize j c ys body
  have htime := (contract_time_le j c ys body pre word suffix hsplit).trans
    (itemClock_le j c ys body pre word suffix hsplit)
  have hg : getterBudget pre word suffix ≤ 50*(L+1)^3 := by
    have h := StatefulListScheduler.getterBudget_cubic pre word suffix
    change getterBudget pre word suffix ≤ 50*((SourceListEncoding.encode
      (pre++word::suffix)).length+1)^3 at h
    rw [hsplit] at h
    apply h.trans
    dsimp only [L,inputSize]
    gcongr <;> omega
  have hsum : (∑ i : Fin 10,((contract j c ys body).state pre word suffix
      (cleanBank i)).length) ≤ 10*(L+growth*itemCap L) := by
    have h := Finset.sum_le_sum (s:=Finset.univ)
      (fun i _ => state_length_le j c ys body pre word suffix hsplit (cleanBank i))
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] using h
  dsimp only [SourceContextScheduler64.cycleBudget,cycleCap,cycleAt]
  exact cycle_arithmetic growth (itemCap L) L _ _ _ hg htime hsum

def coefficient := coefficientAt FeatureExtensionPolynomial64.coefficient growth

theorem scalar_cap_le (n a g : Nat) :
    cycleAt n a g+1 ≤ coefficientAt a g*(n+1)^4 := by
  let M := n+1
  have hM : 1 ≤ M := by dsimp [M]; omega
  have h34 : M^3 ≤ M^4 := by
    have h := Nat.mul_le_mul_left (M^3) hM
    simpa only [Nat.mul_one,pow_succ] using h
  have h14 : M ≤ M^4 := le_self_pow hM (by decide)
  have hN : 64*M+1 ≤ 65*M := by omega
  have hN4 := Nat.pow_le_pow_left hN 4
  rw [show (65*M)^4=65^4*M^4 by ring] at hN4
  have ht := Nat.mul_le_mul_left ((1+10*g)*a) hN4
  have h50 := Nat.mul_le_mul_left 50 h34
  have h25 := Nat.mul_le_mul_left 25 h14
  dsimp only [M] at *
  unfold cycleAt coefficientAt
  nlinarith

theorem cycleCap_le (n : Nat) : cycleCap n+1 ≤ coefficient*(n+1)^4 :=
  scalar_cap_le n FeatureExtensionPolynomial64.coefficient growth

theorem mul_four_five (n C : Nat) : (n+1)*(C*(n+1)^4)=C*(n+1)^5 := by ring

/-- A fixed degree-five polynomial bounds the actual summed reachable-split
budget of the physical alphabet scan. The descriptor, alphabet, coordinate,
body, and literal extension-output byte lengths are all charged. -/
theorem scanClock_le (j : Nat) (c : List (Nat × Nat)) (ys : List Nat) (body : List Bool) :
    FeatureBoundedLift96.scanClock j c ys body ≤
      coefficient*(inputSize j c ys body+1)^5 := by
  let L := inputSize j c ys body
  have h := SourceContextScheduler64.remainingBudget_fixed_input
    FeatureExtensionCompose64.cleanedProgram callbackStart callbackControl
    (piece j c) body j.bits (original ys) (contract j c ys body)
    (cycleCap L) (fun a word b hab => cycleBudget_le j c ys body a word b hab)
    [] (original ys) (by simp)
  change FeatureBoundedLift96.scanClock j c ys body ≤
    ((original ys).length+1)*(cycleCap L+1) at h
  have hm := CylinderRawInputProjection.input_measure_le (original ys)
  unfold CylinderProductionProjectionClock.inputMeasure at hm
  have hcount : (original ys).length+1 ≤ L+1 := by dsimp [L,inputSize]; omega
  exact h.trans ((Nat.mul_le_mul hcount (cycleCap_le L)).trans
    (le_of_eq (mul_four_five L coefficient)))

theorem uniform_scanClock : ∃ C d : Nat,
    ∀ (j : Nat) (c : List (Nat × Nat)) (ys : List Nat) (body : List Bool),
      FeatureBoundedLift96.scanClock j c ys body ≤ C*(inputSize j c ys body+1)^d :=
  ⟨coefficient,5,scanClock_le⟩

#print axioms cycleBudget_le
#print axioms scanClock_le
#print axioms uniform_scanClock
end CurrentAdditive.FeatureAlphabetPolynomial64
