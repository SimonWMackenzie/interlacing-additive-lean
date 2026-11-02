import CurrentAdditive.V38SourceBridge
import Paper2.YaoT26Size

/-!
Private physical v38 clone source. The external GL occurrence compiler remains
the explicit `G : GLSourceInput t`; the clone machine and its clock are
constructed here from the existing generic fixed machine at multiplier
`K*2^(2^t)`, without changing edge arity K.
-/

namespace CurrentAdditive.V38Machine

open CurrentAdditive.V38Source
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineComposition
open Paper2.YaoCloneMachine Paper2.YaoCloneSource Paper2.YaoSourceCodec
open Paper2.YaoT26Size

set_option maxHeartbeats 1000000

def arity (t : ℕ) : ℕ := 2 ^ t * 2 ^ t
def multiplier (t : ℕ) : ℕ := arity t * colourCount t

noncomputable def sourceMachine {t : ℕ} (G : GLSourceInput t) : BitMachine.Machine :=
  composition G.machine (cloneMachine (arity t) (multiplier t))

def sourceTime {t : ℕ} (G : GLSourceInput t) (input : List Bool) : ℕ :=
  G.time input + 2 * (draftOccEncode (G.output input)).length + 2 +
    cloneTime (arity t) (multiplier t) (G.output input).1
      (G.output input).1 (labelsOf (G.output input))

theorem source_outputs {t : ℕ} (G : GLSourceInput t) (input : List Bool) :
    (sourceMachine G).OutputsWithin input
      (encode (selectedSource G input)) (sourceTime G input) := by
  exact composition_outputsWithin G.machine _ (G.runs input)
    (clone_source_outputsWithin t (colourCount t) (G.output input))

theorem occurrence_length_le {t : ℕ} (G : GLSourceInput t)
    (input : List Bool) :
    (draftOccEncode (G.output input)).length ≤
      input.length + G.time input * G.machine.pushBound :=
  BitMachine.output_length_bound G.machine (G.runs input)

theorem clone_stage_le {t : ℕ} (x : DraftOccSource t) :
    cloneTime (arity t) (multiplier t) x.1 x.1 (labelsOf x) ≤
      cloneConst (arity t) (multiplier t) *
        ((draftOccEncode x).length + 1) ^ 2 := by
  rw [draftOccEncode_eq]
  exact Paper2.YaoT26Size.cloneTime_le _ _ _
    (Paper2.YaoT26Size.labelsOf_le x)

theorem sourceTime_poly {t : ℕ} (G : GLSourceInput t) :
    ∃ c d : ℕ, ∀ input,
      sourceTime G input ≤ c * (input.length + 1) ^ d := by
  obtain ⟨c0, d0, hp⟩ := G.poly
  refine ⟨c0 + 2 * (1 + c0 * G.machine.pushBound) +
      cloneConst (arity t) (multiplier t) *
        (1 + c0 * G.machine.pushBound) ^ 2,
      (d0 + 1) * 2, fun input => ?_⟩
  have hm := occurrence_length_le G input
  have hc := clone_stage_le (G.output input)
  have hT := hp input
  unfold sourceTime
  rw [pow_mul]
  generalize G.machine.pushBound = P0 at hm ⊢
  generalize cloneConst (arity t) (multiplier t) = C at hc ⊢
  generalize (draftOccEncode (G.output input)).length = m at hm hc ⊢
  generalize cloneTime (arity t) (multiplier t) (G.output input).1
    (G.output input).1 (labelsOf (G.output input)) = CT at hc ⊢
  generalize G.time input = T at hm hT ⊢
  generalize input.length = L at hm hT ⊢
  have hB1 : 1 ≤ L + 1 := by omega
  have hBX : L + 1 ≤ (L + 1) ^ (d0 + 1) := Nat.le_self_pow (by omega) _
  have hBd : (L + 1) ^ d0 ≤ (L + 1) ^ (d0 + 1) :=
    Nat.pow_le_pow_right hB1 (by omega)
  have hX1 : 1 ≤ (L + 1) ^ (d0 + 1) := Nat.one_le_pow _ _ (by omega)
  generalize (L + 1) ^ (d0 + 1) = X at hBX hBd hX1 ⊢
  generalize (L + 1) ^ d0 = Y at hT hBd
  have hTX : T ≤ c0 * X := hT.trans (Nat.mul_le_mul_left _ hBd)
  have hm1 : m + 1 ≤ (1 + c0 * P0) * X := by
    have h1 : T * P0 ≤ c0 * X * P0 := Nat.mul_le_mul_right _ hTX
    have h2 : (1 + c0 * P0) * X = X + c0 * X * P0 := by ring
    omega
  have hm2 : (m + 1) ^ 2 ≤ ((1 + c0 * P0) * X) ^ 2 :=
    Nat.pow_le_pow_left hm1 2
  have hXX : X ≤ X ^ 2 := by nlinarith
  generalize 1 + c0 * P0 = k at hm1 hm2 ⊢
  have tc : CT ≤ C * k ^ 2 * X ^ 2 :=
    calc CT ≤ C * (m + 1) ^ 2 := hc
      _ ≤ C * (k * X) ^ 2 := Nat.mul_le_mul_left _ hm2
      _ = C * k ^ 2 * X ^ 2 := by ring
  have tt : T ≤ c0 * X ^ 2 := hTX.trans (Nat.mul_le_mul_left _ hXX)
  have tm : m + 1 ≤ k * X ^ 2 := hm1.trans (Nat.mul_le_mul_left _ hXX)
  nlinarith [tc, tt, tm]

theorem source_polytime {t : ℕ} (G : GLSourceInput t) :
    BitMachine.Polytime (fun input => encode (selectedSource G input)) := by
  obtain ⟨c, d, hclock⟩ := sourceTime_poly G
  exact ⟨sourceMachine G, c, d, fun input =>
    BitMachine.outputsWithin_mono _ (source_outputs G input) (hclock input)⟩

theorem source_encoded_length_poly {t : ℕ} (G : GLSourceInput t) :
    ∃ c d : ℕ, ∀ input,
      (encode (selectedSource G input)).length ≤
        c * (input.length + 1) ^ d := by
  obtain ⟨c, d, hclock⟩ := sourceTime_poly G
  refine ⟨1 + c * (sourceMachine G).pushBound, d + 1, fun input => ?_⟩
  have hl := BitMachine.output_length_bound (sourceMachine G)
    (source_outputs G input)
  have hs := hclock input
  generalize (sourceMachine G).pushBound = p at hl ⊢
  generalize sourceTime G input = T at hl hs
  generalize (encode (selectedSource G input)).length = o at hl
  generalize input.length = L at hl hs ⊢
  have hB : L + 1 ≤ (L + 1) ^ (d + 1) := Nat.le_self_pow (by omega) _
  have hd : (L + 1) ^ d ≤ (L + 1) ^ (d + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : T * p ≤ c * (L + 1) ^ (d + 1) * p :=
    Nat.mul_le_mul_right _ (hs.trans (Nat.mul_le_mul_left _ hd))
  have h3 : (1 + c * p) * (L + 1) ^ (d + 1) =
      (L + 1) ^ (d + 1) + c * (L + 1) ^ (d + 1) * p := by ring
  omega

#print axioms source_outputs
#print axioms sourceTime_poly
#print axioms source_polytime
#print axioms source_encoded_length_poly

end CurrentAdditive.V38Machine
