import CurrentAdditive.MinimumRatioCallbackLayout
import CurrentAdditive.MinimumRatioWitness
import EthInapproximability.CurrentPaper.MultiMove

set_option maxHeartbeats 700000
noncomputable section
namespace CurrentAdditive.RatioScalarInstall
open Turing EthInapproximability.CurrentPaper BitMachineEncoding MinimumRatioCallbackLayout

def popProgram : Unit → TM2.Stmt (fun _ : Stack => Bool) Unit Unit
  | () => .pop (low 9) (fun _ _ => ()) .halt
def jobs : List (MultiMove.Job Stack) := [⟨low 9,[low 25]⟩]
def moveProgram := MultiMove.program jobs (low 31)
abbrev Label := BitMachineRawSequence.Label Unit (MultiMove.Label 1)
abbrev Control := Unit × MultiMove.Control
def program := BitMachineRawSequence.program popProgram moveProgram
  (MultiMove.startLabel jobs) () MultiMove.initial
def start : Label := BitMachineRawSequence.leftLabel ()
def control : Control := ((),MultiMove.initial)

theorem outputs (S : Bank) (word : List Bool)
    (h9 : S (low 9) = true :: word)
    (h25 : S (low 25) = []) (h31 : S (low 31) = []) :
    ∃ t ≤ 2*word.length+5,
      ((advance program)^[t]) (⟨some start,control,S⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none,control,Function.update (Function.update S (low 9) []) (low 25) word⟩ := by
  have hne (a b : Fin 32) (h : a ≠ b) : low a ≠ low b := by
    intro he; apply h; apply Fin.ext; exact congrArg (fun k : Stack => k.val) he
  let S1 := Function.update S (low 9) word
  have hrA : ((advance popProgram)^[1]) (⟨some (),(),S⟩ :
      TM2.Cfg (fun _ : Stack => Bool) _ _) = ⟨none,(),S1⟩ := by
    simp [advance,popProgram,TM2.step,TM2.stepAux,h9,S1]
  have hvalid : MultiMove.Valid (low 31) jobs := by
    intro j hj
    simp only [jobs,List.mem_singleton] at hj
    subst j
    exact ⟨hne 9 31 (by decide),by simp [hne 31 25 (by decide)],by simp⟩
  have h31S1 : S1 (low 31) = [] := by
    simp [S1,Function.update_of_ne,hne 31 9 (by decide),h31]
  have hrB := MultiMove.run jobs (low 31) hvalid S1 h31S1
  have hcost : MultiMove.cost jobs S1+1=2*word.length+3 := by
    simp [jobs,MultiMove.cost,S1]
  rw [hcost] at hrB
  have hout : MultiMove.apply jobs S1 =
      Function.update (Function.update S (low 9) []) (low 25) word := by
    funext j
    by_cases hj25 : j=low 25
    · subst j
      simp [MultiMove.apply,MultiMove.step,jobs,BitMachineBroadcast.prepend,S1,
        Function.update_of_ne,hne 25 9 (by decide),h25]
    · by_cases hj9 : j=low 9
      · subst j
        simp [MultiMove.apply,MultiMove.step,jobs,BitMachineBroadcast.prepend,S1,
          Function.update_of_ne,hne 9 25 (by decide)]
      · simp [MultiMove.apply,MultiMove.step,jobs,BitMachineBroadcast.prepend,S1,
          Function.update_of_ne,hj25,hj9]
  rw [hout] at hrB
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs popProgram moveProgram ()
    (MultiMove.startLabel jobs) () () MultiMove.initial MultiMove.initial
    S S1 _ 1 (2*word.length+3) hrA hrB
  exact ⟨t,by omega,by simpa only [program,start,control] using hr⟩

theorem installs_minimum (S : Bank) (weights coeff : Array ℚ) (lambda : ℚ)
    (hmin : SequentialCode.minimumRatio weights coeff = some lambda)
    (h9 : S (low 9) = MinimumRatioStepSpec.bestPacket
      (SequentialCode.minimumRatio weights coeff))
    (h25 : S (low 25) = []) (h31 : S (low 31) = []) :
    ∃ j ∈ List.range (min weights.size coeff.size),
      0 < coeff[j]?.getD 0 ∧ lambda = weights[j]?.getD 0 / coeff[j]?.getD 0 ∧
      ∃ t ≤ 2*(CodeDCodec.encodeRawRat (CodeDCanonicalSource.rawOfRat lambda)).length+5,
      ((advance program)^[t]) (⟨some start,control,S⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none,control,Function.update (Function.update S (low 9) []) (low 25)
        (CodeDCodec.encodeRawRat (CodeDCanonicalSource.rawOfRat lambda))⟩ := by
  obtain ⟨j,hj,hpos,hratio⟩ := RationalBitBounds.minimumRatio_attained weights coeff lambda hmin
  refine ⟨j,hj,hpos,hratio,?_⟩
  apply outputs S _ _ h25 h31
  simpa only [hmin,MinimumRatioStepSpec.bestPacket] using h9

#print axioms outputs
#print axioms installs_minimum
end CurrentAdditive.RatioScalarInstall
