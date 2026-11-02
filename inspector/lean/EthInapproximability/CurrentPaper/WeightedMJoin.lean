import EthInapproximability.CurrentPaper.WeightedMMultiply
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-! One fixed four-phase controller from writer a,rx to the exact threshold
input m=qOne(a)*rx. The private qOne word and all arithmetic work are blank
again at halt. -/

namespace EthInapproximability.CurrentPaper.WeightedMJoin

open Turing BitMachineEncoding
noncomputable section

abbrev Stack := WeightedMWidth.Stack

def P12 := BitMachineRawSequence.program
  WeightedMWidth.powerProgram WeightedMWidth.popProgram ()
  (((false,false),none) : MatrixUnaryPower.Control) ()
def P123 := BitMachineRawSequence.program
  P12 WeightedMMultiply.multiplyProgram MatrixAddressMachine.Label.outer
  ((((false,false),none),()) : MatrixUnaryPower.Control × Unit) false
def program := BitMachineRawSequence.program
  P123 WeightedMMultiply.clearProgram WeightedMMultiply.ClearLabel.loop
  (((((false,false),none),()),false) :
    (MatrixUnaryPower.Control × Unit) × Bool)
  ((),none)

def initial := ((((((false,false),none),()),false),((),none)) :
  ((MatrixUnaryPower.Control × Unit) × Bool) × (Unit × Option Bool))

def cost (a rx : ℕ) : ℕ :=
  (4*2^a + 5*a + 7) + 1 +
  MatrixAddressMachine.exactTime (Construction.qOne a) rx 0 +
  (Construction.qOne a + 2) + 3

theorem run (S : Stack → List Bool) (a rx : ℕ)
    (ha : S (WeightedMWidth.writer 54) = List.replicate a true)
    (hrx : S (WeightedMWidth.writer 17) = List.replicate rx true)
    (h2 : S (WeightedMWidth.scalar 2) = [])
    (h3 : S WeightedMWidth.width = [])
    (h4 : S (WeightedMWidth.scalar 4) = [])
    (h5 : S (WeightedMWidth.scalar 5) = [])
    (h6 : S (WeightedMWidth.scalar 6) = []) :
    ∃ t ≤ cost a rx,
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (Sum.inr false)))),initial,S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,initial,Function.update S (WeightedMWidth.scalar 2)
          (List.replicate (Construction.qOne a * rx) true)⟩ := by
  let U := List.replicate (Construction.qOne a) true
  let S1 := Function.update S WeightedMWidth.width
    (List.replicate (2^a) true)
  let S2 := Function.update S WeightedMWidth.width U
  let S3 := Function.update S2 (WeightedMWidth.scalar 2)
    (List.replicate (Construction.qOne a * rx) true)
  obtain ⟨tp,htp,hpower⟩ := WeightedMWidth.power_run S a ha h3 h4 h5
  have hword : S1 WeightedMWidth.width = List.replicate (2^a) true := by
    simp [S1]
  have hpop : advance WeightedMWidth.popProgram
      (⟨some (),(),S1⟩ : TM2.Cfg (fun _ : Stack => Bool) Unit Unit) =
      ⟨none,(),S2⟩ := by
    have h := WeightedMWidth.pop_run S1 a hword
    simpa [S1,S2,U] using h
  have hm2 : S2 WeightedMWidth.width = U := by simp [S2]
  have hrx2 : S2 (WeightedMWidth.writer 17) =
      List.replicate rx true := by
    simpa [S2,WeightedMWidth.width,WeightedMWidth.scalar,
      WeightedMWidth.writer] using hrx
  have h42 : S2 (WeightedMWidth.scalar 4) = [] := by
    simpa [S2,WeightedMWidth.width,WeightedMWidth.scalar] using h4
  have h52 : S2 (WeightedMWidth.scalar 5) = [] := by
    simpa [S2,WeightedMWidth.width,WeightedMWidth.scalar] using h5
  have h62 : S2 (WeightedMWidth.scalar 6) = [] := by
    simpa [S2,WeightedMWidth.width,WeightedMWidth.scalar] using h6
  have hm : S2 (WeightedMWidth.scalar 2) = [] := by
    simpa [S2,WeightedMWidth.width,WeightedMWidth.scalar] using h2
  have hmul := WeightedMMultiply.multiply_run S2 a rx hm2 hrx2
    h42 h52 h62 hm
  have hclearword : S3 WeightedMWidth.width = U := by
    simp [S3,S2,U,WeightedMWidth.width,WeightedMWidth.scalar]
  have hclean : Function.update S3 WeightedMWidth.width [] =
      Function.update S (WeightedMWidth.scalar 2)
        (List.replicate (Construction.qOne a * rx) true) := by
    funext k
    by_cases hk2 : k = WeightedMWidth.scalar 2
    · subst k; simp [S3,S2,WeightedMWidth.width,WeightedMWidth.scalar]
    · by_cases hk3 : k = WeightedMWidth.width
      · subst k
        rw [Function.update_self,
          Function.update_of_ne (by decide :
            WeightedMWidth.width ≠ WeightedMWidth.scalar 2)]
        exact h3.symm
      · simp [S3,S2,Function.update_of_ne hk2,
          Function.update_of_ne hk3]
  have hclear := WeightedMMultiply.clear_run S3
  rw [show WeightedMMultiply.clearCost S3 =
    Construction.qOne a + 2 by simp [WeightedMMultiply.clearCost,hclearword,
      U]] at hclear
  rw [hclean] at hclear
  obtain ⟨t12,ht12,hr12⟩ := BitMachineRawSequence.runs
    WeightedMWidth.powerProgram WeightedMWidth.popProgram
    (.inr false) ()
    (((false,false),none) : MatrixUnaryPower.Control)
    (((false,false),none) : MatrixUnaryPower.Control)
    () () S S1 S2 tp 1 hpower hpop
  obtain ⟨t123,ht123,hr123⟩ := BitMachineRawSequence.runs
    P12 WeightedMMultiply.multiplyProgram
    (BitMachineRawSequence.leftLabel (Sum.inr false))
    MatrixAddressMachine.Label.outer
    ((((false,false),none),()) : MatrixUnaryPower.Control × Unit)
    ((((false,false),none),()) : MatrixUnaryPower.Control × Unit)
    false false S S2 S3 t12
    (MatrixAddressMachine.exactTime (Construction.qOne a) rx 0)
    (by simpa only [P12,S1,S2] using hr12)
    (by simpa only [S3] using hmul)
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    P123 WeightedMMultiply.clearProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (Sum.inr false)))
    WeightedMMultiply.ClearLabel.loop
    (((((false,false),none),()),false) :
      (MatrixUnaryPower.Control × Unit) × Bool)
    (((((false,false),none),()),false) :
      (MatrixUnaryPower.Control × Unit) × Bool)
    ((),none) ((),none)
    S S3 (Function.update S (WeightedMWidth.scalar 2)
      (List.replicate (Construction.qOne a * rx) true))
    t123 (Construction.qOne a + 2)
    (by simpa only [P123] using hr123) hclear
  refine ⟨t,?_,?_⟩
  · dsimp [cost]; omega
  · simpa only [program,initial] using hr

#print axioms run

end
end EthInapproximability.CurrentPaper.WeightedMJoin
