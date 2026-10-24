import CurrentAdditive.GenericFeatureOldDescriptorFrame
import CurrentAdditive.FeatureOldDescriptorSemantics96

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace CurrentAdditive.GenericFeatureOldDescriptorSemantics
open EthInapproximability.CurrentPaper
open GenericFeatureOldDescriptorFrame
open CurrentAdditive.Wide96ContextListScheduler

export FeatureOldDescriptorSemantics96 (fields_append)

def next (D j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat))) :=
  CylinderOrderedSpec.extendList D j ys cs

theorem joined_extensions (D j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat))) :
    joined (piece D j ys) (words cs) =
      SourceListEncoding.fields (words ((cs.filter (fun c => c.length < D)).flatMap
        (fun c => ys.map (fun y => (j,y) :: c)))) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [words, joined] at ih
    by_cases hc : c.length < D
    · simpa [words, joined, piece, hc, GenericFeatureEligibleDescriptor.extensions,
        fields_append, List.map_append, List.map_map, List.flatMap_cons, Function.comp_def] using
        congrArg (fun tail => SourceListEncoding.fields
          (ys.map (fun y => CylinderFeatureCodec.encodeFeature ((j,y) :: c))) ++ tail) ih
    · simpa [words, joined, piece, hc, List.flatMap_cons] using ih

theorem body_exact (D j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat))) :
    SourceListEncoding.fields (words cs) ++ joined (piece D j ys) (words cs) =
      SourceListEncoding.fields (words (next D j ys cs)) := by
  rw [joined_extensions, ←fields_append]
  congr 1
  simp [words, next, CylinderOrderedSpec.extendList]

theorem context_cons (D n : Nat) (ys : List Nat) (c : List (Nat × Nat))
    (cs : List (List (Nat × Nat))) :
    context D (List.replicate n true) ys (words (c :: cs)) =
      context D (countStep D ys (List.replicate n true) (CylinderFeatureCodec.encodeFeature c))
        ys (words cs) := rfl

theorem count_exact (D n : Nat) (ys : List Nat) (cs : List (List (Nat × Nat))) :
    context D (List.replicate n true) ys (words cs) =
      List.replicate (n + ys.length * (cs.filter (fun c => c.length < D)).length) true := by
  induction cs generalizing n with
  | nil => simp [context, words]
  | cons c cs ih =>
    rw [context_cons]
    by_cases hc : c.length < D
    · have hstep : countStep D ys (List.replicate n true)
          (CylinderFeatureCodec.encodeFeature c) = List.replicate (ys.length + n) true := by
        simp [countStep, eligible, hc]
      rw [hstep, ih]
      simp only [List.filter_cons, decide_true, hc, ite_true, List.length_cons]
      congr 1
      simp [Nat.mul_add]
      omega
    · have hstep : countStep D ys (List.replicate n true)
          (CylinderFeatureCodec.encodeFeature c) = List.replicate n true := by
        simp [countStep, eligible, hc]
      rw [hstep, ih]
      simp [hc]

theorem next_length (D j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat))) :
    (next D j ys cs).length = cs.length + ys.length * (cs.filter (fun c => c.length < D)).length := by
  simp [next, CylinderOrderedSpec.extendList, List.length_flatMap, List.sum_map_mul_left,
    Nat.mul_comm]

theorem count_next (D j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat))) :
    context D (List.replicate cs.length true) ys (words cs) =
      List.replicate (next D j ys cs).length true := by
  rw [count_exact, next_length]

#print axioms body_exact
#print axioms count_next
end CurrentAdditive.GenericFeatureOldDescriptorSemantics
