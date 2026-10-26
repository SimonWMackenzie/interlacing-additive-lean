import CurrentAdditive.FeatureOldDescriptorTraversal96
import CurrentAdditive.CylinderOrderedSpec

/-! Exact ordered descriptor and unary-count interpretation of one complete
old-list scan. Repeated old descriptors and alphabet positions are retained. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace CurrentAdditive.FeatureOldDescriptorSemantics96
open EthInapproximability.CurrentPaper
open CurrentAdditive.FeatureOldDescriptorFrame96
open CurrentAdditive.Wide96ContextListScheduler

def next (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat))) :=
  CylinderOrderedSpec.extendList 8192 j ys cs

theorem fields_append (xs ys : List (List Bool)) :
    SourceListEncoding.fields (xs++ys)=
      SourceListEncoding.fields xs++SourceListEncoding.fields ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [SourceListEncoding.fields,ih,List.append_assoc]

theorem joined_extensions (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat))) :
    joined (piece j ys) (words cs)=
      SourceListEncoding.fields
        (words ((cs.filter (fun c => c.length<8192)).flatMap
          (fun c => ys.map (fun y => (j,y)::c)))) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [words,joined] at ih
    by_cases hc : c.length<8192
    · simpa [words,joined,piece,hc,FeatureEligibleDescriptor96.extensions,
        fields_append,List.map_append,List.map_map,List.flatMap_cons,Function.comp_def] using
        congrArg (fun tail => SourceListEncoding.fields
          (ys.map (fun y => CylinderFeatureCodec.encodeFeature ((j,y)::c)))++tail) ih
    · simpa [words,joined,piece,hc,List.flatMap_cons] using ih

theorem body_exact (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat))) :
    SourceListEncoding.fields (words cs)++joined (piece j ys) (words cs)=
      SourceListEncoding.fields (words (next j ys cs)) := by
  rw [joined_extensions,← fields_append]
  congr 1
  simp [words,next,CylinderOrderedSpec.extendList]

theorem context_cons (n : Nat) (ys : List Nat) (c : List (Nat × Nat))
    (cs : List (List (Nat × Nat))) :
    context (List.replicate n true) ys (words (c::cs))=
      context (countStep ys (List.replicate n true) (CylinderFeatureCodec.encodeFeature c))
        ys (words cs) := rfl

theorem count_exact (n : Nat) (ys : List Nat) (cs : List (List (Nat × Nat))) :
    context (List.replicate n true) ys (words cs)=
      List.replicate (n+ys.length*(cs.filter (fun c => c.length<8192)).length) true := by
  induction cs generalizing n with
  | nil => simp [context,words]
  | cons c cs ih =>
    rw [context_cons]
    by_cases hc : c.length<8192
    · have hstep : countStep ys (List.replicate n true)
          (CylinderFeatureCodec.encodeFeature c)=List.replicate (ys.length+n) true := by
        simp [countStep,eligible,hc]
      rw [hstep,ih]
      simp only [List.filter_cons,decide_true,hc,ite_true,List.length_cons]
      congr 1
      simp [Nat.mul_add]
      omega
    · have hstep : countStep ys (List.replicate n true)
          (CylinderFeatureCodec.encodeFeature c)=List.replicate n true := by
        simp [countStep,eligible,hc]
      rw [hstep,ih]
      simp [hc]

theorem next_length (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat))) :
    (next j ys cs).length=cs.length+ys.length*(cs.filter (fun c => c.length<8192)).length := by
  simp [next,CylinderOrderedSpec.extendList,List.length_flatMap,List.sum_map_mul_left,
    Nat.mul_comm]

theorem count_next (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat))) :
    context (List.replicate cs.length true) ys (words cs)=
      List.replicate (next j ys cs).length true := by
  rw [count_exact,next_length]

#print axioms body_exact
#print axioms count_next
end CurrentAdditive.FeatureOldDescriptorSemantics96
