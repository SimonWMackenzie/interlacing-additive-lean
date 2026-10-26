import CurrentAdditive.GenericFeatureGuardedDescriptor
import CurrentAdditive.FeatureOldDescriptorFrame96

noncomputable section
set_option autoImplicit false
namespace CurrentAdditive.GenericFeatureOldDescriptorFrame
open EthInapproximability.CurrentPaper

/- The physical selected-word frame and all extra banks do not depend on
depth. Their exact old definitions, rather than copies of their layouts,
remain the generic ABI. -/
export FeatureOldDescriptorFrame96 (words extra selected selected_extra selected_banks)

def eligible (D : Nat) (word : List Bool) : Bool :=
  match CylinderFeatureCodec.decodeFeature word with
  | none => false
  | some c => decide (c.length < D)

def piece (D j : Nat) (ys : List Nat) (word : List Bool) : List Bool :=
  match CylinderFeatureCodec.decodeFeature word with
  | none => []
  | some c => if c.length < D then GenericFeatureEligibleDescriptor.extensions j c ys else []

def countStep (D : Nat) (ys : List Nat) (count word : List Bool) : List Bool :=
  if eligible D word then List.replicate ys.length true ++ count else count

def context (D : Nat) (count : List Bool) (ys : List Nat) (pre : List (List Bool)) : List Bool :=
  pre.foldl (countStep D ys) count

theorem context_step (D : Nat) (count : List Bool) (ys : List Nat)
    (pre : List (List Bool)) (word : List Bool) :
    context D count ys (pre ++ [word]) = countStep D ys (context D count ys pre) word := by
  simp [context, List.foldl_append]

end CurrentAdditive.GenericFeatureOldDescriptorFrame
