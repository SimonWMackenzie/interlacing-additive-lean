import CurrentAdditive.GaussCellSourceBridge

/-! The exact unary words needed for swap-on-access source rows. -/

namespace CurrentAdditive.GaussSwapIndexSpec

theorem sourceRow_current {m : Nat} (r pivot : Fin m) :
    GaussCellSourceBridge.sourceRow r pivot r = pivot := by
  simp [GaussCellSourceBridge.sourceRow]

theorem sourceRow_target {m : Nat} (r pivot i : Fin m) :
    GaussCellSourceBridge.sourceRow r pivot i =
      if i = r then pivot else if i = pivot then r else i := by
  simp [GaussCellSourceBridge.sourceRow, Equiv.swap_apply_def]

#print axioms sourceRow_current
#print axioms sourceRow_target

end CurrentAdditive.GaussSwapIndexSpec
