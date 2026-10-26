import EthInapproximability.CurrentPaper.MatrixStage4FamilyData
import EthInapproximability.CurrentPaper.MatrixAddressMachine

/-!
# Physical family-field row and bit-start addresses

Each theorem is a separate run of the fixed address machine. Feeding the
first unary output into the second run requires a charged bank transfer in
a future combined controller; these are not presented as a composed run.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4FamilyAddress

open MatrixMaterialization MatrixAddressMachine

theorem family_pair_address {L q : ℕ} (ℓ : Fin L) (α : Fin q) :
    run (exactTime ℓ.val q α.val)
      (cfg (some .outer) false (List.replicate ℓ.val true)
        (List.replicate q true) (List.replicate α.val true) [] [] []) =
    cfg none false (List.replicate ℓ.val true)
      (List.replicate q true) (List.replicate α.val true) [] []
      (List.replicate (finProdFinEquiv (ℓ,α)).val true) := by
  have hval : (finProdFinEquiv (ℓ,α)).val = ℓ.val*q+α.val := by
    simp only [finProdFinEquiv_apply_val]
    ring
  simpa only [hval, List.append_nil] using
    address_run ℓ.val q α.val false []

theorem family_field_start {L q : ℕ} (ℓ : Fin L) (α : Fin q)
    (fieldWidth : ℕ) :
    let row := (finProdFinEquiv (ℓ,α)).val
    run (exactTime row fieldWidth 0)
      (cfg (some .outer) false (List.replicate row true)
        (List.replicate fieldWidth true) [] [] [] []) =
    cfg none false (List.replicate row true)
      (List.replicate fieldWidth true) [] [] []
      (List.replicate (row*fieldWidth) true) := by
  dsimp
  simpa only [Nat.add_zero, List.append_nil] using
    address_run (finProdFinEquiv (ℓ,α)).val fieldWidth 0 false []

end EthInapproximability.CurrentPaper.MatrixStage4FamilyAddress
