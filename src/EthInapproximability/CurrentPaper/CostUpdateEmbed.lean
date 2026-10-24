import EthInapproximability.CurrentPaper.CostUpdateMachine

/-! Lane owner:b-weighted-level-6, unit 2, segment 2b, piece 3: the fixed
cost-word update program on ANY global stack `K`, through ANY embedding
`ι : CS ↪ K` whose six input cells alias the cells that already hold the
words (no copy is inserted; the inputs are read in place and restored).

`cost_embedded`: if the global bank `G` shows through `ι` exactly the local
start bank (unary `lam, b, c, s, e, y` at the six input cells, every other
local cell blank), the embedded program halts within the SAME `costBound`
on `Function.update G (ι (cell 5)) (unary costTarget)`: exactly one global cell
changes. Transport by the frozen `WeightedRawWords.region_run`. -/

namespace EthInapproximability.CurrentPaper.CostUpdateEmbed

open Turing BitMachineEncoding BitMachineStackEmbedding CostUpdateStages CostUpdateMachine

noncomputable section

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

theorem st_update (lam b c s e y y' : ℕ) :
    Function.update (st lam b c s e y 0 0 0 0 0 0 0 0 0 0 0 0) 5 y' =
      st lam b c s e y' 0 0 0 0 0 0 0 0 0 0 0 0 := by
  funext k; fin_cases k <;> rfl

theorem st_other (lam b c s e y y' : ℕ) (k : Fin 22) (hk : k ≠ 5) :
    st lam b c s e y' 0 0 0 0 0 0 0 0 0 0 0 0 k = st lam b c s e y 0 0 0 0 0 0 0 0 0 0 0 0 k := by
  rw [← st_update lam b c s e y y']
  exact Function.update_of_ne hk _ _

theorem st_five (lam b c s e y' : ℕ) :
    st lam b c s e y' 0 0 0 0 0 0 0 0 0 0 0 0 5 = y' := rfl

/-- The embedded cost program on a global stack. -/
def costOn {K : Type} [DecidableEq K] (ι : CS ↪ K) :=
  fun l => stackStmt ι (costProgram l)

/-- The exit bank, pointwise. -/
theorem final_bank {K : Type} [DecidableEq K] (ι : CS ↪ K) (G : K → List Bool)
    (lam b c s e y : ℕ)
    (hG : ∀ x, G (ι x) = U (st lam b c s e y 0 0 0 0 0 0 0 0 0 0 0 0) x) :
    bank ι G (U (st lam b c s e (costTarget lam b c s e y) 0 0 0 0 0 0 0 0 0 0 0 0)) =
      Function.update G (ι (cell 5)) (List.replicate (costTarget lam b c s e y) true) := by
  funext x
  by_cases hx : ∃ k, ι k = x
  · obtain ⟨k, rfl⟩ := hx
    rw [bank_at]
    by_cases hk : k = cell 5
    · subst hk
      rw [Function.update_self, U_cell, st_five]
    · rw [Function.update_of_ne (fun e => hk (ι.injective e)), hG k]
      rcases k with j | j
      · have hj : j ≠ 5 := fun e => hk (by rw [e])
        rw [U_cell, U_cell, st_other lam b c s e y _ j hj]
      · rw [U_log, U_log]
  · rw [bank_outside _ _ _ _ hx, Function.update_of_ne (fun e => hx ⟨cell 5, e.symm⟩)]

#print axioms final_bank

theorem cost_embedded {K : Type} [DecidableEq K] (ι : CS ↪ K) (G : K → List Bool)
    (lam b c s e y : ℕ)
    (hG : ∀ x, G (ι x) = U (st lam b c s e y 0 0 0 0 0 0 0 0 0 0 0 0) x) :
    ∃ t ≤ costBound lam b c s e y,
      ((advance (costOn ι))^[t])
          (⟨some costStart, costCtrl, G⟩ : TM2.Cfg (fun _ : K => Bool) _ _) =
        ⟨none, costCtrl,
          Function.update G (ι (cell 5)) (List.replicate (costTarget lam b c s e y) true)⟩ := by
  obtain ⟨t, ht, r⟩ := cost_run lam b c s e y
  have h := WeightedRawWords.region_run ι costProgram
    ⟨some costStart, costCtrl, U (st lam b c s e y 0 0 0 0 0 0 0 0 0 0 0 0)⟩
    ⟨none, costCtrl, U (st lam b c s e (costTarget lam b c s e y) 0 0 0 0 0 0 0 0 0 0 0 0)⟩
    t r G (fun k => (hG k).symm)
  dsimp only at h
  rw [final_bank ι G lam b c s e y hG] at h
  exact ⟨t, ht, h⟩

#print axioms cost_embedded

end
end EthInapproximability.CurrentPaper.CostUpdateEmbed
