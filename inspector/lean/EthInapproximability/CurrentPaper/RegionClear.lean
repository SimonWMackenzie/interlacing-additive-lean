import EthInapproximability.CurrentPaper.EntryDispatch

/-!
# Charged clear of a whole embedded finite region, from a length bound

Lane owner:b-stage4-entry-program-4 (Paper B, unit 2, map item 3, segment 3).

For a finite region `ι : Rg ↪ K`, ONE fixed program (cells enumerated by the
fixed classical `Fintype.equivFin Rg`) pops every region cell empty, one
bit per step, then halts. From a per-cell length bound `B` it halts within
`card Rg * B + card Rg + 2` steps on the bank with every region cell blank
and every other cell unchanged. Built on owner-3's checked
`EntryDispatch.clear_bounded` (the admitted `BitMachineClearBank`).
-/

namespace EthInapproximability.CurrentPaper.RegionClear

open Turing BitMachineEncoding

variable {K : Type*} [DecidableEq K]

def prog (n : ℕ) (bank : Fin n → K) (i : Fin (n + 2)) :
    TM2.Stmt (fun _ : K => Bool) (Fin (n + 2)) (Unit × Option Bool) :=
  if h : i.val < n then
    BitMachineClearBank.clearStep (bank ⟨i.val, h⟩) i ⟨i.val + 1, by omega⟩
  else if i.val = n then BitMachineClearBank.finishStep id ⟨n + 1, by omega⟩
  else TM2.Stmt.halt

theorem clear_run (n : ℕ) (bank : Fin n → K) (hinj : Function.Injective bank)
    (S : K → List Bool) (B : ℕ) (hB : ∀ i, (S (bank i)).length ≤ B) :
    ∃ t ≤ n * B + n + 2,
      ((advance (prog n bank))^[t]) ⟨some 0, ((), none), S⟩ =
        ⟨none, ((), none), BitMachineClearBank.cleared bank S⟩ := by
  have hsteps : ∀ i : Fin n, prog n bank (Fin.castSucc (Fin.castSucc i)) =
      BitMachineClearBank.clearStep (bank i) (Fin.castSucc (Fin.castSucc i))
        (Fin.castSucc i.succ) := by
    intro i
    simp only [prog, Fin.val_castSucc, i.isLt, dif_pos]
    rfl
  have hfinish : prog n bank (Fin.castSucc (Fin.last n)) =
      BitMachineClearBank.finishStep id (Fin.last (n + 1)) := by
    simp only [prog, Fin.val_castSucc, Fin.val_last, lt_irrefl, dif_neg, not_false_eq_true,
      if_true]
    rfl
  obtain ⟨t, ht, hr⟩ := EntryDispatch.clear_bounded (prog n bank) id (Fin.last (n + 1)) n bank
    hinj Fin.castSucc hsteps hfinish () S B hB
  refine ⟨t + 1, by omega, ?_⟩
  rw [Function.iterate_succ_apply']
  have h0 : (Fin.castSucc (0 : Fin (n + 1))) = (0 : Fin (n + 2)) := rfl
  rw [h0] at hr
  rw [hr]
  have hh : prog n bank (Fin.last (n + 1)) = TM2.Stmt.halt := by
    simp [prog]
  simp [advance, TM2.step, hh, TM2.stepAux]

/-- The region version: enumerate `Rg` once (fixed classical enumeration). -/
noncomputable def regionBank {Rg : Type*} [Fintype Rg] (ι : Rg ↪ K) :
    Fin (Fintype.card Rg) → K :=
  fun i => ι ((Fintype.equivFin Rg).symm i)

omit [DecidableEq K] in
theorem regionBank_injective {Rg : Type*} [Fintype Rg] (ι : Rg ↪ K) :
    Function.Injective (regionBank ι) := by
  intro a b h
  exact (Fintype.equivFin Rg).symm.injective (ι.injective h)

theorem region_clear {Rg : Type*} [Fintype Rg] (ι : Rg ↪ K)
    (S : K → List Bool) (B : ℕ) (hB : ∀ r, (S (ι r)).length ≤ B) :
    ∃ t ≤ Fintype.card Rg * B + Fintype.card Rg + 2,
      ((advance (prog (Fintype.card Rg) (regionBank ι)))^[t]) ⟨some 0, ((), none), S⟩ =
        ⟨none, ((), none), fun k => if ∃ r, ι r = k then [] else S k⟩ := by
  obtain ⟨t, ht, hr⟩ := clear_run (Fintype.card Rg) (regionBank ι) (regionBank_injective ι) S B
    (fun i => hB _)
  refine ⟨t, ht, hr.trans ?_⟩
  congr 1
  funext k
  simp only [BitMachineClearBank.cleared, regionBank]
  congr 1
  apply propext
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨_, hi⟩
  · rintro ⟨r, hr⟩
    exact ⟨Fintype.equivFin Rg r, by simpa using hr⟩

#print axioms clear_run
#print axioms region_clear

end EthInapproximability.CurrentPaper.RegionClear
