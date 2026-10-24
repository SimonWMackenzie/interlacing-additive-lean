import Paper2.A3Wrap

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 8192

namespace CurrentAdditive.V39ThreePortFrame
noncomputable section
open Paper2
open EthInapproximability.CurrentPaper

variable {S : Type} [Fintype S] [DecidableEq S]
  (g k t : S) (hgk : g ≠ k) (hgt : g ≠ t) (hkt : k ≠ t)

abbrev Work := {j : S // j ≠ g ∧ j ≠ k ∧ j ≠ t}

def split (j : S) : Work g k t ⊕ Fin 3 :=
  if h0 : j=g then .inr 0 else
  if h1 : j=k then .inr 1 else
  if h2 : j=t then .inr 2 else .inl ⟨j,h0,h1,h2⟩

def unsplit : Work g k t ⊕ Fin 3 → S := Sum.elim Subtype.val (fun i => ![g,k,t] i)

theorem unsplit_split (j : S) : unsplit g k t (split g k t j) = j := by
  unfold split
  split_ifs <;> simp_all [unsplit]

include hgk hgt hkt in
theorem split_unsplit (j : Work g k t ⊕ Fin 3) : split g k t (unsplit g k t j) = j := by
  rcases j with j | j
  · simp [unsplit,split,j.property.1,j.property.2.1,j.property.2.2]
  · fin_cases j <;> simp [unsplit,split,hgk,hgt,hkt,Ne.symm hgk,Ne.symm hgt,Ne.symm hkt]

def portEquiv : S ≃ Work g k t ⊕ Fin 3 where
  toFun := split g k t
  invFun := unsplit g k t
  left_inv := unsplit_split g k t
  right_inv := split_unsplit g k t hgk hgt hkt

abbrev workCount : ℕ := Fintype.card (Work g k t)

/-- A fixed bank enumeration with the three literal inputs last. This is
part of the fixed program's layout, never a computation on input values. -/
def number : S ≃ Fin (workCount g k t + 3) :=
  (portEquiv g k t hgk hgt hkt).trans
    ((Equiv.sumCongr (Fintype.equivFin (Work g k t)) (Equiv.refl (Fin 3))).trans finSumFinEquiv)

def inputBank (gw kw tw : List Bool) (j : S) : List Bool :=
  if j=g then gw else if j=k then kw else if j=t then tw else []

theorem number_g : number g k t hgk hgt hkt g = (0 : Fin 3).natAdd (workCount g k t) := by
  simp [number,portEquiv,split,finSumFinEquiv_apply_right,finSumFinEquiv]

theorem number_k : number g k t hgk hgt hkt k = (1 : Fin 3).natAdd (workCount g k t) := by
  simp [number,portEquiv,split,Ne.symm hgk,finSumFinEquiv_apply_right,finSumFinEquiv]

theorem number_t : number g k t hgk hgt hkt t = (2 : Fin 3).natAdd (workCount g k t) := by
  simp [number,portEquiv,split,Ne.symm hgt,Ne.symm hkt,finSumFinEquiv_apply_right,finSumFinEquiv]

theorem inputBank_widen (gw kw tw : List Bool) :
    (fun i => inputBank g k t gw kw tw ((number g k t hgk hgt hkt).symm i)) =
      A3Assembly.Wrap.widen (workCount g k t) ![gw,kw,tw] := by
  funext i
  obtain ⟨j,rfl⟩ := (number g k t hgk hgt hkt).surjective i
  simp only [Equiv.symm_apply_apply]
  by_cases h0 : j=g
  · subst j
    rw [number_g]
    simp [inputBank,A3Assembly.Wrap.widen]
  by_cases h1 : j=k
  · subst j
    rw [number_k]
    simp [inputBank,A3Assembly.Wrap.widen,Ne.symm hgk]
  by_cases h2 : j=t
  · subst j
    rw [number_t]
    simp [inputBank,A3Assembly.Wrap.widen,Ne.symm hgt,Ne.symm hkt]
  have hn : (number g k t hgk hgt hkt j).val < workCount g k t := by
    simpa [number,portEquiv,split,h0,h1,h2,finSumFinEquiv_apply_left,workCount,finSumFinEquiv] using
      (Fintype.equivFin (Work g k t) ⟨j,h0,h1,h2⟩).isLt
  simp [inputBank,h0,h1,h2,A3Assembly.Wrap.widen,show ¬workCount g k t ≤ (number g k t hgk hgt hkt j).val by omega]

/-- The existing physical prefixer writes every blank work field; the
three input words are parsed later by the existing bank wrapper. -/
theorem frame_outputs (gw kw tw : List Bool) :
    (Unit4Post.Pre.machine (workCount g k t)).OutputsWithin
      (BitMachineBankCodec.encode ![gw,kw,tw])
      (BitMachineBankCodec.encode (fun i => inputBank g k t gw kw tw
        ((number g k t hgk hgt hkt).symm i))) (workCount g k t+1) := by
  rw [inputBank_widen,A3Assembly.Wrap.encode_widen]
  exact Unit4Post.Pre.outputs _ _

end
end CurrentAdditive.V39ThreePortFrame

#print axioms CurrentAdditive.V39ThreePortFrame.inputBank_widen
#print axioms CurrentAdditive.V39ThreePortFrame.frame_outputs
