import CurrentAdditive.V38Fin2PrefixGeneric

/-! The block assignment in selected v39 `cl:separation`.  Every complete
Alice transcript receives a distinct actual original block.  The assignment
uses the majority row fibres of the actual protocol, not an abstract tree. -/

namespace CurrentAdditive.V38Fin2Prefix

open Paper2 Workspace.Types.Protocol
open CurrentAdditive.ArbitraryPrefix

variable {X Z S : Type*} [Fintype X] [Fintype Z] [Fintype S]
  {q : ℕ}

theorem bitCons_head_tail {t : ℕ} (w : Fin (2^(t+1))) :
    NPCC.Protocol.bitCons (NPCC.Protocol.bitHead w)
      (NPCC.Protocol.bitTail w) = w := by
  apply Fin.ext
  by_cases h : 2^t ≤ w.val
  · simp [NPCC.Protocol.bitCons, NPCC.Protocol.bitHead,
      NPCC.Protocol.bitTail, h]
  · simp [NPCC.Protocol.bitCons, NPCC.Protocol.bitHead,
      NPCC.Protocol.bitTail, h]

theorem code_ext {t : ℕ} {v w : Fin (2^(t+1))}
    (hh : NPCC.Protocol.bitHead v = NPCC.Protocol.bitHead w)
    (ht : NPCC.Protocol.bitTail v = NPCC.Protocol.bitTail w) : v = w := by
  rw [← bitCons_head_tail v, ← bitCons_head_tail w, hh, ht]

private theorem node_code_iff {t : ℕ}
    (pred : Fin q × X → Bool) (l r : Protocol (Fin q × X) S Bool)
    (a : Fin q × X) (w : Fin (2^(t+1))) :
    NPCC.Protocol.prefixCodeRaw (t+1) (.aNode pred l r) a = w ↔
      pred a = NPCC.Protocol.bitHead w ∧
      NPCC.Protocol.prefixCodeRaw t
        (if NPCC.Protocol.bitHead w then r else l) a =
        NPCC.Protocol.bitTail w := by
  constructor
  · intro h
    have hh := congrArg NPCC.Protocol.bitHead h
    have ht := congrArg NPCC.Protocol.bitTail h
    simp only [NPCC.Protocol.prefixCodeRaw,
      NPCC.Protocol.bitHead_bitCons] at hh
    simp only [NPCC.Protocol.prefixCodeRaw,
      NPCC.Protocol.bitTail_bitCons] at ht
    exact ⟨hh, by simpa only [hh] using ht⟩
  · rintro ⟨hh, ht⟩
    simp only [NPCC.Protocol.prefixCodeRaw, hh, ht]
    exact bitCons_head_tail w

/-- Each prefix part has a different assigned block with the promised row
mass in its actual protocol fibre.  No row or column alphabet is enlarged. -/
theorem assigned_prefix_parts
    (μ : PositiveRationalLaw X)
    (F : X → Z → Bool) (source : FiniteLaw S)
    (decode : S → Fin q → Z)
    (Q : Finset (Fin q)) (R : Fin q → Set X) (K : Set S)
    (d t : ℕ) (ρ z : ℝ)
    (hd : 2 ≤ d) (hρ : 0 < ρ)
    (hscale : (2 : ℝ)^t * ρ ≤ 1)
    (hblock : ExactBlockBound μ F source decode d ρ)
    (hcount : Q.card = 2^t)
    (hrow : ∀ i ∈ Q, z ≤ μ.toFiniteLaw.prob (· ∈ R i))
    (hgap : 2 * (2 : ℝ)^t * ρ < z)
    (hK : (18/25 : ℝ) ≤ source.prob (· ∈ K))
    (P : Protocol (Fin q × X) S Bool)
    (hcost : P.cost ≤ d+t)
    (heval : ∀ i ∈ Q, ∀ x ∈ R i, ∀ s ∈ K,
      P.eval (i,x) s = F x (decode s i)) :
    ∃ dom : Fin (2^t) → Fin q,
      Function.Injective dom ∧
      ∀ w, dom w ∈ Q ∧ z / (2 : ℝ)^t ≤ μ.toFiniteLaw.prob
        (fun x => x ∈ R (dom w) ∧
          NPCC.Protocol.prefixCodeRaw t P (dom w,x) = w) := by
  classical
  induction t generalizing Q R z P with
  | zero =>
      have hQ : Q.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h
        simp [h] at hcount
      obtain ⟨i, hi⟩ := hQ
      refine ⟨fun _ => i, ?_, ?_⟩
      · intro a b _
        apply Fin.ext
        have ha := a.isLt
        have hb := b.isLt
        norm_num at ha hb
        omega
      · intro w
        refine ⟨hi, ?_⟩
        have hw : w = NPCC.Protocol.zeroPow2 0 := by
          apply Fin.ext
          have hh := w.isLt
          norm_num at hh
          simp only [NPCC.Protocol.zeroPow2]
          omega
        simpa [NPCC.Protocol.prefixCodeRaw, NPCC.Protocol.zeroPow2,
          hw]
          using hrow i hi
  | succ t ih =>
      obtain ⟨pred, l, r, Qf, Qt, hP, hQf, hQt, hdisj, hunion,
        hcountf, hcountt, hrowf, hrowt, hcostl, hcostr, hevall, hevalr⟩ :=
        first_alice_balanced μ F source decode Q R K d (t+1) ρ z
          hd hρ (by omega) hscale hblock hcount hrow hgap hK P hcost heval
      subst P
      have hscale' : (2 : ℝ)^t * ρ ≤ 1 := by
        have hpos : 0 ≤ (2 : ℝ)^t * ρ := by positivity
        rw [pow_succ] at hscale
        nlinarith
      have hgap' : 2 * (2 : ℝ)^t * ρ < z/2 := by
        rw [pow_succ] at hgap
        nlinarith
      obtain ⟨df, hdf, hf⟩ := ih Qf
        (fun i => {x | x ∈ R i ∧ pred (i,x) = false}) (z/2)
        hscale' (by simpa using hcountf) hrowf hgap'
        l (by omega) (by
          intro i hi x hx s hs
          exact hevall i hi x hx.1 hx.2 s hs)
      obtain ⟨dt, hdt, ht⟩ := ih Qt
        (fun i => {x | x ∈ R i ∧ pred (i,x) = true}) (z/2)
        hscale' (by simpa using hcountt) hrowt hgap'
        r (by omega) (by
          intro i hi x hx s hs
          exact hevalr i hi x hx.1 hx.2 s hs)
      let dom : Fin (2^(t+1)) → Fin q := fun w =>
        if NPCC.Protocol.bitHead w then dt (NPCC.Protocol.bitTail w)
        else df (NPCC.Protocol.bitTail w)
      refine ⟨dom, ?_, ?_⟩
      · intro a b hab
        have hheads : NPCC.Protocol.bitHead a = NPCC.Protocol.bitHead b := by
          by_contra hn
          cases ha : NPCC.Protocol.bitHead a <;>
            cases hb : NPCC.Protocol.bitHead b
          · exact hn (ha.trans hb.symm)
          · have heq : df (NPCC.Protocol.bitTail a) = dt (NPCC.Protocol.bitTail b) :=
              by simpa [dom, ha, hb] using hab
            exact (Finset.disjoint_left.mp hdisj)
              (hf (NPCC.Protocol.bitTail a)).1
              (heq ▸ (ht (NPCC.Protocol.bitTail b)).1)
          · have heq : dt (NPCC.Protocol.bitTail a) = df (NPCC.Protocol.bitTail b) :=
              by simpa [dom, ha, hb] using hab
            exact (Finset.disjoint_left.mp hdisj)
              (heq ▸ (hf (NPCC.Protocol.bitTail b)).1)
              (ht (NPCC.Protocol.bitTail a)).1
          · exact hn (ha.trans hb.symm)
        apply code_ext hheads
        cases ha : NPCC.Protocol.bitHead a
        · apply hdf
          simpa [dom, ha, ← hheads] using hab
        · apply hdt
          simpa [dom, ha, ← hheads] using hab
      · intro w
        have hden : (z/2)/(2 : ℝ)^t = z/(2 : ℝ)^(t+1) := by
          rw [pow_succ]
          ring
        cases hw : NPCC.Protocol.bitHead w
        · have hh := hf (NPCC.Protocol.bitTail w)
          refine ⟨by simpa [dom, hw] using hQf hh.1, ?_⟩
          rw [← hden]
          convert hh.2 using 1
          apply congrArg μ.toFiniteLaw.prob
          funext x
          simp only [dom, hw, Bool.false_eq_true, ↓reduceIte,
            node_code_iff, Set.mem_setOf_eq]
          exact propext (by tauto)
        · have hh := ht (NPCC.Protocol.bitTail w)
          refine ⟨by simpa [dom, hw] using hQt hh.1, ?_⟩
          rw [← hden]
          convert hh.2 using 1
          apply congrArg μ.toFiniteLaw.prob
          funext x
          simp only [dom, hw, ↓reduceIte, node_code_iff,
            Set.mem_setOf_eq]
          exact propext (by tauto)

#print axioms assigned_prefix_parts

end CurrentAdditive.V38Fin2Prefix
