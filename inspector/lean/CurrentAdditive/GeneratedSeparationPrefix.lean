import CurrentAdditive.ExactBoost
import CurrentAdditive.PrefixSuffixGlue
import Paper2.SourceProtocolPrefixTree

/-! Appendix I `det:separation`, the complete prefix on the actual indexed
source. This file never replaces a conditioned source by an iid law. -/

namespace CurrentAdditive.GeneratedSeparation

open Paper2 Workspace.Types.Protocol
open CurrentAdditive.ArbitraryPrefix

variable {X Z S : Type*} [Fintype X] [Fintype Z] [Fintype S]
  {q : ℕ}

private theorem mass_split (μ : FiniteLaw X) (R : Set X) (p : X → Prop) :
    μ.prob (fun x => x ∈ R ∧ p x) +
      μ.prob (fun x => x ∈ R ∧ ¬ p x) = μ.prob (· ∈ R) := by
  classical
  simp only [FiniteLaw.prob, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ∈ R <;> by_cases hp : p x <;> simp [hx, hp]

omit [Fintype Z] in
private theorem source_cost_le
    (F : X → Z → Bool) (decode : S → Fin q → Z)
    (Q : Finset (Fin q)) (R : Fin q → Set X) (K : Set S)
    (P : Protocol (Fin q × X) S Bool)
    (heval : ∀ i ∈ Q, ∀ x ∈ R i, ∀ s ∈ K,
      P.eval (i,x) s = F x (decode s i)) :
    Paper2.Compression.restrictionD
      (fun a s => F a.2 (decode s a.1)) (rowRectangle Q R) K ≤ P.cost :=
  selected_suffix_upper (fun a s => F a.2 (decode s a.1)) Q R K P P.cost
    (le_refl _) heval

/-- The exact-source lower bound rules out Bob's first query, and rules out
an Alice child assigned more than half the blocks. Both child assignments
use the actual row fibres cut out by that Alice query. -/
theorem first_alice_balanced
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (source : FiniteLaw S)
    (decode : S → Fin q → Z)
    (hwise : IsDWise 8 source decode ν.toFiniteLaw)
    (Q : Finset (Fin q)) (R : Fin q → Set X) (K : Set S)
    (d t : ℕ) (ρ z : ℝ)
    (hd : 2 ≤ d) (hρ : 0 < ρ) (ht : 1 ≤ t)
    (hscale : (2 : ℝ)^t * ρ ≤ 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw ρ (d : ℤ))
    (hcount : Q.card = 2^t)
    (hrow : ∀ i ∈ Q, z ≤ μ.toFiniteLaw.prob (· ∈ R i))
    (hgap : 2 * (2 : ℝ)^t * ρ < z)
    (hK : (18/25 : ℝ) ≤ source.prob (· ∈ K))
    (P : Protocol (Fin q × X) S Bool)
    (hcost : P.cost ≤ d+t)
    (heval : ∀ i ∈ Q, ∀ x ∈ R i, ∀ s ∈ K,
      P.eval (i,x) s = F x (decode s i)) :
    ∃ (pred : Fin q × X → Bool)
      (l r : Protocol (Fin q × X) S Bool)
      (Qfalse Qtrue : Finset (Fin q)),
      P = Protocol.aNode pred l r ∧
      Qfalse ⊆ Q ∧ Qtrue ⊆ Q ∧
      Qfalse.card = 2^(t-1) ∧ Qtrue.card = 2^(t-1) ∧
      (∀ i ∈ Qfalse,
        z/2 ≤ μ.toFiniteLaw.prob
          (fun x => x ∈ R i ∧ pred (i,x) = false)) ∧
      (∀ i ∈ Qtrue,
        z/2 ≤ μ.toFiniteLaw.prob
          (fun x => x ∈ R i ∧ pred (i,x) = true)) ∧
      l.cost ≤ d+t-1 ∧ r.cost ≤ d+t-1 ∧
      (∀ i ∈ Qfalse, ∀ x ∈ R i, pred (i,x) = false →
        ∀ s ∈ K, l.eval (i,x) s = F x (decode s i)) ∧
      (∀ i ∈ Qtrue, ∀ x ∈ R i, pred (i,x) = true →
        ∀ s ∈ K, r.eval (i,x) s = F x (decode s i)) := by
  classical
  have hcountBoost : 2^(t-1)+1 ≤ Q.card := by
    rw [hcount]
    have hpow : 0 < 2^(t-1) := pow_pos (by omega) _
    have hpowEq : 2^t = 2 * 2^(t-1) := by
      calc
        2^t = 2^((t-1)+1) := by congr 1; omega
        _ = 2 * 2^(t-1) := by rw [pow_succ]; omega
    omega
  have hrowBoost : ∀ i ∈ Q,
      (2 : ℝ)^t * ρ ≤ μ.toFiniteLaw.prob (· ∈ R i) := by
    intro i hi
    have hh := hrow i hi
    have hp : 0 ≤ (2 : ℝ)^t * ρ := by positivity
    linarith
  have hKBoost : (9/25 : ℝ) ≤ source.prob (· ∈ K) := by linarith
  cases P with
  | leaf b =>
      have hl := CurrentAdditive.ArbitraryPrefix.exactboost μ ν F source decode
        hwise Q R K d t ρ ht hd hρ hscale hprofile hcountBoost
        hrowBoost hKBoost
      have hu := source_cost_le F decode Q R K (.leaf b) heval
      simp only [Protocol.cost] at hu
      omega
  | bNode pred l r =>
      obtain ⟨bit, K', hsub, hbit, hmass⟩ := bob_child source K pred
      let C : Protocol (Fin q × X) S Bool := if bit then r else l
      have hcostC : C.cost ≤ d+t-1 := by
        dsimp [C]
        split_ifs <;> simp only [Protocol.cost] at hcost <;> omega
      have hevalC : ∀ i ∈ Q, ∀ x ∈ R i, ∀ s ∈ K',
          C.eval (i,x) s = F x (decode s i) := by
        intro i hi x hx s hs
        have hb := hbit s hs
        have he := heval i hi x hx s (hsub hs)
        cases bit <;> simpa [C, Protocol.eval, hb] using he
      have hK' : (9/25 : ℝ) ≤ source.prob (· ∈ K') := by linarith
      have hl := CurrentAdditive.ArbitraryPrefix.exactboost μ ν F source decode
        hwise Q R K' d t ρ ht hd hρ hscale hprofile hcountBoost
        hrowBoost hK'
      have hu := source_cost_le F decode Q R K' C hevalC
      omega
  | aNode pred l r =>
      let high (i : Fin q) : Prop :=
        2 * μ.toFiniteLaw.prob (fun x => x ∈ R i ∧ pred (i,x) = true) ≥
          μ.toFiniteLaw.prob (· ∈ R i)
      let Qt := Q.filter high
      let Qf := Q.filter (fun i => ¬ high i)
      let Rt : Fin q → Set X := fun i => {x | x ∈ R i ∧ pred (i,x) = true}
      let Rf : Fin q → Set X := fun i => {x | x ∈ R i ∧ pred (i,x) = false}
      have hsum : Qt.card + Qf.card = Q.card := by
        simpa [Qt, Qf, add_comm] using
          (Finset.card_filter_add_card_filter_not (s := Q) high)
      have hQt : Qt ⊆ Q := Finset.filter_subset _ _
      have hQf : Qf ⊆ Q := Finset.filter_subset _ _
      have htrow : ∀ i ∈ Qt, z/2 ≤ μ.toFiniteLaw.prob (· ∈ Rt i) := by
        intro i hi
        have hg : high i := (Finset.mem_filter.mp hi).2
        have hr := hrow i (hQt hi)
        dsimp [high, Rt] at hg ⊢
        linarith
      have hfrow : ∀ i ∈ Qf, z/2 ≤ μ.toFiniteLaw.prob (· ∈ Rf i) := by
        intro i hi
        have hg : ¬ high i := (Finset.mem_filter.mp hi).2
        have hr := hrow i (hQf hi)
        have hs := mass_split μ.toFiniteLaw (R i)
          (fun x => pred (i,x) = true)
        dsimp [high] at hg
        have hfalse : (fun x => x ∈ R i ∧ ¬ pred (i,x) = true) =
            (fun x => x ∈ R i ∧ pred (i,x) = false) := by
          funext x
          cases pred (i,x) <;> simp
        rw [hfalse] at hs
        dsimp [Rf]
        linarith
      have hcostL : l.cost ≤ d+t-1 := by
        simp only [Protocol.cost] at hcost
        omega
      have hcostR : r.cost ≤ d+t-1 := by
        simp only [Protocol.cost] at hcost
        omega
      have hevalL : ∀ i ∈ Qf, ∀ x ∈ Rf i, ∀ s ∈ K,
          l.eval (i,x) s = F x (decode s i) := by
        intro i hi x hx s hs
        have he := heval i (hQf hi) x hx.1 s hs
        simpa [Protocol.eval, hx.2] using he
      have hevalR : ∀ i ∈ Qt, ∀ x ∈ Rt i, ∀ s ∈ K,
          r.eval (i,x) s = F x (decode s i) := by
        intro i hi x hx s hs
        have he := heval i (hQt hi) x hx.1 s hs
        simpa [Protocol.eval, hx.2] using he
      have hside (bit : Bool) (Qb : Finset (Fin q))
          (Rb : Fin q → Set X) (Pb : Protocol (Fin q × X) S Bool)
          (hcard : 2^(t-1)+1 ≤ Qb.card)
          (hrowb : ∀ i ∈ Qb, z/2 ≤ μ.toFiniteLaw.prob (· ∈ Rb i))
          (hcostb : Pb.cost ≤ d+t-1)
          (hevalb : ∀ i ∈ Qb, ∀ x ∈ Rb i, ∀ s ∈ K,
            Pb.eval (i,x) s = F x (decode s i)) : False := by
        have hrowBoostb : ∀ i ∈ Qb,
            (2 : ℝ)^t * ρ ≤ μ.toFiniteLaw.prob (· ∈ Rb i) := by
          intro i hi
          have hr := hrowb i hi
          linarith
        have hl := CurrentAdditive.ArbitraryPrefix.exactboost μ ν F source decode
          hwise Qb Rb K d t ρ ht hd hρ hscale hprofile hcard
          hrowBoostb hKBoost
        have hu := source_cost_le F decode Qb Rb K Pb hevalb
        omega
      have hQtcard : Qt.card ≤ 2^(t-1) := by
        by_contra hn
        exact hside true Qt Rt r (by omega) htrow hcostR hevalR
      have hQfcard : Qf.card ≤ 2^(t-1) := by
        by_contra hn
        exact hside false Qf Rf l (by omega) hfrow hcostL hevalL
      have hpow : 2^t = 2^(t-1)+2^(t-1) := by
        calc
          2^t = 2^((t-1)+1) := by congr 1; omega
          _ = 2^(t-1)+2^(t-1) := by rw [pow_succ]; omega
      have hQtEq : Qt.card = 2^(t-1) := by omega
      have hQfEq : Qf.card = 2^(t-1) := by omega
      refine ⟨pred, l, r, Qf, Qt, rfl, hQf, hQt,
        hQfEq, hQtEq, ?_, ?_, hcostL, hcostR, ?_, ?_⟩
      · simpa [Rf] using hfrow
      · simpa [Rt] using htrow
      · intro i hi x hx hb s hs
        exact hevalL i hi x ⟨hx, hb⟩ s hs
      · intro i hi x hx hb s hs
        exact hevalR i hi x ⟨hx, hb⟩ s hs

#print axioms CurrentAdditive.GeneratedSeparation.first_alice_balanced

/-- Every one of the first `t` nodes on every branch is an Alice node.
The proof treats fixed Alice messages as real protocol bits: a fixed message
would make one of the two required block groups empty. -/
theorem complete_alice_prefix
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (source : FiniteLaw S)
    (decode : S → Fin q → Z)
    (hwise : IsDWise 8 source decode ν.toFiniteLaw)
    (Q : Finset (Fin q)) (R : Fin q → Set X) (K : Set S)
    (d t : ℕ) (ρ z : ℝ)
    (hd : 2 ≤ d) (hρ : 0 < ρ)
    (hscale : (2 : ℝ)^t * ρ ≤ 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw ρ (d : ℤ))
    (hcount : Q.card = 2^t)
    (hrow : ∀ i ∈ Q, z ≤ μ.toFiniteLaw.prob (· ∈ R i))
    (hgap : 2 * (2 : ℝ)^t * ρ < z)
    (hK : (18/25 : ℝ) ≤ source.prob (· ∈ K))
    (P : Protocol (Fin q × X) S Bool)
    (hcost : P.cost ≤ d+t)
    (heval : ∀ i ∈ Q, ∀ x ∈ R i, ∀ s ∈ K,
      P.eval (i,x) s = F x (decode s i)) :
    Paper2.SourceProtocolPrefixTree.CompleteAlicePrefix t P := by
  induction t generalizing Q R z P with
  | zero => trivial
  | succ t ih =>
      obtain ⟨pred, l, r, Qf, Qt, hP, hQf, hQt, hcountf, hcountt,
        hrowf, hrowt, hcostl, hcostr, hevall, hevalr⟩ :=
        first_alice_balanced μ ν F source decode hwise Q R K d (t+1) ρ z
          hd hρ (by omega) hscale hprofile hcount hrow hgap hK P hcost heval
      subst P
      have hscale' : (2 : ℝ)^t * ρ ≤ 1 := by
        have hpos : 0 ≤ (2 : ℝ)^t * ρ := by positivity
        rw [pow_succ] at hscale
        nlinarith
      have hgap' : 2 * (2 : ℝ)^t * ρ < z/2 := by
        rw [pow_succ] at hgap
        nlinarith
      have hcostl' : l.cost ≤ d+t := by omega
      have hcostr' : r.cost ≤ d+t := by omega
      have hcountf' : Qf.card = 2^t := by simpa using hcountf
      have hcountt' : Qt.card = 2^t := by simpa using hcountt
      have hleft := ih Qf (fun i => {x | x ∈ R i ∧ pred (i,x) = false})
        (z/2) hscale' hcountf' hrowf hgap' l hcostl' (by
          intro i hi x hx s hs
          exact hevall i hi x hx.1 hx.2 s hs)
      have hright := ih Qt (fun i => {x | x ∈ R i ∧ pred (i,x) = true})
        (z/2) hscale' hcountt' hrowt hgap' r hcostr' (by
          intro i hi x hx s hs
          exact hevalr i hi x hx.1 hx.2 s hs)
      exact ⟨hleft, hright⟩

#print axioms CurrentAdditive.GeneratedSeparation.complete_alice_prefix

end CurrentAdditive.GeneratedSeparation
