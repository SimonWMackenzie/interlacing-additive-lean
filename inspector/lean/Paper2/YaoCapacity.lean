import Paper2.YaoStrategies

/-!
# Column capacity with fixed Alice maps

Statement source: locked Paper 2 v12, `sections/07-yao.tex:208--230`,
`yao:capacity` (T28). The finite catalogue below is built from the actual
fixed Alice maps and fixed leaf outputs. At Bob nodes it takes a union;
at Alice nodes it combines the two actual row-dependent branches.
Thus Bob's choice is common to all rows at that transcript. Coverage is
proved for concrete completions, not assumed as a cardinality contract.
-/

namespace Paper2.Yao

open Workspace.Types.Protocol

universe u v
variable {X : Type u} {Y : Type v}

/-- All output columns obtainable by supplying one Boolean decision at each
Bob node. Alice's maps and the public leaf labels are fixed. -/
noncomputable def columnCatalogue : Protocol X Y Bool → Finset (X → Bool)
  | .leaf b => {fun _ => b}
  | .aNode a l r => by
      classical
      exact ((columnCatalogue l) ×ˢ (columnCatalogue r)).image
        (fun fg x => if a x then fg.2 x else fg.1 x)
  | .bNode _ l r => by
      classical
      exact columnCatalogue l ∪ columnCatalogue r

theorem columnCatalogue_nonempty (P : Protocol X Y Bool) :
    (columnCatalogue P).Nonempty := by
  classical
  induction P with
  | leaf b => exact ⟨_, Finset.mem_singleton_self _⟩
  | aNode a l r ihl ihr =>
      obtain ⟨f, hf⟩ := ihl
      obtain ⟨g, hg⟩ := ihr
      refine ⟨fun x => if a x then g x else f x, Finset.mem_image.mpr ?_⟩
      exact ⟨(f, g), Finset.mem_product.mpr ⟨hf, hg⟩, rfl⟩
  | bNode b l r ihl ihr => exact Finset.Nonempty.mono Finset.subset_union_left ihl

/-- Each actual column of the protocol is represented. This permits Bob's
maps to depend on the entire column, never on the row. -/
theorem actualColumn_mem_catalogue (P : Protocol X Y Bool) (y : Y) :
    (fun x => P.eval x y) ∈ columnCatalogue P := by
  classical
  induction P with
  | leaf b => exact Finset.mem_singleton_self _
  | aNode a l r ihl ihr =>
      exact Finset.mem_image.mpr ⟨(fun x => l.eval x y, fun x => r.eval x y),
        Finset.mem_product.mpr ⟨ihl, ihr⟩, rfl⟩
  | bNode b l r ihl ihr =>
      cases hy : b y with
      | false => simpa [Protocol.eval, hy, columnCatalogue] using Finset.mem_union_left _ ihl
      | true => simpa [Protocol.eval, hy, columnCatalogue] using Finset.mem_union_right _ ihr

theorem catalogue_alice_card_le (a : X → Bool) (l r : Protocol X Y Bool) :
    (columnCatalogue (.aNode a l r)).card ≤
      (columnCatalogue l).card * (columnCatalogue r).card := by
  classical
  exact (Finset.card_image_le).trans (by rw [Finset.card_product])

theorem catalogue_bob_card_le (b : Y → Bool) (l r : Protocol X Y Bool) :
    (columnCatalogue (.bNode b l r)).card ≤
      (columnCatalogue l).card + (columnCatalogue r).card := by
  classical
  exact Finset.card_union_le _ _

/-- If every retained row sends the same Alice bit, only that subtree's
column catalogue matters. The other subtree is allowed to be unreachable. -/
theorem catalogue_alice_uniform_card_le (a : X → Bool) (l r : Protocol X Y Bool)
    (b : Bool) (ha : ∀ x, a x = b) :
    (columnCatalogue (.aNode a l r)).card ≤ (columnCatalogue (if b then r else l)).card := by
  classical
  apply Finset.card_le_card
  intro f hf
  obtain ⟨⟨g0, g1⟩, hg, rfl⟩ := Finset.mem_image.mp hf
  have hg0 := (Finset.mem_product.mp hg).1
  have hg1 := (Finset.mem_product.mp hg).2
  cases b with
  | false => simpa [ha] using hg0
  | true => simpa [ha] using hg1

/-- Changing Bob's maps does not change the catalogue. -/
theorem catalogue_eq_of_forget_eq {P : Protocol X Y Bool} {Y' : Type*}
    {Q : Protocol X Y' Bool} (h : PartialProtocol.forget P = PartialProtocol.forget Q) :
    columnCatalogue P = columnCatalogue Q := by
  induction P generalizing Q with
  | leaf b => cases Q <;> simp_all [PartialProtocol.forget, columnCatalogue]
  | aNode a l r ihl ihr =>
      cases Q <;> simp only [PartialProtocol.forget, PartialProtocol.alice.injEq] at h
      · contradiction
      · rcases h with ⟨rfl, hl, hr⟩
        simp [columnCatalogue, ihl hl, ihr hr]
      · contradiction
  | bNode b l r ihl ihr =>
      cases Q <;> simp only [PartialProtocol.forget, PartialProtocol.bob.injEq] at h
      · contradiction
      · contradiction
      · rcases h with ⟨hl, hr⟩
        simp [columnCatalogue, ihl hl, ihr hr]

theorem completionColumn_mem_catalogue (P : PartialProtocol X) {Y' : Type*}
    (c : P.Completion Y') (y : Y') (Q : Protocol X Y Bool)
    (hQ : PartialProtocol.forget Q = P) :
    (fun x => (P.complete c).eval x y) ∈ columnCatalogue Q := by
  have hf : PartialProtocol.forget (P.complete c) = P := by
    clear hQ
    induction P with
    | leaf b => rfl
    | alice a l r ihl ihr => simp [PartialProtocol.complete, PartialProtocol.forget, ihl, ihr]
    | bob l r ihl ihr => simp [PartialProtocol.complete, PartialProtocol.forget, ihl, ihr]
  rw [← catalogue_eq_of_forget_eq (hf.trans hQ.symm)]
  exact actualColumn_mem_catalogue _ _

private theorem exponent_step (a : ℕ) :
    2 * (2 ^ a - 1) + 1 = 2 ^ (a + 1) - 1 := by
  have hp : 1 ≤ 2 ^ a := Nat.one_le_pow a 2 (by decide)
  rw [pow_succ]
  omega

/-- Unrestricted early behaviour within an Alice-last suffix. The paired
statements are proved together by Alice product and Bob union recurrences.
The Bob depth-zero branch is explicitly a public leaf, not a missing bit. -/
theorem suffix_catalogue_bounds (a : ℕ) :
    (∀ P : Protocol X Y Bool, IsComplete P (2 * a + 1) → Alternates .alice P →
      CanonicalLastLeaves (2 * a + 1) P →
      (columnCatalogue P).card ≤ 2 ^ (2 * (2 ^ a - 1))) ∧
    (∀ P : Protocol X Y Bool, IsComplete P (2 * a) → Alternates .bob P →
      (a = 0 ∨ CanonicalLastLeaves (2 * a) P) →
      (columnCatalogue P).card ≤ 2 ^ (2 ^ a - 1)) := by
  classical
  induction a with
  | zero =>
      constructor
      · intro P hc ha hn
        obtain ⟨f, l, r, rfl⟩ := alice_root_of_complete P 0 hc ha
        rcases hn with ⟨rfl, rfl⟩
        simp [columnCatalogue]
      · intro P hc _ _
        obtain ⟨b, rfl⟩ := (IsComplete.zero_iff P).mp hc
        simp [columnCatalogue]
  | succ a ih =>
      have hb : ∀ P : Protocol X Y Bool,
          IsComplete P (2 * (a + 1)) → Alternates .bob P →
          (a + 1 = 0 ∨ CanonicalLastLeaves (2 * (a + 1)) P) →
          (columnCatalogue P).card ≤ 2 ^ (2 ^ (a + 1) - 1) := by
        intro P hc ha hn
        have hn' := hn.resolve_left (by omega)
        have hc' : IsComplete P ((2 * a + 1) + 1) := by simpa [Nat.mul_add] using hc
        have hn'' : CanonicalLastLeaves ((2 * a) + 2) P := by simpa [Nat.mul_add] using hn'
        cases P with
        | leaf b => exact False.elim hc'
        | aNode f l r => exact False.elim ha
        | bNode b l r =>
            have hl := ih.1 l hc'.1 ha.1 hn''.1
            have hr := ih.1 r hc'.2 ha.2 hn''.2
            calc
              (columnCatalogue (.bNode b l r)).card ≤
                  (columnCatalogue l).card + (columnCatalogue r).card := catalogue_bob_card_le _ _ _
              _ ≤ 2 ^ (2 * (2 ^ a - 1)) + 2 ^ (2 * (2 ^ a - 1)) := Nat.add_le_add hl hr
              _ = 2 ^ (2 ^ (a + 1) - 1) := by
                rw [← two_mul, ← pow_succ', exponent_step]
      refine ⟨?_, hb⟩
      intro P hc ha hn
      obtain ⟨f, l, r, rfl⟩ := alice_root_of_complete P (2 * (a + 1)) hc ha
      have hn' : CanonicalLastLeaves ((2 * a + 1) + 2) (.aNode f l r) := by
        simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hn
      have hl := hb l hc.1 ha.1 (Or.inr (by simpa [Nat.mul_add] using hn'.1))
      have hr := hb r hc.2 ha.2 (Or.inr (by simpa [Nat.mul_add] using hn'.2))
      calc
        (columnCatalogue (.aNode f l r)).card ≤
            (columnCatalogue l).card * (columnCatalogue r).card := catalogue_alice_card_le _ _ _
        _ ≤ 2 ^ (2 ^ (a + 1) - 1) * 2 ^ (2 ^ (a + 1) - 1) := Nat.mul_le_mul hl hr
        _ = 2 ^ (2 * (2 ^ (a + 1) - 1)) := by rw [← pow_add, two_mul]

/-- Common early response strategy controls the whole retained row carrier.
Here `k+1` is the paper's positive number `t` of early Alice turns. -/
theorem common_strategy_catalogue_bound (k a : ℕ) (P : Protocol X Y Bool)
    (hc : IsComplete P (2 * k + 1 + 2 * a)) (ha : Alternates .alice P)
    (hn : CanonicalLastLeaves (2 * k + 1 + 2 * a) P)
    (σ : ResponseStrategy (k + 1)) (hσ : ∀ x, earlyStrategy (k + 1) P x = σ) :
    (columnCatalogue P).card ≤ 2 ^ (k + (2 ^ a - 1)) := by
  classical
  induction k generalizing P with
  | zero =>
      have hc' : IsComplete P (2 * a + 1) := by simpa [Nat.add_comm] using hc
      obtain ⟨f, l, r, rfl⟩ := alice_root_of_complete P (2 * a) hc' ha
      have hf : ∀ x, f x = σ.1 := by
        intro x
        exact congrArg Prod.fst (hσ x)
      let Q : Protocol X Y Bool := if σ.1 then r else l
      have hQ : IsComplete Q (2 * a) ∧ Alternates .bob Q := by
        cases hb : σ.1 <;> simp [Q, hb, hc'.1, hc'.2, ha.1, ha.2]
      have hnQ : a = 0 ∨ CanonicalLastLeaves (2 * a) Q := by
        cases a with
        | zero => exact Or.inl rfl
        | succ a =>
            right
            have hn' : CanonicalLastLeaves ((2 * a + 1) + 2) (.aNode f l r) := by
              simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hn
            cases hb : σ.1 with
            | false => simpa [Q, hb, Nat.mul_add, Nat.add_assoc] using hn'.1
            | true => simpa [Q, hb, Nat.mul_add, Nat.add_assoc] using hn'.2
      have hb := (suffix_catalogue_bounds (X := X) (Y := Y) a).2 Q hQ.1 hQ.2 hnQ
      exact (catalogue_alice_uniform_card_le f l r σ.1 hf).trans (by simpa [Q] using hb)
  | succ k ih =>
      let d := 2 * k + 1 + 2 * a
      have hc' : IsComplete P (d + 2) := by
        simpa [d, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc
      have hn' : CanonicalLastLeaves (d + 2) P := by
        simpa [d, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hn
      obtain ⟨f, l, r, rfl⟩ := alice_root_of_complete P (d + 1) hc' ha
      have hf : ∀ x, f x = σ.1 := by
        intro x
        exact congrArg Prod.fst (hσ x)
      let Q : Protocol X Y Bool := if σ.1 then r else l
      have hQ : IsComplete Q (d + 1) ∧ Alternates .bob Q ∧
          CanonicalLastLeaves (d + 1) Q := by
        cases hb : σ.1 <;>
          simp [Q, hb, hc'.1, hc'.2, ha.1, ha.2, hn'.1, hn'.2]
      have hfalse : ∀ x, earlyStrategy (k + 1) (afterBob Q false) x = σ.2.1 := by
        intro x
        have hh := congrArg (fun z : ResponseStrategy (k + 2) => z.2.1) (hσ x)
        simpa only [earlyStrategy, afterRound, afterAlice, hf x] using hh
      have htrue : ∀ x, earlyStrategy (k + 1) (afterBob Q true) x = σ.2.2 := by
        intro x
        have hh := congrArg (fun z : ResponseStrategy (k + 2) => z.2.2) (hσ x)
        simpa only [earlyStrategy, afterRound, afterAlice, hf x] using hh
      have hQbound : (columnCatalogue Q).card ≤ 2 ^ (k + 1 + (2 ^ a - 1)) := by
        cases hshape : Q with
        | leaf b => simp [hshape, IsComplete] at hQ
        | aNode g l' r' => simp [hshape, Alternates] at hQ
        | bNode b l' r' =>
            have hcl : IsComplete l' d ∧ IsComplete r' d := by
              simpa [hshape, IsComplete] using hQ.1
            have hal : Alternates .alice l' ∧ Alternates .alice r' := by
              simpa [hshape, Alternates] using hQ.2.1
            have hnl : CanonicalLastLeaves d l' ∧ CanonicalLastLeaves d r' := by
              have hd : ∃ j, d = j + 1 := ⟨2 * k + 2 * a, by dsimp [d]; omega⟩
              obtain ⟨j, hj⟩ := hd
              simpa [hshape, hj, CanonicalLastLeaves] using hQ.2.2
            have hl := ih l' hcl.1 hal.1 hnl.1 σ.2.1 (by simpa [hshape, afterBob] using hfalse)
            have hr := ih r' hcl.2 hal.2 hnl.2 σ.2.2 (by simpa [hshape, afterBob] using htrue)
            calc
              (columnCatalogue (.bNode b l' r')).card ≤
                  (columnCatalogue l').card + (columnCatalogue r').card := catalogue_bob_card_le _ _ _
              _ ≤ 2 ^ (k + (2 ^ a - 1)) + 2 ^ (k + (2 ^ a - 1)) := Nat.add_le_add hl hr
              _ = 2 ^ (k + 1 + (2 ^ a - 1)) := by
                rw [← two_mul, ← pow_succ']
                congr 1
                omega
      exact (catalogue_alice_uniform_card_le f l r σ.1 hf).trans hQbound

/-- Source T28's numerical exponent, with `t≥1` and `a=0` included. -/
theorem common_strategy_capacity (t a : ℕ) (ht : 1 ≤ t) (P : Protocol X Y Bool)
    (hc : IsComplete P ((2 * t - 1) + 2 * a)) (ha : Alternates .alice P)
    (hn : CanonicalLastLeaves ((2 * t - 1) + 2 * a) P)
    (σ : ResponseStrategy t) (hσ : ∀ x, earlyStrategy t P x = σ) :
    (columnCatalogue P).card ≤ 2 ^ (2 ^ a + t - 2) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  have hd : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  have h := common_strategy_catalogue_bound k a P (by simpa [hd] using hc) ha
    (by simpa [hd] using hn) σ hσ
  have hp : 1 ≤ 2 ^ a := Nat.one_le_pow a 2 (by decide)
  have he : k + (2 ^ a - 1) = 2 ^ a + (k + 1) - 2 := by omega
  simpa [he] using h

/-! ## Actual retained rows and all Bob completions -/

open Workspace.UpperBound

variable {X' Y' : Type*}

theorem isComplete_comap (P : Protocol X Y Bool) (f : X' → X) (g : Y' → Y)
    (d : ℕ) (h : IsComplete P d) : IsComplete (Protocol.comap f g P) d := by
  induction d generalizing P with
  | zero =>
      obtain ⟨b, rfl⟩ := (IsComplete.zero_iff P).mp h
      trivial
  | succ d ih =>
      cases P with
      | leaf b => exact False.elim h
      | aNode a l r => exact ⟨ih l h.1, ih r h.2⟩
      | bNode b l r => exact ⟨ih l h.1, ih r h.2⟩

theorem alternates_comap (P : Protocol X Y Bool) (f : X' → X) (g : Y' → Y)
    (s : Turn) (h : Alternates s P) : Alternates s (Protocol.comap f g P) := by
  induction P generalizing s with
  | leaf b => trivial
  | aNode a l r ihl ihr =>
      cases s with
      | alice => exact ⟨ihl .bob h.1, ihr .bob h.2⟩
      | bob => exact False.elim h
  | bNode b l r ihl ihr =>
      cases s with
      | alice => exact False.elim h
      | bob => exact ⟨ihl .alice h.1, ihr .alice h.2⟩

theorem canonicalLastLeaves_comap (P : Protocol X Y Bool) (f : X' → X) (g : Y' → Y)
    (d : ℕ) (h : CanonicalLastLeaves d P) :
    CanonicalLastLeaves d (Protocol.comap f g P) := by
  induction d using Nat.twoStepInduction generalizing P with
  | zero => cases P <;> exact False.elim h
  | one =>
      cases P with
      | leaf b => exact False.elim h
      | aNode a l r => rcases h with ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
      | bNode b l r => rcases h with ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
  | more d _ ih =>
      cases P with
      | leaf b => exact False.elim h
      | aNode a l r => exact ⟨ih l h.1, ih r h.2⟩
      | bNode b l r => exact ⟨ih l h.1, ih r h.2⟩

theorem afterRound_comap (P : Protocol X Y Bool) (f : X' → X) (g : Y' → Y)
    (x : X') (b : Bool) :
    afterRound (Protocol.comap f g P) x b = Protocol.comap f g (afterRound P (f x) b) := by
  have hA : afterAlice (Protocol.comap f g P) x = Protocol.comap f g (afterAlice P (f x)) := by
    cases P with
    | leaf c => rfl
    | aNode a l r => cases hx : a (f x) <;> simp [afterAlice, Protocol.comap, hx]
    | bNode c l r => rfl
  have hB : ∀ Q : Protocol X Y Bool,
      afterBob (Protocol.comap f g Q) b = Protocol.comap f g (afterBob Q b) := by
    intro Q
    cases Q with
    | leaf c => rfl
    | aNode a l r => rfl
    | bNode c l r => cases b <;> rfl
  rw [afterRound, hA, hB]
  rfl

theorem earlyStrategy_comap (t : ℕ) (P : Protocol X Y Bool) (f : X' → X) (g : Y' → Y)
    (x : X') : earlyStrategy t (Protocol.comap f g P) x = earlyStrategy t P (f x) := by
  induction t generalizing P with
  | zero => rfl
  | succ t ih =>
      have hm : aliceMessage (Protocol.comap f g P) x = aliceMessage P (f x) := by
        cases P <;> rfl
      simp only [earlyStrategy, hm, afterRound_comap, ih]

/-- Restrict any catalogue column to the actual retained row labels. -/
theorem catalogue_comap_mem (P : Protocol X Y Bool) (f : X' → X) (g : Y' → Y)
    (v : X → Bool) (hv : v ∈ columnCatalogue P) :
    (fun x => v (f x)) ∈ columnCatalogue (Protocol.comap f g P) := by
  classical
  induction P generalizing v with
  | leaf b =>
      have he : v = fun _ => b := Finset.mem_singleton.mp hv
      subst v
      exact Finset.mem_singleton_self _
  | aNode a l r ihl ihr =>
      obtain ⟨⟨v0, v1⟩, hh, rfl⟩ := Finset.mem_image.mp hv
      refine Finset.mem_image.mpr ⟨(fun x => v0 (f x), fun x => v1 (f x)), ?_, rfl⟩
      exact Finset.mem_product.mpr ⟨ihl _ (Finset.mem_product.mp hh).1,
        ihr _ (Finset.mem_product.mp hh).2⟩
  | bNode b l r ihl ihr =>
      rcases Finset.mem_union.mp hv with hl | hr
      · exact Finset.mem_union_left _ (ihl _ hl)
      · exact Finset.mem_union_right _ (ihr _ hr)

/-- Actual Boolean columns on a retained row set, with an arbitrary Bob
completion for that one column. The completion is chosen before all rows. -/
def completionColumns (P : Protocol X Y Bool) (U : Set X) : Set (U → Bool) :=
  {v | ∃ c : (PartialProtocol.forget P).Completion Unit,
    ∀ x : U, ((PartialProtocol.forget P).complete c).eval x.val () = v x}

theorem completionColumns_subset_catalogue (P : Protocol X Y Bool) (U : Set X) :
    completionColumns P U ⊆
      (columnCatalogue (Protocol.comap (fun x : U => x.val) id P) : Set (U → Bool)) := by
  intro v hv
  obtain ⟨c, hc⟩ := hv
  have hm := completionColumn_mem_catalogue (PartialProtocol.forget P) c () P rfl
  have hr := catalogue_comap_mem P (fun x : U => x.val) id _ hm
  have he : (fun x : U => ((PartialProtocol.forget P).complete c).eval x.val ()) = v :=
    funext hc
  simpa only [he] using hr

/-- Full T28: all Bob completions on an arbitrary retained row set. The
strategy hypothesis concerns all hypothetical histories; the normalized
last-bit convention is the concrete predicate proved by `YaoNormalization`.
The empty suffix `a=0` and empty retained set are included. -/
theorem retained_common_strategy_capacity (t a : ℕ) (ht : 1 ≤ t)
    (P : Protocol X Y Bool) (U : Set X)
    (hc : IsComplete P ((2 * t - 1) + 2 * a)) (ha : Alternates .alice P)
    (hn : CanonicalLastLeaves ((2 * t - 1) + 2 * a) P)
    (σ : ResponseStrategy t) (hσ : ∀ x ∈ U, earlyStrategy t P x = σ) :
    (completionColumns P U).ncard ≤ 2 ^ (2 ^ a + t - 2) := by
  classical
  let Q := Protocol.comap (fun x : U => x.val) id P
  have hbound : (columnCatalogue Q).card ≤ 2 ^ (2 ^ a + t - 2) :=
    common_strategy_capacity t a ht Q
      (isComplete_comap P _ _ _ hc) (alternates_comap P _ _ _ ha)
      (canonicalLastLeaves_comap P _ _ _ hn) σ (by
        intro x
        simpa [Q, earlyStrategy_comap] using hσ x.val x.property)
  have hsub := completionColumns_subset_catalogue P U
  have hncard := Set.ncard_le_ncard hsub (Finset.finite_toSet (columnCatalogue Q))
  exact hncard.trans (by simpa using hbound)

end Paper2.Yao
