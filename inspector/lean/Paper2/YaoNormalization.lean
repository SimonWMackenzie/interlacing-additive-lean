import Paper2.YaoModel

/-!
# Complete-depth padding and final-message normalisation

Statement source: Paper 2, locked `2026-09-22-protocol-labels-v12`,
`sections/07-yao.tex:21--24` immediately after `yao:conventions`, and
`appendices/B-yao.tex:44--50` in `yao:payload-event`.

Padding extends actual public-output trees, preserving every original
internal message and adding charged dummy messages below leaves. Final-bit
normalisation acts on a complete positive-depth tree: it preserves all
earlier message functions, including those on unreachable branches, and
gives every final node the same two fixed leaves `false` and `true`.

These are concrete transformations, not an assumed normal-form contract.
They do not count strategies or prove the alternating-model hardness theorem.
-/

namespace Paper2.Yao

open Workspace.Types.Protocol

universe u v
variable {X : Type u} {Y : Type v}

/-- Every syntactic root-to-leaf path has exactly the indicated depth.
This includes branches that no actual input can reach. -/
def IsComplete : Protocol X Y Bool → ℕ → Prop
  | .leaf _, 0 => True
  | .aNode _ l r, d + 1 => IsComplete l d ∧ IsComplete r d
  | .bNode _ l r, d + 1 => IsComplete l d ∧ IsComplete r d
  | _, _ => False

theorem IsComplete.cost_eq {P : Protocol X Y Bool} {d : ℕ}
    (h : IsComplete P d) : P.cost = d := by
  induction d generalizing P with
  | zero => cases P <;> simp_all [IsComplete, Protocol.cost]
  | succ d ih =>
      cases P with
      | leaf b => exact False.elim h
      | aNode a l r => simp [Protocol.cost, ih h.1, ih h.2, Nat.add_comm]
      | bNode b l r => simp [Protocol.cost, ih h.1, ih h.2, Nat.add_comm]

theorem IsComplete.zero_iff (P : Protocol X Y Bool) :
    IsComplete P 0 ↔ ∃ b, P = .leaf b := by
  cases P <;> simp [IsComplete]

/-- Structural extension below leaves. It asserts literal equality of
every original internal speaker and message map; function preservation is
proved separately. No reachability restriction weakens this predicate. -/
def PreservesInternal : Protocol X Y Bool → Protocol X Y Bool → Prop
  | .leaf _, _ => True
  | .aNode a l r, .aNode a' l' r' =>
      a = a' ∧ PreservesInternal l l' ∧ PreservesInternal r r'
  | .bNode b l r, .bNode b' l' r' =>
      b = b' ∧ PreservesInternal l l' ∧ PreservesInternal r r'
  | _, _ => False

theorem preservesInternal_refl (P : Protocol X Y Bool) : PreservesInternal P P := by
  induction P <;> simp_all [PreservesInternal]

/-- Extend leaves by constant-zero messages from the scheduled player.
At depth zero the tree is left unchanged; completion requires `cost ≤ d`. -/
def padTree : Protocol X Y Bool → Turn → ℕ → Protocol X Y Bool
  | P, _, 0 => P
  | .leaf b, .alice, d + 1 =>
      .aNode (fun _ => false) (padTree (.leaf b) .bob d) (padTree (.leaf b) .bob d)
  | .leaf b, .bob, d + 1 =>
      .bNode (fun _ => false) (padTree (.leaf b) .alice d) (padTree (.leaf b) .alice d)
  | .aNode a l r, _, d + 1 => .aNode a (padTree l .bob d) (padTree r .bob d)
  | .bNode b l r, _, d + 1 => .bNode b (padTree l .alice d) (padTree r .alice d)

theorem padTree_eval (P : Protocol X Y Bool) (s : Turn) (d : ℕ) (x : X) (y : Y) :
    (padTree P s d).eval x y = P.eval x y := by
  induction d generalizing P s with
  | zero => rfl
  | succ d ih =>
      cases P with
      | leaf b => cases s <;> simp [padTree, Protocol.eval, ih]
      | aNode a l r => simp [padTree, Protocol.eval, ih]
      | bNode b l r => simp [padTree, Protocol.eval, ih]

theorem padTree_preservesInternal (P : Protocol X Y Bool) (s : Turn) (d : ℕ) :
    PreservesInternal P (padTree P s d) := by
  induction d generalizing P s with
  | zero => exact preservesInternal_refl P
  | succ d ih =>
      cases P with
      | leaf b => trivial
      | aNode a l r => exact ⟨rfl, ih l .bob, ih r .bob⟩
      | bNode b l r => exact ⟨rfl, ih l .alice, ih r .alice⟩

theorem padTree_alternates (P : Protocol X Y Bool) (s : Turn) (d : ℕ)
    (h : Alternates s P) : Alternates s (padTree P s d) := by
  induction d generalizing P s with
  | zero => exact h
  | succ d ih =>
      cases P with
      | leaf b => cases s <;> exact ⟨ih _ _ trivial, ih _ _ trivial⟩
      | aNode a l r =>
          cases s with
          | alice => exact ⟨ih l .bob h.1, ih r .bob h.2⟩
          | bob => exact False.elim h
      | bNode b l r =>
          cases s with
          | alice => exact False.elim h
          | bob => exact ⟨ih l .alice h.1, ih r .alice h.2⟩

theorem padTree_isComplete (P : Protocol X Y Bool) (s : Turn) (d : ℕ)
    (hcost : P.cost ≤ d) : IsComplete (padTree P s d) d := by
  induction d generalizing P s with
  | zero => cases P <;> simp_all [Protocol.cost, padTree, IsComplete]
  | succ d ih =>
      cases P with
      | leaf b =>
          cases s <;> exact ⟨ih _ _ (Nat.zero_le d), ih _ _ (Nat.zero_le d)⟩
      | aNode a l r =>
          have hl : l.cost ≤ d := by simp only [Protocol.cost] at hcost; omega
          have hr : r.cost ≤ d := by simp only [Protocol.cost] at hcost; omega
          exact ⟨ih l .bob hl, ih r .bob hr⟩
      | bNode b l r =>
          have hl : l.cost ≤ d := by simp only [Protocol.cost] at hcost; omega
          have hr : r.cost ≤ d := by simp only [Protocol.cost] at hcost; omega
          exact ⟨ih l .alice hl, ih r .alice hr⟩

namespace StrictProtocol

def pad {s : Turn} (P : StrictProtocol X Y s) (d : ℕ) : StrictProtocol X Y s :=
  ⟨padTree P.toProtocol s d, padTree_alternates _ _ _ P.alternates⟩

theorem pad_eval {s : Turn} (P : StrictProtocol X Y s) (d : ℕ) (x : X) (y : Y) :
    (P.pad d).eval x y = P.eval x y := padTree_eval _ _ _ _ _

theorem pad_isComplete {s : Turn} (P : StrictProtocol X Y s) (d : ℕ) (h : P.cost ≤ d) :
    IsComplete (P.pad d).toProtocol d := padTree_isComplete _ _ _ h

theorem pad_cost {s : Turn} (P : StrictProtocol X Y s) (d : ℕ) (h : P.cost ≤ d) :
    (P.pad d).cost = d := (P.pad_isComplete d h).cost_eq

theorem pad_computes {s : Turn} (P : StrictProtocol X Y s) (d : ℕ)
    {F : X → Y → Bool} (h : P.Computes F) : (P.pad d).Computes F := by
  intro x y
  rw [pad_eval]
  exact h x y

theorem pad_preservesInternal {s : Turn} (P : StrictProtocol X Y s) (d : ℕ) :
    PreservesInternal P.toProtocol (P.pad d).toProtocol := padTree_preservesInternal _ _ _

end StrictProtocol

/-- Keep exactly the first `k` message levels and erase outputs. Equality
of these prefixes means literal equality on all hypothetical transcripts,
not only equality of messages along realized input paths. -/
def messagePrefix : ℕ → Protocol X Y Bool → Protocol X Y Unit
  | 0, _ => .leaf ()
  | _ + 1, .leaf _ => .leaf ()
  | k + 1, .aNode a l r => .aNode a (messagePrefix k l) (messagePrefix k r)
  | k + 1, .bNode b l r => .bNode b (messagePrefix k l) (messagePrefix k r)

/-- At the final message level, send the output selected by the old bit,
then use canonical false/true leaves. Noncomplete depth-one trees are left
unchanged; the normal-form theorem explicitly requires completeness. -/
def normalizeTree : ℕ → Protocol X Y Bool → Protocol X Y Bool
  | 0, P => P
  | _ + 1, .leaf b => .leaf b
  | 1, .aNode a (.leaf b0) (.leaf b1) =>
      .aNode (fun x => if a x then b1 else b0) (.leaf false) (.leaf true)
  | 1, .bNode b (.leaf b0) (.leaf b1) =>
      .bNode (fun y => if b y then b1 else b0) (.leaf false) (.leaf true)
  | 1, P => P
  | d + 2, .aNode a l r => .aNode a (normalizeTree (d + 1) l) (normalizeTree (d + 1) r)
  | d + 2, .bNode b l r => .bNode b (normalizeTree (d + 1) l) (normalizeTree (d + 1) r)

/-- Every final syntactic node has zero and one as its two leaf labels.
There is deliberately no depth-zero instance: no bit has then been sent. -/
def CanonicalLastLeaves : ℕ → Protocol X Y Bool → Prop
  | 1, .aNode _ l r => l = .leaf false ∧ r = .leaf true
  | 1, .bNode _ l r => l = .leaf false ∧ r = .leaf true
  | d + 2, .aNode _ l r => CanonicalLastLeaves (d + 1) l ∧ CanonicalLastLeaves (d + 1) r
  | d + 2, .bNode _ l r => CanonicalLastLeaves (d + 1) l ∧ CanonicalLastLeaves (d + 1) r
  | _, _ => False

theorem normalizeTree_messagePrefix (d : ℕ) (P : Protocol X Y Bool) :
    messagePrefix d (normalizeTree (d + 1) P) = messagePrefix d P := by
  induction d generalizing P with
  | zero => rfl
  | succ d ih =>
      cases P <;> simp [normalizeTree, messagePrefix, ih]

theorem normalizeTree_eval (d : ℕ) (P : Protocol X Y Bool)
    (h : IsComplete P d) (x : X) (y : Y) :
    (normalizeTree d P).eval x y = P.eval x y := by
  induction d generalizing P with
  | zero => rfl
  | succ d ih =>
      cases P with
      | leaf b => exact False.elim h
      | aNode a l r =>
          cases d with
          | zero =>
              obtain ⟨b0, rfl⟩ := (IsComplete.zero_iff l).mp h.1
              obtain ⟨b1, rfl⟩ := (IsComplete.zero_iff r).mp h.2
              simp [normalizeTree, Protocol.eval]
          | succ d => simp [normalizeTree, Protocol.eval, ih _ h.1, ih _ h.2]
      | bNode b l r =>
          cases d with
          | zero =>
              obtain ⟨b0, rfl⟩ := (IsComplete.zero_iff l).mp h.1
              obtain ⟨b1, rfl⟩ := (IsComplete.zero_iff r).mp h.2
              simp [normalizeTree, Protocol.eval]
          | succ d => simp [normalizeTree, Protocol.eval, ih _ h.1, ih _ h.2]

theorem normalizeTree_isComplete (d : ℕ) (P : Protocol X Y Bool)
    (h : IsComplete P d) : IsComplete (normalizeTree d P) d := by
  induction d generalizing P with
  | zero => exact h
  | succ d ih =>
      cases P with
      | leaf b => exact False.elim h
      | aNode a l r =>
          cases d with
          | zero =>
              obtain ⟨b0, rfl⟩ := (IsComplete.zero_iff l).mp h.1
              obtain ⟨b1, rfl⟩ := (IsComplete.zero_iff r).mp h.2
              exact ⟨trivial, trivial⟩
          | succ d => simpa only [normalizeTree, IsComplete] using And.intro (ih l h.1) (ih r h.2)
      | bNode b l r =>
          cases d with
          | zero =>
              obtain ⟨b0, rfl⟩ := (IsComplete.zero_iff l).mp h.1
              obtain ⟨b1, rfl⟩ := (IsComplete.zero_iff r).mp h.2
              exact ⟨trivial, trivial⟩
          | succ d => simpa only [normalizeTree, IsComplete] using And.intro (ih l h.1) (ih r h.2)

theorem normalizeTree_alternates (d : ℕ) (P : Protocol X Y Bool) (s : Turn)
    (hc : IsComplete P d) (ha : Alternates s P) : Alternates s (normalizeTree d P) := by
  induction d generalizing P s with
  | zero => exact ha
  | succ d ih =>
      cases P with
      | leaf b => exact False.elim hc
      | aNode a l r =>
          cases s with
          | bob => exact False.elim ha
          | alice =>
              cases d with
              | zero =>
                  obtain ⟨b0, rfl⟩ := (IsComplete.zero_iff l).mp hc.1
                  obtain ⟨b1, rfl⟩ := (IsComplete.zero_iff r).mp hc.2
                  exact ⟨trivial, trivial⟩
              | succ d =>
                  simpa only [normalizeTree, Alternates] using
                    And.intro (ih l .bob hc.1 ha.1) (ih r .bob hc.2 ha.2)
      | bNode b l r =>
          cases s with
          | alice => exact False.elim ha
          | bob =>
              cases d with
              | zero =>
                  obtain ⟨b0, rfl⟩ := (IsComplete.zero_iff l).mp hc.1
                  obtain ⟨b1, rfl⟩ := (IsComplete.zero_iff r).mp hc.2
                  exact ⟨trivial, trivial⟩
              | succ d =>
                  simpa only [normalizeTree, Alternates] using
                    And.intro (ih l .alice hc.1 ha.1) (ih r .alice hc.2 ha.2)

theorem normalizeTree_canonical (d : ℕ) (P : Protocol X Y Bool)
    (h : IsComplete P (d + 1)) : CanonicalLastLeaves (d + 1) (normalizeTree (d + 1) P) := by
  induction d generalizing P with
  | zero =>
      cases P with
      | leaf b => exact False.elim h
      | aNode a l r =>
          obtain ⟨b0, rfl⟩ := (IsComplete.zero_iff l).mp h.1
          obtain ⟨b1, rfl⟩ := (IsComplete.zero_iff r).mp h.2
          exact ⟨rfl, rfl⟩
      | bNode b l r =>
          obtain ⟨b0, rfl⟩ := (IsComplete.zero_iff l).mp h.1
          obtain ⟨b1, rfl⟩ := (IsComplete.zero_iff r).mp h.2
          exact ⟨rfl, rfl⟩
  | succ d ih =>
      cases P with
      | leaf b => exact False.elim h
      | aNode a l r =>
          simpa only [normalizeTree, CanonicalLastLeaves] using And.intro (ih l h.1) (ih r h.2)
      | bNode b l r =>
          simpa only [normalizeTree, CanonicalLastLeaves] using And.intro (ih l h.1) (ih r h.2)

/-- The last bit actually transmitted; absent precisely at a reached root leaf. -/
def lastSent : Protocol X Y Bool → X → Y → Option Bool
  | .leaf _, _, _ => none
  | .aNode a l r, x, y =>
      match (if a x then lastSent r x y else lastSent l x y) with
      | some b => some b
      | none => some (a x)
  | .bNode b l r, x, y =>
      match (if b y then lastSent r x y else lastSent l x y) with
      | some c => some c
      | none => some (b y)

theorem CanonicalLastLeaves.lastSent_eq {d : ℕ} {P : Protocol X Y Bool}
    (h : CanonicalLastLeaves (d + 1) P) (x : X) (y : Y) :
    lastSent P x y = some (P.eval x y) := by
  induction d generalizing P with
  | zero =>
      cases P with
      | leaf b => exact False.elim h
      | aNode a l r =>
          rcases h with ⟨rfl, rfl⟩
          cases ha : a x <;> simp [lastSent, Protocol.eval, ha]
      | bNode b l r =>
          rcases h with ⟨rfl, rfl⟩
          cases hb : b y <;> simp [lastSent, Protocol.eval, hb]
  | succ d ih =>
      cases P with
      | leaf b => exact False.elim h
      | aNode a l r =>
          cases ha : a x <;> simp [lastSent, Protocol.eval, ha, ih h.1, ih h.2]
      | bNode b l r =>
          cases hb : b y <;> simp [lastSent, Protocol.eval, hb, ih h.1, ih h.2]

namespace StrictProtocol

/-- Normalise the last message of a complete tree. The original tree itself,
not a stipulated communication bound, determines every new local message. -/
def normalize {s : Turn} (P : StrictProtocol X Y s) (d : ℕ)
    (hc : IsComplete P.toProtocol d) : StrictProtocol X Y s :=
  ⟨normalizeTree d P.toProtocol, normalizeTree_alternates _ _ _ hc P.alternates⟩

theorem normalize_eval {s : Turn} (P : StrictProtocol X Y s) (d : ℕ)
    (hc : IsComplete P.toProtocol d) (x : X) (y : Y) :
    (P.normalize d hc).eval x y = P.eval x y := normalizeTree_eval _ _ hc x y

theorem normalize_isComplete {s : Turn} (P : StrictProtocol X Y s) (d : ℕ)
    (hc : IsComplete P.toProtocol d) : IsComplete (P.normalize d hc).toProtocol d :=
  normalizeTree_isComplete _ _ hc

theorem normalize_cost {s : Turn} (P : StrictProtocol X Y s) (d : ℕ)
    (hc : IsComplete P.toProtocol d) : (P.normalize d hc).cost = P.cost :=
  (P.normalize_isComplete d hc).cost_eq.trans hc.cost_eq.symm

theorem normalize_canonical {s : Turn} (P : StrictProtocol X Y s) (d : ℕ)
    (hc : IsComplete P.toProtocol (d + 1)) :
    CanonicalLastLeaves (d + 1) (P.normalize (d + 1) hc).toProtocol :=
  normalizeTree_canonical _ _ hc

theorem normalize_messagePrefix {s : Turn} (P : StrictProtocol X Y s) (d : ℕ)
    (hc : IsComplete P.toProtocol (d + 1)) :
    messagePrefix d (P.normalize (d + 1) hc).toProtocol = messagePrefix d P.toProtocol :=
  normalizeTree_messagePrefix _ _

/-- Combined padding and normalisation used before the payload union bound.
It is valid for either starter and every strictly positive target depth. -/
theorem exists_complete_normalized {s : Turn} (P : StrictProtocol X Y s) (d : ℕ)
    (hcost : P.cost ≤ d + 1) :
    ∃ Q : StrictProtocol X Y s,
      IsComplete Q.toProtocol (d + 1) ∧ Q.cost = d + 1 ∧
      CanonicalLastLeaves (d + 1) Q.toProtocol ∧
      messagePrefix d Q.toProtocol = messagePrefix d (P.pad (d + 1)).toProtocol ∧
      ∀ x y, Q.eval x y = P.eval x y := by
  let R := P.pad (d + 1)
  have hc : IsComplete R.toProtocol (d + 1) := P.pad_isComplete _ hcost
  refine ⟨R.normalize (d + 1) hc, R.normalize_isComplete _ hc,
    (R.normalize_isComplete _ hc).cost_eq, R.normalize_canonical d hc,
    R.normalize_messagePrefix d hc, ?_⟩
  intro x y
  exact (R.normalize_eval _ hc x y).trans (P.pad_eval _ x y)

end StrictProtocol

/-! ## Boundary and unreachable-branch examples -/

theorem depth_zero_no_last_message (b : Bool) (x : X) (y : Y) :
    padTree (.leaf b : Protocol X Y Bool) .alice 0 = .leaf b ∧
      normalizeTree 0 (.leaf b : Protocol X Y Bool) = .leaf b ∧
      lastSent (.leaf b) x y = none := ⟨rfl, rfl, rfl⟩

/-- Equal old outputs produce a constant last message, but both canonical
leaves remain in the new tree, including the unreachable opposite leaf. -/
theorem normalize_equal_leaf_labels (a : X → Bool) (b : Bool) :
    normalizeTree 1 (.aNode a (.leaf b) (.leaf b) : Protocol X Y Bool) =
      .aNode (fun _ => b) (.leaf false) (.leaf true) := by
  simp [normalizeTree]

/-- A zero-bit constant can be padded to one bit; the opposite branch remains
syntactically present even though a constant dummy message cannot reach it. -/
theorem constant_pad_one (b : Bool) :
    padTree (.leaf b : Protocol X Y Bool) .alice 1 =
      .aNode (fun _ => false) (.leaf b) (.leaf b) := rfl

end Paper2.Yao
