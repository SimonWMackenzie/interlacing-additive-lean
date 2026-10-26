import Workspace.UpperBound

/-!
# Strictly alternating public-output protocols

Statement source: Paper 2, `2026-09-22-protocol-labels-v12`, Section 7,
`yao:model` / `def:yao-model` / `yao:conventions` and `yao:comparison`.

The trees here are the actual `Workspace.Types.Protocol.Protocol` trees.
The recursive `Alternates` predicate checks the speaker at every internal
node, including unreachable nodes; the transcript alone determines stopping,
and every leaf has a fixed public Boolean output. This is not the unrelated
`Workspace.Types.AlternatingGame` family of matrices.

No hardness theorem is proved in this module. The definitions and comparison
lemmas fix the model that such a theorem must use.
-/

namespace Paper2.Yao

open Workspace.Types.Protocol Workspace.Types.CommComplexity

/-- The publicly fixed player scheduled to send the next charged bit. -/
inductive Turn where
  | alice
  | bob
  deriving DecidableEq, Fintype

namespace Turn

def other : Turn → Turn
  | alice => bob
  | bob => alice

@[simp] theorem other_other (s : Turn) : s.other.other = s := by cases s <;> rfl

end Turn

universe u v
variable {X : Type u} {Y : Type v}

/-- Local recursive check of strict alternation. A leaf can occur at any
public transcript; its constant label is independent of both private inputs. -/
def Alternates : Turn → Protocol X Y Bool → Prop
  | _, .leaf _ => True
  | .alice, .aNode _ l r => Alternates .bob l ∧ Alternates .bob r
  | .bob, .bNode _ l r => Alternates .alice l ∧ Alternates .alice r
  | .alice, .bNode _ _ _ => False
  | .bob, .aNode _ _ _ => False

/-- A concrete deterministic binary protocol with a fixed starter and
strictly alternating speakers. Its representation retains the full tree. -/
structure StrictProtocol (X : Type u) (Y : Type v) (starter : Turn) where
  toProtocol : Protocol X Y Bool
  alternates : Alternates starter toProtocol

namespace StrictProtocol

variable {s : Turn}

def cost (P : StrictProtocol X Y s) : ℕ := P.toProtocol.cost

def eval (P : StrictProtocol X Y s) (x : X) (y : Y) : Bool :=
  P.toProtocol.eval x y

def Computes (P : StrictProtocol X Y s) (F : X → Y → Bool) : Prop :=
  ∀ x y, P.eval x y = F x y

theorem toProtocol_cost (P : StrictProtocol X Y s) :
    P.toProtocol.cost = P.cost := rfl

theorem toProtocol_eval (P : StrictProtocol X Y s) (x : X) (y : Y) :
    P.toProtocol.eval x y = P.eval x y := rfl

@[simp] theorem toProtocol_computes (P : StrictProtocol X Y s) (F : X → Y → Bool) :
    P.toProtocol.Computes F ↔ P.Computes F := Iff.rfl

def leaf (s : Turn) (b : Bool) : StrictProtocol X Y s := ⟨.leaf b, trivial⟩

def alice (a : X → Bool) (l r : StrictProtocol X Y .bob) :
    StrictProtocol X Y .alice :=
  ⟨.aNode a l.toProtocol r.toProtocol, l.alternates, r.alternates⟩

def bob (b : Y → Bool) (l r : StrictProtocol X Y .alice) :
    StrictProtocol X Y .bob :=
  ⟨.bNode b l.toProtocol r.toProtocol, l.alternates, r.alternates⟩

/-- Send a charged dummy zero before running the original tree. The starter
changes globally, not as a function of the input. Both subtrees are retained. -/
def prependDummy {s : Turn} (P : StrictProtocol X Y s) :
    StrictProtocol X Y s.other :=
  match s with
  | .alice => bob (fun _ => false) P P
  | .bob => alice (fun _ => false) P P

@[simp] theorem prependDummy_cost {s : Turn} (P : StrictProtocol X Y s) :
    P.prependDummy.cost = P.cost + 1 := by
  cases s <;> simp [prependDummy, alice, bob, cost, Protocol.cost, Nat.add_comm]

@[simp] theorem prependDummy_eval {s : Turn} (P : StrictProtocol X Y s)
    (x : X) (y : Y) : P.prependDummy.eval x y = P.eval x y := by
  cases s <;> rfl

theorem prependDummy_computes {s : Turn} (P : StrictProtocol X Y s)
    {F : X → Y → Bool} (h : P.Computes F) : P.prependDummy.Computes F := by
  intro x y
  simpa using h x y

end StrictProtocol

/-- Insert dummy bits whenever an unrestricted node is not scheduled.
This is the concrete factor-two simulation mentioned before `yao:model`. -/
def alternateTree : Protocol X Y Bool → Turn → Protocol X Y Bool
  | .leaf b, _ => .leaf b
  | .aNode a l r, .alice =>
      .aNode a (alternateTree l .bob) (alternateTree r .bob)
  | .aNode a l r, .bob =>
      let Q := Protocol.aNode a (alternateTree l .bob) (alternateTree r .bob)
      .bNode (fun _ => false) Q Q
  | .bNode b l r, .bob =>
      .bNode b (alternateTree l .alice) (alternateTree r .alice)
  | .bNode b l r, .alice =>
      let Q := Protocol.bNode b (alternateTree l .alice) (alternateTree r .alice)
      .aNode (fun _ => false) Q Q

theorem alternateTree_alternates (P : Protocol X Y Bool) (s : Turn) :
    Alternates s (alternateTree P s) := by
  induction P generalizing s with
  | leaf b => cases s <;> trivial
  | aNode a l r ihl ihr => cases s <;> simp [alternateTree, Alternates, ihl, ihr]
  | bNode b l r ihl ihr => cases s <;> simp [alternateTree, Alternates, ihl, ihr]

theorem alternateTree_eval (P : Protocol X Y Bool) (s : Turn) (x : X) (y : Y) :
    (alternateTree P s).eval x y = P.eval x y := by
  induction P generalizing s with
  | leaf b => cases s <;> rfl
  | aNode a l r ihl ihr => cases s <;> simp [alternateTree, Protocol.eval, ihl, ihr]
  | bNode b l r ihl ihr => cases s <;> simp [alternateTree, Protocol.eval, ihl, ihr]

theorem alternateTree_cost_le (P : Protocol X Y Bool) (s : Turn) :
    (alternateTree P s).cost ≤ 2 * P.cost := by
  induction P generalizing s with
  | leaf b => cases s <;> simp [alternateTree, Protocol.cost]
  | aNode a l r ihl ihr =>
      have hl := ihl Turn.bob
      have hr := ihr Turn.bob
      cases s <;> simp only [alternateTree, Protocol.cost, max_self] <;> omega
  | bNode b l r ihl ihr =>
      have hl := ihl Turn.alice
      have hr := ihr Turn.alice
      cases s <;> simp only [alternateTree, Protocol.cost, max_self] <;> omega

def alternate (P : Protocol X Y Bool) (s : Turn) : StrictProtocol X Y s :=
  ⟨alternateTree P s, alternateTree_alternates P s⟩

@[simp] theorem alternate_eval (P : Protocol X Y Bool) (s : Turn) (x : X) (y : Y) :
    (alternate P s).eval x y = P.eval x y := alternateTree_eval P s x y

theorem alternate_cost_le (P : Protocol X Y Bool) (s : Turn) :
    (alternate P s).cost ≤ 2 * P.cost := alternateTree_cost_le P s

/-- Exact achievable costs, rather than a stipulated complexity contract. -/
def Achievable (s : Turn) (F : X → Y → Bool) : Set ℕ :=
  {c | ∃ P : StrictProtocol X Y s, P.cost = c ∧ P.Computes F}

/-- Minimum strictly alternating public-output depth with the fixed starter. -/
noncomputable def Dalt (s : Turn) [Fintype X] [Fintype Y] (F : X → Y → Bool) : ℕ :=
  sInf (Achievable s F)

theorem achievable_nonempty [Fintype X] [Fintype Y] (s : Turn) (F : X → Y → Bool) :
    (Achievable s F).Nonempty := by
  obtain ⟨c, P, _, hP⟩ := Workspace.UpperBound.AchievableCosts_nonempty F
  refine ⟨(alternate P s).cost, alternate P s, rfl, ?_⟩
  intro x y
  simpa using hP x y

theorem exists_optimal [Fintype X] [Fintype Y] (s : Turn) (F : X → Y → Bool) :
    ∃ P : StrictProtocol X Y s, P.cost = Dalt s F ∧ P.Computes F :=
  Nat.sInf_mem (achievable_nonempty s F)

theorem Dalt_le_cost [Fintype X] [Fintype Y] {s : Turn}
    (P : StrictProtocol X Y s) {F : X → Y → Bool} (hP : P.Computes F) :
    Dalt s F ≤ P.cost := Nat.sInf_le ⟨P, rfl, hP⟩

/-- Source `yao:comparison`: a dummy first bit switches the starter. -/
theorem Dalt_other_le [Fintype X] [Fintype Y] (s : Turn) (F : X → Y → Bool) :
    Dalt s.other F ≤ Dalt s F + 1 := by
  obtain ⟨P, hcost, hP⟩ := exists_optimal s F
  calc
    Dalt s.other F ≤ P.prependDummy.cost := Dalt_le_cost _ (P.prependDummy_computes hP)
    _ = Dalt s F + 1 := by rw [StrictProtocol.prependDummy_cost, hcost]

theorem starter_comparison [Fintype X] [Fintype Y] (F : X → Y → Bool) :
    Dalt .alice F ≤ Dalt .bob F + 1 ∧ Dalt .bob F ≤ Dalt .alice F + 1 :=
  ⟨Dalt_other_le .bob F, Dalt_other_le .alice F⟩

/-- The first inequality in `yao:comparison`, stated with an integer absolute
value so natural subtraction cannot silently truncate the difference. -/
theorem starter_abs_difference_le [Fintype X] [Fintype Y] (F : X → Y → Bool) :
    |(Dalt .alice F : ℤ) - (Dalt .bob F : ℤ)| ≤ 1 := by
  obtain ⟨hAB, hBA⟩ := starter_comparison F
  rw [abs_le]
  constructor <;> omega

/-- The starter is minimized once per protocol, never per input. -/
noncomputable def Dfree [Fintype X] [Fintype Y] (F : X → Y → Bool) : ℕ :=
  min (Dalt .alice F) (Dalt .bob F)

theorem free_starter_comparison [Fintype X] [Fintype Y] (F : X → Y → Bool) :
    Dfree F ≤ Dalt .alice F ∧ Dalt .alice F ≤ Dfree F + 1 := by
  obtain ⟨hAB, _⟩ := starter_comparison F
  simp only [Dfree]
  constructor
  · exact min_le_left _ _
  · omega

/-- Forgetting the schedule preserves every message and fixed leaf output. -/
theorem unrestricted_le_Dalt [Fintype X] [Fintype Y]
    (s : Turn) (F : X → Y → Bool) : D F ≤ Dalt s F := by
  obtain ⟨P, hcost, hP⟩ := exists_optimal s F
  apply Nat.sInf_le
  exact ⟨P.toProtocol, hcost, hP⟩

theorem Dalt_le_twice_unrestricted [Fintype X] [Fintype Y]
    (s : Turn) (F : X → Y → Bool) : Dalt s F ≤ 2 * D F := by
  obtain ⟨P, hcost, hP⟩ := Nat.sInf_mem (Workspace.UpperBound.AchievableCosts_nonempty F)
  calc
    Dalt s F ≤ (alternate P s).cost := Dalt_le_cost _ (by intro x y; simpa using hP x y)
    _ ≤ 2 * P.cost := alternate_cost_le P s
    _ = 2 * D F := by rw [hcost]; rfl

/-! ## Receiver outputs and the depth-zero convention

Source: `yao:receiver-section` and `yao:comparison`. At a positive-depth
terminal transcript the receiver of the last message is the next scheduled
speaker. At depth zero there is no last message: the full protocol explicitly
designates Alice or Bob as the output player. Private data determine the
answer, but never determine whether the protocol has stopped.
-/

variable {X Y : Type u}

/-- A player's own input type. -/
def LocalInput (X Y : Type u) : Turn → Type u
  | .alice => X
  | .bob => Y

def localInput (s : Turn) (x : X) (y : Y) : LocalInput X Y s :=
  match s with
  | .alice => x
  | .bob => y

/-- A receiver-output continuation. Its index is the next scheduled speaker;
at a terminal node this is the receiver of the preceding charged message.
The full protocol below handles depth zero separately. -/
inductive ReceiverTree (X Y : Type u) : Turn → Type u where
  | leaf {s : Turn} (answer : LocalInput X Y s → Bool) : ReceiverTree X Y s
  | send {s : Turn} (message : LocalInput X Y s → Bool)
      (l r : ReceiverTree X Y s.other) : ReceiverTree X Y s

namespace ReceiverTree

def cost {s : Turn} : ReceiverTree X Y s → ℕ
  | .leaf _ => 0
  | .send _ l r => 1 + max l.cost r.cost

def eval {s : Turn} : ReceiverTree X Y s → X → Y → Bool
  | .leaf answer, x, y => answer (localInput s x y)
  | .send message l r, x, y =>
      if message (localInput s x y) then r.eval x y else l.eval x y

/-- Append one answer bit at each publicly determined terminal transcript.
This bit is sent by the next scheduled player, so alternation is preserved. -/
def publicize : {s : Turn} → ReceiverTree X Y s → StrictProtocol X Y s
  | .alice, .leaf answer =>
      StrictProtocol.alice answer (StrictProtocol.leaf .bob false) (StrictProtocol.leaf .bob true)
  | .bob, .leaf answer =>
      StrictProtocol.bob answer (StrictProtocol.leaf .alice false) (StrictProtocol.leaf .alice true)
  | .alice, .send message l r => StrictProtocol.alice message l.publicize r.publicize
  | .bob, .send message l r => StrictProtocol.bob message l.publicize r.publicize

theorem publicize_cost {s : Turn} (T : ReceiverTree X Y s) :
    T.publicize.cost = T.cost + 1 := by
  induction T with
  | @leaf s answer => cases s <;> rfl
  | @send s message l r ihl ihr =>
      cases s <;>
        simp only [publicize, StrictProtocol.alice, StrictProtocol.bob,
          StrictProtocol.cost, Protocol.cost, cost] at * <;> omega

theorem publicize_eval {s : Turn} (T : ReceiverTree X Y s) (x : X) (y : Y) :
    T.publicize.eval x y = T.eval x y := by
  induction T with
  | @leaf s answer =>
      cases s <;>
        simp [publicize, StrictProtocol.eval, StrictProtocol.alice, StrictProtocol.bob,
          StrictProtocol.leaf, Protocol.eval, eval, localInput]
  | @send s message l r ihl ihr =>
      cases s <;>
        simp only [publicize, StrictProtocol.alice, StrictProtocol.bob,
          StrictProtocol.eval, Protocol.eval, eval, localInput] at * <;>
        split <;> assumption

/-- A fixed public leaf can also be read by the terminal receiver. -/
def ofPublic : (s : Turn) → (P : Protocol X Y Bool) →
    Alternates s P → ReceiverTree X Y s
  | _, .leaf b, _ => .leaf (fun _ => b)
  | .alice, .aNode a l r, h =>
      .send a (ofPublic .bob l h.1) (ofPublic .bob r h.2)
  | .bob, .bNode b l r, h =>
      .send b (ofPublic .alice l h.1) (ofPublic .alice r h.2)
  | .alice, .bNode _ _ _, h => False.elim h
  | .bob, .aNode _ _ _, h => False.elim h

theorem ofPublic_cost (s : Turn) (P : Protocol X Y Bool) (h : Alternates s P) :
    (ofPublic s P h).cost = P.cost := by
  induction P generalizing s with
  | leaf b => rfl
  | aNode a l r ihl ihr =>
      cases s with
      | alice =>
          change 1 + max (ofPublic .bob l h.1).cost (ofPublic .bob r h.2).cost =
            1 + max l.cost r.cost
          rw [ihl .bob h.1, ihr .bob h.2]
      | bob => exact False.elim h
  | bNode b l r ihl ihr =>
      cases s with
      | alice => exact False.elim h
      | bob =>
          change 1 + max (ofPublic .alice l h.1).cost (ofPublic .alice r h.2).cost =
            1 + max l.cost r.cost
          rw [ihl .alice h.1, ihr .alice h.2]

theorem ofPublic_eval (s : Turn) (P : Protocol X Y Bool) (h : Alternates s P)
    (x : X) (y : Y) : (ofPublic s P h).eval x y = P.eval x y := by
  induction P generalizing s with
  | leaf b => rfl
  | aNode a l r ihl ihr =>
      cases s with
      | alice =>
          change (if a x then (ofPublic .bob r h.2).eval x y else
            (ofPublic .bob l h.1).eval x y) = if a x then r.eval x y else l.eval x y
          rw [ihl .bob h.1, ihr .bob h.2]
      | bob => exact False.elim h
  | bNode b l r ihl ihr =>
      cases s with
      | alice => exact False.elim h
      | bob =>
          change (if b y then (ofPublic .alice r h.2).eval x y else
            (ofPublic .alice l h.1).eval x y) = if b y then r.eval x y else l.eval x y
          rw [ihl .alice h.1, ihr .alice h.2]

end ReceiverTree

/-- A receiver-output protocol with either publicly chosen starter. A
zero-message protocol explicitly chooses an output player; in a positive
protocol each child is indexed by the receiver of the first message. -/
inductive ReceiverProtocol (X Y : Type u) : Type u where
  | zero (outputPlayer : Turn) (answer : LocalInput X Y outputPlayer → Bool)
  | positive (starter : Turn) (message : LocalInput X Y starter → Bool)
      (l r : ReceiverTree X Y starter.other)

namespace ReceiverProtocol

def cost : ReceiverProtocol X Y → ℕ
  | .zero _ _ => 0
  | .positive _ _ l r => 1 + max l.cost r.cost

def eval : ReceiverProtocol X Y → X → Y → Bool
  | .zero p answer, x, y => answer (localInput p x y)
  | .positive s message l r, x, y =>
      if message (localInput s x y) then r.eval x y else l.eval x y

def Computes (P : ReceiverProtocol X Y) (F : X → Y → Bool) : Prop :=
  ∀ x y, P.eval x y = F x y

/-- At the root, reinterpret a continuation's terminal case using the
explicit designated-output-player convention. -/
def ofTree {s : Turn} : ReceiverTree X Y s → ReceiverProtocol X Y
  | .leaf answer => .zero s answer
  | .send message l r => .positive s message l r

@[simp] theorem ofTree_cost {s : Turn} (T : ReceiverTree X Y s) :
    (ofTree T).cost = T.cost := by cases T <;> rfl

@[simp] theorem ofTree_eval {s : Turn} (T : ReceiverTree X Y s) (x : X) (y : Y) :
    (ofTree T).eval x y = T.eval x y := by cases T <;> rfl

/-- The starter of publicisation: the original starter at positive depth,
or the designated output player at depth zero. -/
def publicStarter : ReceiverProtocol X Y → Turn
  | .zero p _ => p
  | .positive s _ _ _ => s

def publicize (P : ReceiverProtocol X Y) : StrictProtocol X Y P.publicStarter :=
  match P with
  | .zero p answer => ReceiverTree.publicize (.leaf answer : ReceiverTree X Y p)
  | .positive s message l r =>
      ReceiverTree.publicize (.send message l r : ReceiverTree X Y s)

theorem publicize_cost (P : ReceiverProtocol X Y) :
    P.publicize.cost = P.cost + 1 := by
  cases P with
  | zero p answer => exact ReceiverTree.publicize_cost (.leaf answer)
  | positive s message l r => exact ReceiverTree.publicize_cost (.send message l r)

theorem publicize_eval (P : ReceiverProtocol X Y) (x : X) (y : Y) :
    P.publicize.eval x y = P.eval x y := by
  cases P with
  | zero p answer => exact ReceiverTree.publicize_eval (.leaf answer) x y
  | positive s message l r => exact ReceiverTree.publicize_eval (.send message l r) x y

def ofPublic {s : Turn} (P : StrictProtocol X Y s) : ReceiverProtocol X Y :=
  ofTree (ReceiverTree.ofPublic s P.toProtocol P.alternates)

@[simp] theorem ofPublic_cost {s : Turn} (P : StrictProtocol X Y s) :
    (ofPublic P).cost = P.cost := by
  simp [ofPublic, ReceiverTree.ofPublic_cost, StrictProtocol.cost]

@[simp] theorem ofPublic_eval {s : Turn} (P : StrictProtocol X Y s) (x : X) (y : Y) :
    (ofPublic P).eval x y = P.eval x y := by
  simp [ofPublic, ReceiverTree.ofPublic_eval, StrictProtocol.eval]

end ReceiverProtocol

def ReceiverAchievable (F : X → Y → Bool) : Set ℕ :=
  {c | ∃ P : ReceiverProtocol X Y, P.cost = c ∧ P.Computes F}

/-- Yao's free-starter receiver-output cost, including designated output
players at depth zero. The existential choice of tree precedes all inputs. -/
noncomputable def Yfree [Fintype X] [Fintype Y] (F : X → Y → Bool) : ℕ :=
  sInf (ReceiverAchievable F)

theorem receiver_achievable_nonempty [Fintype X] [Fintype Y] (F : X → Y → Bool) :
    (ReceiverAchievable F).Nonempty := by
  obtain ⟨P, _, hP⟩ := exists_optimal .alice F
  refine ⟨(ReceiverProtocol.ofPublic P).cost, ReceiverProtocol.ofPublic P, rfl, ?_⟩
  intro x y
  simpa using hP x y

theorem exists_receiver_optimal [Fintype X] [Fintype Y] (F : X → Y → Bool) :
    ∃ P : ReceiverProtocol X Y, P.cost = Yfree F ∧ P.Computes F :=
  Nat.sInf_mem (receiver_achievable_nonempty F)

theorem Yfree_le_Dalt [Fintype X] [Fintype Y] (s : Turn) (F : X → Y → Bool) :
    Yfree F ≤ Dalt s F := by
  obtain ⟨P, hcost, hP⟩ := exists_optimal s F
  apply Nat.sInf_le
  refine ⟨ReceiverProtocol.ofPublic P, ?_, ?_⟩
  · simpa using hcost
  · intro x y; simpa using hP x y

theorem Yfree_le_Dfree [Fintype X] [Fintype Y] (F : X → Y → Bool) :
    Yfree F ≤ Dfree F := le_min (Yfree_le_Dalt .alice F) (Yfree_le_Dalt .bob F)

/-- Source `yao:comparison`: the receiver sends its answer in one bit.
Depth zero is included by choosing the designated output player as starter. -/
theorem Dfree_le_Yfree_add_one [Fintype X] [Fintype Y] (F : X → Y → Bool) :
    Dfree F ≤ Yfree F + 1 := by
  obtain ⟨P, hcost, hP⟩ := exists_receiver_optimal F
  have hp : P.publicize.Computes F := by
    intro x y
    rw [ReceiverProtocol.publicize_eval]
    exact hP x y
  have hb := Dalt_le_cost P.publicize hp
  rw [ReceiverProtocol.publicize_cost, hcost] at hb
  cases hs : P.publicStarter with
  | alice => exact le_trans (min_le_left _ _) (by simpa [hs] using hb)
  | bob => exact le_trans (min_le_right _ _) (by simpa [hs] using hb)

/-- The second inequality of source `yao:comparison`, stated without
truncated subtraction: receiver output saves at most two bits from Alice start. -/
theorem receiver_comparison [Fintype X] [Fintype Y] (F : X → Y → Bool) :
    Yfree F ≤ Dalt .alice F ∧ Dalt .alice F ≤ Yfree F + 2 := by
  have h1 := (free_starter_comparison F).2
  have h2 := Dfree_le_Yfree_add_one F
  exact ⟨Yfree_le_Dalt .alice F, by omega⟩

/-- Exact manuscript form, interpreted in the integers. -/
theorem receiver_integer_comparison [Fintype X] [Fintype Y] (F : X → Y → Bool) :
    (Dalt .alice F : ℤ) - 2 ≤ (Yfree F : ℤ) ∧
      (Yfree F : ℤ) ≤ (Dalt .alice F : ℤ) := by
  obtain ⟨h1, h2⟩ := receiver_comparison F
  constructor <;> omega

/-- A nonconstant depth-zero receiver output is legal when the designated
player knows the answer. The public-output measure cannot do this. -/
theorem receiver_alice_bit_complexity : Yfree (fun (x : Bool) (_ : Unit) => x) = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply Nat.sInf_le
  exact ⟨ReceiverProtocol.zero .alice id, rfl, by intro x y; rfl⟩

/-- Nonvacuity: sending Alice's input really computes a nonconstant matrix. -/
def aliceBitProtocol : StrictProtocol Bool Unit .alice :=
  StrictProtocol.alice id (StrictProtocol.leaf .bob false) (StrictProtocol.leaf .bob true)

theorem aliceBitProtocol_cost : aliceBitProtocol.cost = 1 := rfl

theorem aliceBitProtocol_computes : aliceBitProtocol.Computes (fun x _ => x) := by
  intro x y
  cases x <;> rfl

theorem no_zero_cost_alice_bit {s : Turn} (P : StrictProtocol Bool Unit s) :
    P.cost = 0 → ¬ P.Computes (fun x _ => x) := by
  intro hcost hcomp
  have hz : P.toProtocol.cost = 0 := hcost
  cases htree : P.toProtocol with
  | leaf b =>
      have h0 := hcomp false ()
      have h1 := hcomp true ()
      simp only [StrictProtocol.eval, htree, Protocol.eval] at h0 h1
      exact Bool.false_ne_true (h0.symm.trans h1)
  | aNode a l r => simp [htree, Protocol.cost] at hz
  | bNode b l r => simp [htree, Protocol.cost] at hz

theorem alice_bit_complexity : Dalt .alice (fun (x : Bool) (_ : Unit) => x) = 1 := by
  have hle := Dalt_le_cost aliceBitProtocol aliceBitProtocol_computes
  rw [aliceBitProtocol_cost] at hle
  obtain ⟨P, hcost, hP⟩ := exists_optimal .alice (fun (x : Bool) (_ : Unit) => x)
  have hne : P.cost ≠ 0 := fun hz => no_zero_cost_alice_bit P hz hP
  omega

end Paper2.Yao
