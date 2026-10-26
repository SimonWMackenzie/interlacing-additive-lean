import Paper2.SourceMatrix
import Paper2.InterlaceProtocol

/-!
# Legal upper protocols for the source matrix

Frozen Paper 2 v12, Section 4, `src:upper`. All messages below are functions
of the sender's input and the previous messages. The matrix constructor in
`SourceMatrix` takes no colouring. A collision-free bin assignment is used
only to prove a cheaper protocol for its YES instances.
-/

namespace Paper2

open Workspace.Types.Protocol Workspace.Types.CommComplexity

namespace FiniteAnnounce

variable {A B V : Type*} [Fintype V] [Nonempty V]

noncomputable def code (v : V) : Fin (Nat.clog 2 (Fintype.card V)) → Bool :=
  selectorCode (Fintype.card V) (Fintype.equivFin V v)

noncomputable def decode (w : Fin (Nat.clog 2 (Fintype.card V)) → Bool) : V :=
  (Fintype.equivFin V).symm (selectorDecode (Fintype.card_pos) w)

@[simp] theorem decode_code (v : V) : decode (code v) = v := by
  simp [decode, code]

noncomputable def alice (read : A → V) (next : V → Protocol A B Bool) :
    Protocol A B Bool :=
  Workspace.UpperBound.announceTree (Nat.clog 2 (Fintype.card V))
    (fun w => next (decode w)) (fun a => code (read a))

theorem alice_cost (read : A → V) (next : V → Protocol A B Bool)
    {c : ℕ} (h : ∀ v, (next v).cost ≤ c) :
    (alice read next).cost ≤ Nat.clog 2 (Fintype.card V) + c := by
  exact Workspace.UpperBound.announceTree_cost c _ _ _ (fun _ => h _)

@[simp] theorem alice_eval (read : A → V) (next : V → Protocol A B Bool)
    (a : A) (b : B) : (alice read next).eval a b = (next (read a)).eval a b := by
  simp [alice, Workspace.UpperBound.announceTree_eval]

noncomputable def bob (read : B → V) (next : V → Protocol A B Bool) :
    Protocol A B Bool :=
  Workspace.UpperBound.Protocol.transpose
    (alice read (fun v => Workspace.UpperBound.Protocol.transpose (next v)))

theorem bob_cost (read : B → V) (next : V → Protocol A B Bool)
    {c : ℕ} (h : ∀ v, (next v).cost ≤ c) :
    (bob read next).cost ≤ Nat.clog 2 (Fintype.card V) + c := by
  simp only [bob, Workspace.UpperBound.Protocol.transpose_cost]
  exact alice_cost read _ (fun v => by
    simpa only [Workspace.UpperBound.Protocol.transpose_cost] using h v)

@[simp] theorem bob_eval (read : B → V) (next : V → Protocol A B Bool)
    (a : A) (b : B) : (bob read next).eval a b = (next (read b)).eval a b := by
  simp [bob, Workspace.UpperBound.Protocol.transpose_eval]

end FiniteAnnounce

namespace SourceMatrix

variable {X Y I : Type*} {s q₁ q₂ : ℕ} [NeZero s] [NeZero q₂]

def rowBin (assign : I → Fin s) : RawRow q₁ q₂ s X I → Fin s
  | .inl (p, _) => p
  | .inr (i, _) => assign i

def rowBase (α : Fin q₂) : RawRow q₁ q₂ s X I → X
  | .inl (_, z) => (z α).2
  | .inr (_, u) => u

def universalChoice (activity : I → Fin q₂ → Option (Fin s)) (α : Fin q₂) :
    RawRow q₁ q₂ s X I → Fin q₁ ⊕ Fin (s + 1)
  | .inl (_, z) => .inl (z α).1
  | .inr (i, _) => .inr ((activity i α).elim (Fin.last s) Fin.castSucc)

def universalDecode (p : Fin s) (c : Fin q₁ ⊕ Fin (s + 1))
    (Z : RawColumn q₁ q₂ s Y) : Y :=
  match c with
  | .inl r => head (Z.2 p).2 r
  | .inr k => if (∀ j, (Z.2 j).1 = (Z.2 0).1) then Z.1 k else Z.1 (Fin.last s)

omit [NeZero q₂] in
theorem universal_request (assign : I → Fin s)
    (activity : I → Fin q₂ → Option (Fin s))
    (k : RawRow q₁ q₂ s X I) (Z : RawColumn q₁ q₂ s Y) :
    (rowBase (Z.2 (rowBin assign k)).1 k,
      universalDecode (rowBin assign k)
        (universalChoice activity (Z.2 (rowBin assign k)).1 k) Z) =
      baseRequest activity k Z := by
  cases k with
  | inl k => rfl
  | inr k =>
    rcases k with ⟨i, u⟩
    by_cases h : ∀ j, (Z.2 j).1 = (Z.2 0).1
    · cases ha : activity i (Z.2 0).1 <;>
        simp [rowBin, rowBase, universalChoice, universalDecode, h,
          baseRequest, sourceColumn, sourcePosition, ha]
    · simp [rowBin, rowBase, universalChoice, universalDecode, h,
        baseRequest, sourceColumn, sourcePosition]

/-- Alice announces a bin; Bob announces its outer coordinate; Alice names
one of `q₁+s+1` inputs; then they run the base protocol. -/
noncomputable def universalProtocol (assign : I → Fin s)
    (activity : I → Fin q₂ → Option (Fin s)) (P : Protocol X Y Bool) :
    Protocol (RawRow q₁ q₂ s X I) (RawColumn q₁ q₂ s Y) Bool :=
  FiniteAnnounce.alice (rowBin assign) fun p =>
    FiniteAnnounce.bob (fun Z => (Z.2 p).1) fun α =>
      FiniteAnnounce.alice (universalChoice activity α) fun c =>
        Workspace.UpperBound.Protocol.comap (rowBase α) (universalDecode p c) P

theorem universalProtocol_cost (assign : I → Fin s)
    (activity : I → Fin q₂ → Option (Fin s)) (P : Protocol X Y Bool) :
    (universalProtocol (q₁ := q₁) assign activity P).cost ≤
      Nat.clog 2 s + Nat.clog 2 q₂ + Nat.clog 2 (q₁ + s + 1) + P.cost := by
  unfold universalProtocol
  have h := FiniteAnnounce.alice_cost (rowBin (q₁ := q₁) (q₂ := q₂) (X := X) assign)
    (fun p => FiniteAnnounce.bob (fun Z : RawColumn q₁ q₂ s Y => (Z.2 p).1)
      (fun α => FiniteAnnounce.alice (universalChoice activity α)
        (fun c => Workspace.UpperBound.Protocol.comap (rowBase α) (universalDecode p c) P)))
    (fun p => FiniteAnnounce.bob_cost _ _ (fun α =>
      FiniteAnnounce.alice_cost _ _ (fun c => by
        rw [Workspace.UpperBound.Protocol.comap_cost])))
  simpa [Fintype.card_sum, Fintype.card_fin, Nat.add_assoc] using h

theorem universalProtocol_computes (assign : I → Fin s)
    (activity : I → Fin q₂ → Option (Fin s)) (R : X → Y → Bool)
    (P : Protocol X Y Bool) (hP : P.Computes R) :
    (universalProtocol (q₁ := q₁) assign activity P).Computes (raw R activity) := by
  intro k Z
  simp only [universalProtocol, FiniteAnnounce.alice_eval, FiniteAnnounce.bob_eval,
    Workspace.UpperBound.Protocol.comap_eval]
  rw [hP]
  have h := universal_request assign activity k Z
  exact congrArg (fun xy : X × Y => R xy.1 xy.2) h

/-- An assignment has at most one active item per bin at every coordinate. -/
def CollisionFree (assign : I → Fin s) (activity : I → Fin q₂ → Option (Fin s)) : Prop :=
  ∀ α i j r r', activity i α = some r → activity j α = some r' →
    assign i = assign j → i = j

/-- Bob's active decoder, constructed from the assignment. In a bin with no
active item it uses the neutral position; such a branch is never needed by
an active source row. -/
noncomputable def activePosition (assign : I → Fin s)
    (activity : I → Fin q₂ → Option (Fin s)) (p : Fin s) (α : Fin q₂) : Fin (s + 1) := by
  classical
  exact if h : ∃ r, ∃ i, assign i = p ∧ activity i α = some r then
    (Classical.choose h).castSucc
  else Fin.last s

omit [NeZero s] [NeZero q₂] in
theorem activePosition_eq (assign : I → Fin s)
    (activity : I → Fin q₂ → Option (Fin s)) (hc : CollisionFree assign activity)
    (α : Fin q₂) (i : I) (r : Fin s) (hi : activity i α = some r) :
    activePosition assign activity (assign i) α = r.castSucc := by
  classical
  have he : ∃ r', ∃ j, assign j = assign i ∧ activity j α = some r' :=
    ⟨r, i, rfl, hi⟩
  rw [activePosition, dif_pos he]
  obtain ⟨j, hj, ha⟩ := Classical.choose_spec he
  have hji := hc α j i _ r ha hi hj
  subst j
  have heq : Classical.choose he = r := Option.some.inj (ha.symm.trans hi)
  rw [heq]

def yesChoice (activity : I → Fin q₂ → Option (Fin s)) (α : Fin q₂) :
    RawRow q₁ q₂ s X I → Fin q₁ ⊕ Bool
  | .inl (_, z) => .inl (z α).1
  | .inr (i, _) => .inr (activity i α).isSome

noncomputable def yesDecode (assign : I → Fin s)
    (activity : I → Fin q₂ → Option (Fin s)) (p : Fin s) (c : Fin q₁ ⊕ Bool)
    (Z : RawColumn q₁ q₂ s Y) : Y :=
  match c with
  | .inl r => head (Z.2 p).2 r
  | .inr b => if b && decide (∀ j, (Z.2 j).1 = (Z.2 0).1) then
      Z.1 (activePosition assign activity p (Z.2 p).1) else Z.1 (Fin.last s)

omit [NeZero q₂] in
theorem yes_request (assign : I → Fin s)
    (activity : I → Fin q₂ → Option (Fin s)) (hc : CollisionFree assign activity)
    (k : RawRow q₁ q₂ s X I) (Z : RawColumn q₁ q₂ s Y) :
    (rowBase (Z.2 (rowBin assign k)).1 k,
      yesDecode assign activity (rowBin assign k)
        (yesChoice activity (Z.2 (rowBin assign k)).1 k) Z) =
      baseRequest activity k Z := by
  cases k with
  | inl k => rfl
  | inr k =>
    rcases k with ⟨i, u⟩
    by_cases h : ∀ j, (Z.2 j).1 = (Z.2 0).1
    · cases ha : activity i (Z.2 0).1 with
      | none => simp [rowBase, rowBin, yesChoice, yesDecode,
          baseRequest, sourceColumn, sourcePosition, h, ha]
      | some r =>
        have hp := activePosition_eq assign activity hc (Z.2 0).1 i r ha
        simp [rowBase, rowBin, yesChoice, yesDecode,
          baseRequest, sourceColumn, sourcePosition, h, ha, hp]
    · simp [rowBase, rowBin, yesChoice, yesDecode,
        baseRequest, sourceColumn, sourcePosition, h]

noncomputable def yesProtocol (assign : I → Fin s)
    (activity : I → Fin q₂ → Option (Fin s)) (P : Protocol X Y Bool) :
    Protocol (RawRow q₁ q₂ s X I) (RawColumn q₁ q₂ s Y) Bool :=
  FiniteAnnounce.alice (rowBin assign) fun p =>
    FiniteAnnounce.bob (fun Z => (Z.2 p).1) fun α =>
      FiniteAnnounce.alice (yesChoice activity α) fun c =>
        Workspace.UpperBound.Protocol.comap (rowBase α) (yesDecode assign activity p c) P

theorem yesProtocol_cost (assign : I → Fin s)
    (activity : I → Fin q₂ → Option (Fin s)) (P : Protocol X Y Bool) :
    (yesProtocol (q₁ := q₁) assign activity P).cost ≤
      Nat.clog 2 s + Nat.clog 2 q₂ + Nat.clog 2 (q₁ + 2) + P.cost := by
  unfold yesProtocol
  have h := FiniteAnnounce.alice_cost (rowBin (q₁ := q₁) (q₂ := q₂) (X := X) assign)
    (fun p => FiniteAnnounce.bob (fun Z : RawColumn q₁ q₂ s Y => (Z.2 p).1)
      (fun α => FiniteAnnounce.alice (yesChoice activity α)
        (fun c => Workspace.UpperBound.Protocol.comap
          (rowBase α) (yesDecode assign activity p c) P)))
    (fun p => FiniteAnnounce.bob_cost _ _ (fun α =>
      FiniteAnnounce.alice_cost _ _ (fun c => by
        rw [Workspace.UpperBound.Protocol.comap_cost])))
  simpa [Fintype.card_sum, Fintype.card_fin, Nat.add_assoc] using h

theorem yesProtocol_computes (assign : I → Fin s)
    (activity : I → Fin q₂ → Option (Fin s)) (hc : CollisionFree assign activity)
    (R : X → Y → Bool) (P : Protocol X Y Bool) (hP : P.Computes R) :
    (yesProtocol (q₁ := q₁) assign activity P).Computes (raw R activity) := by
  intro k Z
  simp only [yesProtocol, FiniteAnnounce.alice_eval, FiniteAnnounce.bob_eval,
    Workspace.UpperBound.Protocol.comap_eval]
  rw [hP]
  exact congrArg (fun xy : X × Y => R xy.1 xy.2) (yes_request assign activity hc k Z)

section Finite

variable [Fintype X] [Fintype Y] [Fintype I]

theorem raw_D_le (activity : I → Fin q₂ → Option (Fin s)) (R : X → Y → Bool) :
    D (raw (q₁ := q₁) R activity) ≤
      Nat.clog 2 s + Nat.clog 2 q₂ + Nat.clog 2 (q₁ + s + 1) + D R := by
  obtain ⟨P, hcost, hcomp⟩ := Nat.sInf_mem (Workspace.UpperBound.AchievableCosts_nonempty R)
  have h := universalProtocol_cost (q₁ := q₁) (fun _ : I => (0 : Fin s)) activity P
  rw [hcost] at h
  apply le_trans (Nat.sInf_le ?_) h
  exact ⟨_, rfl, universalProtocol_computes _ _ R P hcomp⟩

theorem raw_D_le_of_collisionFree (assign : I → Fin s)
    (activity : I → Fin q₂ → Option (Fin s)) (hc : CollisionFree assign activity)
    (R : X → Y → Bool) :
    D (raw (q₁ := q₁) R activity) ≤
      Nat.clog 2 s + Nat.clog 2 q₂ + Nat.clog 2 (q₁ + 2) + D R := by
  obtain ⟨P, hcost, hcomp⟩ := Nat.sInf_mem (Workspace.UpperBound.AchievableCosts_nonempty R)
  have h := yesProtocol_cost (q₁ := q₁) assign activity P
  rw [hcost] at h
  apply le_trans (Nat.sInf_le ?_) h
  exact ⟨_, rfl, yesProtocol_computes _ _ hc R P hcomp⟩

omit [NeZero q₂] in
/-- All three raw tags retain every raw column through the unrestricted
tag, so tagging and transposition preserve the optimum exactly. -/
theorem N_D_eq_raw (activity : I → Fin q₂ → Option (Fin s))
    (R : X → Y → Bool) (ξ₀ : Tail s Y) :
    D (N (q₁ := q₁) R activity ξ₀) = D (raw (q₁ := q₁) R activity) := by
  change D (fun Z k => raw R activity k (forgetTag ξ₀ Z)) = _
  rw [transpose_D]
  exact pullback_D_eq_of_surjective (raw R activity) id (forgetTag ξ₀)
    Function.surjective_id (forgetTag_surjective ξ₀)

theorem N_D_le (activity : I → Fin q₂ → Option (Fin s))
    (R : X → Y → Bool) (ξ₀ : Tail s Y) :
    D (N (q₁ := q₁) R activity ξ₀) ≤
      Nat.clog 2 s + Nat.clog 2 q₂ + Nat.clog 2 (q₁ + s + 1) + D R := by
  rw [N_D_eq_raw]
  exact raw_D_le activity R

theorem N_D_le_of_collisionFree (assign : I → Fin s)
    (activity : I → Fin q₂ → Option (Fin s)) (hc : CollisionFree assign activity)
    (R : X → Y → Bool) (ξ₀ : Tail s Y) :
    D (N (q₁ := q₁) R activity ξ₀) ≤
      Nat.clog 2 s + Nat.clog 2 q₂ + Nat.clog 2 (q₁ + 2) + D R := by
  rw [N_D_eq_raw]
  exact raw_D_le_of_collisionFree assign activity hc R

/-- Exact source-independent and YES budgets in `src:upper`. The finite
width equalities are explicit; their production by the schedule is separate. -/
theorem source_upper_budgets (activity : I → Fin q₂ → Option (Fin s))
    (R : X → Y → Bool) (ξ₀ : Tail s Y) (a b : ℕ)
    (hq₁ : q₁ + 2 = s) (hs : s = 2 ^ a) (hq₂ : q₂ = 2 ^ b) :
    D (N (q₁ := q₁) R activity ξ₀) ≤ D R + a + b + a + 1 ∧
      (∀ assign, CollisionFree assign activity →
        D (N (q₁ := q₁) R activity ξ₀) ≤ D R + a + b + a) := by
  have hslog : Nat.clog 2 s = a := by rw [hs, Nat.clog_pow 2 a (by decide)]
  have hqlog : Nat.clog 2 q₂ = b := by rw [hq₂, Nat.clog_pow 2 b (by decide)]
  have hsel : Nat.clog 2 (q₁ + s + 1) ≤ a + 1 := by
    apply Nat.clog_le_of_le_pow
    rw [pow_succ, ← hs]
    omega
  have hu := N_D_le (q₁ := q₁) activity R ξ₀
  rw [hslog, hqlog] at hu
  refine ⟨by omega, ?_⟩
  intro assign hc
  have hy := N_D_le_of_collisionFree (q₁ := q₁) assign activity hc R ξ₀
  rw [hq₁, hslog, hqlog] at hy
  omega

omit [NeZero q₂] in
theorem successor_D_le (activity : I → Fin q₂ → Option (Fin s))
    (R : X → Y → Bool) (ξ₀ : Tail s Y) (w Q : ℕ) (hw : 0 < w) (hQ : 0 < Q) :
    D (successor (q₁ := q₁) R activity ξ₀ w Q) ≤
      Nat.clog 2 Q + Nat.clog 2 w + D (N (q₁ := q₁) R activity ξ₀) := by
  unfold successor
  apply (fullInterlace_transpose_D_le _ Q hQ).trans
  have h := fullInterlace_transpose_D_le (N (q₁ := q₁) R activity ξ₀) w hw
  omega

/-- Both upper bounds for the actual amplified matrix; no lower bound or
profile theorem is assumed or asserted here. -/
theorem successor_upper_budgets (activity : I → Fin q₂ → Option (Fin s))
    (R : X → Y → Bool) (ξ₀ : Tail s Y) (w Q a b c d : ℕ)
    (hq₁ : q₁ + 2 = s) (hs : s = 2 ^ a) (hq₂ : q₂ = 2 ^ b)
    (hw : w = 2 ^ c) (hQ : Q = 2 ^ d) :
    D (successor (q₁ := q₁) R activity ξ₀ w Q) ≤ D R + (a + a + b + c + d) + 1 ∧
      (∀ assign, CollisionFree assign activity →
        D (successor (q₁ := q₁) R activity ξ₀ w Q) ≤ D R + (a + a + b + c + d)) := by
  have h := successor_D_le (q₁ := q₁) activity R ξ₀ w Q
    (by rw [hw]; positivity) (by rw [hQ]; positivity)
  have hwlog : Nat.clog 2 w = c := by rw [hw, Nat.clog_pow 2 c (by decide)]
  have hQlog : Nat.clog 2 Q = d := by rw [hQ, Nat.clog_pow 2 d (by decide)]
  rw [hwlog, hQlog] at h
  obtain ⟨hu, hy⟩ := source_upper_budgets (q₁ := q₁) activity R ξ₀ a b hq₁ hs hq₂
  refine ⟨by omega, ?_⟩
  intro assign hc
  have := hy assign hc
  omega

end Finite

end SourceMatrix
end Paper2
