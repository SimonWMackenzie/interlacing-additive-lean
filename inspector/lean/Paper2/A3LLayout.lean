import Paper2.A3H3Run
import Paper2.A3U
import Paper2.A3NC
import Paper2.RepJoin
import EthInapproximability.CurrentPaper.BitMachineStackGrowth
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-!
# Unit 3 lift, segment 0: the H_A3 bank layout, Mid1, Mid2 and the generic tools

Lane `owner:a-h-a3-lift-1` (private, 26 September 2026). Consumer: `A3H3Run.H_A3_R12` (owner-3, R13).

The widened H_A3 bank `Fin (a + 3)` is split, through ONE fixed equivalence, into the work region
`W FS = Fin 3 ⊕ (OS ⊕ (PO ⊕ (JN ⊕ (JT5 ⊕ (JU ⊕ FS)))))` (three single cells: flag₁, flag₂, the common output cell;
the master start region; the probe copy region; the none, success and unscheduled regions; the front scratch `FS`)
followed by the three H_A3 packet cells at `a, a+1, a+2` exactly as in `Wrap.widen`.
-/

namespace Paper2.A3Assembly.Lift

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2
open SourceProfileParameters SourceRecursiveNoSampling TotalFiniteConstructorScratch

/-! ### The layout -/

/-- The work region. -/
abbrev W (FS : Type) : Type :=
  Fin 3 ⊕ (SuccessOrient.Stack ⊕ (SuccessOrient.Stack ⊕ (NoneOut.JN ⊕
    (RepJoin.JT5 ⊕ (Unsched.JU ⊕ FS)))))

noncomputable instance instDecJT5 : DecidableEq RepJoin.JT5 := instDecidableEqSum

set_option synthInstance.maxSize 16384 in
noncomputable instance instFtJT5 : Fintype RepJoin.JT5 := inferInstance
set_option synthInstance.maxSize 16384 in
noncomputable instance instFtJN : Fintype NoneOut.JN := inferInstance
set_option synthInstance.maxSize 16384 in
noncomputable instance instFtJU : Fintype Unsched.JU := inferInstance
set_option synthInstance.maxSize 16384 in
noncomputable instance instFtOS : Fintype SuccessOrient.Stack := inferInstance
set_option synthInstance.maxSize 16384 in
noncomputable instance instFtW (FS : Type) [Fintype FS] : Fintype (W FS) := inferInstance

/-- The number of work cells. -/
noncomputable def a (FS : Type) [Fintype FS] : ℕ := Fintype.card (W FS)

/-- The fixed enumeration of the work cells. -/
noncomputable def eW (FS : Type) [Fintype FS] [DecidableEq FS] : W FS ≃ Fin (a FS) :=
  Fintype.equivFin (W FS)

variable (FS : Type) [Fintype FS] [DecidableEq FS]

/-- Position of a layout cell in the widened bank. -/
noncomputable def pos (x : W FS ⊕ Fin 3) : Fin (a FS + 3) :=
  finSumFinEquiv (Sum.map (eW FS) id x)

theorem pos_injective : Function.Injective (pos FS) := by
  intro x y h
  have h1 := finSumFinEquiv.injective h
  rcases x with x | x <;> rcases y with y | y <;> simp_all [Sum.map]

/-- A widened bank described by its packet `P` and its work region `R`. -/
noncomputable def layoutBank (P : Fin 3 → List Bool) (R : W FS → List Bool) :
    Fin (a FS + 3) → List Bool :=
  fun i => Sum.elim R P (Sum.map (eW FS).symm id (finSumFinEquiv.symm i))

theorem layoutBank_inl (P : Fin 3 → List Bool) (R : W FS → List Bool) (x : W FS) :
    layoutBank FS P R (pos FS (.inl x)) = R x := by
  simp [layoutBank, pos]

theorem layoutBank_inr (P : Fin 3 → List Bool) (R : W FS → List Bool) (i : Fin 3) :
    layoutBank FS P R (pos FS (.inr i)) = P i := by
  simp [layoutBank, pos]

theorem pos_surj (i : Fin (a FS + 3)) : ∃ x, pos FS x = i := by
  refine ⟨Sum.map (eW FS).symm id (finSumFinEquiv.symm i), ?_⟩
  simp only [pos]
  rcases h : finSumFinEquiv.symm i with u | u
  · simp only [Sum.map_inl, Equiv.apply_symm_apply]
    rw [← h, Equiv.apply_symm_apply]
  · simp only [Sum.map_inr, id]
    rw [← h, Equiv.apply_symm_apply]

/-- Two widened banks agreeing at every layout position are equal. -/
theorem bank_ext (S S' : Fin (a FS + 3) → List Bool) (h : ∀ x, S (pos FS x) = S' (pos FS x)) :
    S = S' := by
  funext i
  obtain ⟨x, rfl⟩ := pos_surj FS i
  exact h x

/-- The widened H_A3 input is the layout bank with a blank work region. -/
theorem widen_eq (X : Fin 3 → List Bool) :
    Wrap.widen (a FS) X = layoutBank FS X (fun _ => []) := by
  apply bank_ext
  intro x
  rcases x with x | x
  · rw [layoutBank_inl]
    have hv : (pos FS (.inl x)).val < a FS := by
      simp [pos, finSumFinEquiv_apply_left]
    simp only [Wrap.widen]
    rw [dif_neg (by omega)]
  · rw [layoutBank_inr]
    have hv : (pos FS (.inr x)).val = a FS + x.val := by
      simp [pos, finSumFinEquiv_apply_right]
    simp only [Wrap.widen]
    rw [dif_pos (by omega)]
    congr 1
    ext
    simp only [hv]
    omega

/-! ### Fixed cells and region embeddings -/

noncomputable def flag₁ : Fin (a FS + 3) := pos FS (.inl (.inl 0))
noncomputable def flag₂ : Fin (a FS + 3) := pos FS (.inl (.inl 1))
noncomputable def outJ : Fin (a FS + 3) := pos FS (.inl (.inl 2))
noncomputable def pk (i : Fin 3) : Fin (a FS + 3) := pos FS (.inr i)

/-- Master start region. -/
noncomputable def ιOS : SuccessOrient.Stack ↪ Fin (a FS + 3) :=
  ⟨fun x => pos FS (.inl (.inr (.inl x))), fun x y h => by
    have := pos_injective FS h; simpa using this⟩

/-- Probe copy region. -/
noncomputable def ιPO : SuccessOrient.Stack ↪ Fin (a FS + 3) :=
  ⟨fun x => pos FS (.inl (.inr (.inr (.inl x)))), fun x y h => by
    have := pos_injective FS h; simpa using this⟩

/-- Front scratch. -/
noncomputable def ιFS : FS ↪ Fin (a FS + 3) :=
  ⟨fun z => pos FS (.inl (.inr (.inr (.inr (.inr (.inr (.inr z))))))), fun x y h => by
    have := pos_injective FS h; simpa using this⟩

/-! ### The canonical start bank and Mid1 / Mid2 -/

/-- The canonical success start bank (the counts of the let block of `ThrJoin.success_run_full`). -/
noncomputable def startCanon (Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices) (k : ℕ)
    (t : (select hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape) :
    SuccessOrient.Stack → List Bool :=
  SuccessOrient.startBank g.vertices (LookupSeed.width (Nat.clog 2 g.vertices))
    (width (Nat.clog 2 g.vertices)) (width (Nat.clog 2 g.vertices) - 2)
    (outerWidth (Nat.clog 2 g.vertices))
    (ParameterizedCanonicalSource.restorationWidth (Nat.clog 2 g.vertices))
    (ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ) k
    (sourceRows (Nat.clog 2 g.vertices)
      (ParameterizedCanonicalSource.restorationDepth (Nat.clog 2 g.vertices))
      (ParameterizedCanonicalSource.coverDepth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ) k)
    (sourceCols (Nat.clog 2 g.vertices)
      (ParameterizedCanonicalSource.restorationDepth (Nat.clog 2 g.vertices))
      (ParameterizedCanonicalSource.coverDepth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ) k)
    ((select hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).tapeBits t)

/-- Work-region contents: the three single cells `c`, the master start region `st`, the front scratch `Z`,
every other work cell blank. -/
def region (st : SuccessOrient.Stack → List Bool) (c : Fin 3 → List Bool) (Z : FS → List Bool) :
    W FS → List Bool :=
  Sum.elim c (Sum.elim st (Sum.elim (fun _ => []) (Sum.elim (fun _ => [])
    (Sum.elim (fun _ => []) (Sum.elim (fun _ => []) Z)))))

/-- **Mid1** (the front's post-condition): packet untouched, the master start region EXACTLY the canonical
`SuccessOrient.startBank` with `word = tapeBits t`, `flag₁` exactly one bit, `flag₂` and the output cell blank,
the probe / none / success / unscheduled regions blank, the front scratch arbitrary, and encoded size
at most `CM·(n+2)^(EM(k+1))`. -/
def Mid1 (Δ : ℕ) (γ : ℚ) (CM EM : ℕ) : Run.Pred Δ γ (a FS) := fun g hg hn k t S =>
  (∃ (b : Bool) (Z : FS → List Bool),
    S = layoutBank FS (Wrap.inputBank Δ γ g hg hn k t)
      (region FS (startCanon Δ γ g hg hn k t) ![[b], [], []] Z)) ∧
  (BitMachineBankCodec.encode S).length ≤ CM * (g.vertices + 2) ^ (EM * (k + 1))

/-- **Mid2** (the probe's post-condition): as Mid1, with `flag₂` exactly one bit. -/
def Mid2 (Δ : ℕ) (γ : ℚ) (CM EM : ℕ) : Run.Pred Δ γ (a FS) := fun g hg hn k t S =>
  (∃ (b₁ b₂ : Bool) (Z : FS → List Bool),
    S = layoutBank FS (Wrap.inputBank Δ γ g hg hn k t)
      (region FS (startCanon Δ γ g hg hn k t) ![[b₁], [b₂], []] Z)) ∧
  (BitMachineBankCodec.encode S).length ≤ CM * (g.vertices + 2) ^ (EM * (k + 1))

/-! ### Generic tools -/

/-- Growth of the encoded bank along any run of a finite program (admitted per-cell growth). -/
theorem size_run {K : ℕ} {L V : Type} [Fintype L]
    (P : L → TM2.Stmt (fun _ : Fin K => Bool) L V) (c : TM2.Cfg (fun _ : Fin K => Bool) L V) (t : ℕ) :
    (BitMachineBankCodec.encode (((advance P)^[t]) c).stk).length ≤
      (BitMachineBankCodec.encode c.stk).length + 2 * K * (BitMachineStackGrowth.perStep P * t) := by
  rw [BitMachineBankCodec.encode_length, BitMachineBankCodec.encode_length]
  have h : ∑ j, ((((advance P)^[t]) c).stk j).length ≤
      ∑ j : Fin K, ((c.stk j).length + BitMachineStackGrowth.perStep P * t) :=
    Finset.sum_le_sum (fun j _ => BitMachineStackGrowth.run_growth P c t j)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  have : 2 * K * (BitMachineStackGrowth.perStep P * t) =
      2 * (K * (BitMachineStackGrowth.perStep P * t)) := by ring
  omega

/-- Lifting a whole program along a stack embedding (same labels and controls). -/
def liftP {K J L V : Type} [DecidableEq K] [DecidableEq J] (ι : K ↪ J)
    (P : L → TM2.Stmt (fun _ : K => Bool) L V) : L → TM2.Stmt (fun _ : J => Bool) L V :=
  fun l => stackStmt ι (P l)

end Paper2.A3Assembly.Lift

#print axioms Paper2.A3Assembly.Lift.pos_injective
#print axioms Paper2.A3Assembly.Lift.widen_eq
#print axioms Paper2.A3Assembly.Lift.bank_ext
#print axioms Paper2.A3Assembly.Lift.size_run
