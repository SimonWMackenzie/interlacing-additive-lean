import Paper2.A3LUnsched
import Paper2.A3D
import Paper2.A3H3ClockB
import Paper2.ClearAll
import Paper2.SourceOverheadBounds

/-!
# Unit 3 lift, segment 1: hProbe (the generator-outcome bit) on the H_A3 layout bank

Lane `owner:a-h-a3-lift-2` (private, 26 September 2026). Paper A, lock v12.
Continues lane a-h-a3-lift-1 (frozen `A3LLayout`, `A3LUnsched`, imported, not changed).

ONE fixed program `pProg FS = copies ; (status push of the lifted admitted decision run) ; clear`
(production `BitMachineRawSequence` handoffs, every handoff charged):
1. `CopyAll.prog cpP`: one charged source-preserving copy per cell of `SuccessOrient.Stack`, master start
   region cell `ιOS x` into probe-copy region cell `ιPO x`, scratch `flag₂` (blank under Mid1);
2. `A3D.spProg` over the admitted `SamplerFallbackJoin.program` (the program `SuccessOrient.preProgram`
   runs inside `SuccessOrient.program`, the some/none decision) lifted by `ιPP = preSlots.trans ιPO` into the
   probe-copy region, pushing the ACTUAL final-control status `SuccessOrient.status` onto `flag₂`;
3. `ClearAll.prog csP`: charged pops of every probe-copy cell.
Exit bank EXACTLY Mid2: flag₂ = [status], the probe region blank again, everything else as in Mid1.
-/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.A3Assembly.Lift

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2
open SourceProfileParameters SourceRecursiveNoSampling TotalFiniteConstructorScratch

/-! ### Finite-control instances of the admitted decision program (private, own namespace; no
`deriving` into production namespaces) -/
noncomputable instance instFtCopyListLabel {K : Type} [DecidableEq K] :
    (xs : List (Fin 3 ↪ K)) → Fintype (CopyList.Label xs)
  | [] => inferInstanceAs (Fintype Unit)
  | _ :: xs => by
      haveI := instFtCopyListLabel xs
      exact inferInstanceAs
        (Fintype (BitMachineRawSequence.Label BitMachineCopy.Label (CopyList.Label xs)))

noncomputable instance instFtCopyListControl {K : Type} [DecidableEq K] :
    (xs : List (Fin 3 ↪ K)) → Fintype (CopyList.Control xs)
  | [] => inferInstanceAs (Fintype Unit)
  | _ :: xs => by
      haveI := instFtCopyListControl xs
      exact inferInstanceAs (Fintype (Option Bool × CopyList.Control xs))

noncomputable instance instFtSAMLabel :
    (xs : List SamplerAlphabetMachine.Source) → Fintype (SamplerAlphabetMachine.Label xs)
  | [] => inferInstanceAs (Fintype (SourceClauseFixedUnary.Label 514))
  | _ :: xs => by
      haveI := instFtSAMLabel xs
      exact inferInstanceAs
        (Fintype (BitMachineRawSequence.Label (SamplerAlphabetMachine.Label xs) BitMachineCopy.Label))

noncomputable instance instFtSAMControl :
    (xs : List SamplerAlphabetMachine.Source) → Fintype (SamplerAlphabetMachine.Control xs)
  | [] => inferInstanceAs (Fintype Unit)
  | _ :: xs => by
      haveI := instFtSAMControl xs
      exact inferInstanceAs (Fintype (SamplerAlphabetMachine.Control xs × Option Bool))

def sldEquiv : SamplerLoopDraw.Label ≃
    SamplerAffineLoop.Label ⊕ (Unit ⊕ (Bool × SamplerDrawCount.Label)) where
  toFun
    | .loop l => .inl l
    | .dispatch => .inr (.inl ())
    | .draw b l => .inr (.inr (b, l))
  invFun
    | .inl l => .loop l
    | .inr (.inl _) => .dispatch
    | .inr (.inr (b, l)) => .draw b l
  left_inv := by intro x; cases x <;> rfl
  right_inv := by intro x; rcases x with l | _ | ⟨b, l⟩ <;> rfl

noncomputable instance instFtSLDLabel : Fintype SamplerLoopDraw.Label :=
  Fintype.ofEquiv _ sldEquiv.symm

noncomputable instance instFtPreLabel : Fintype SuccessOrient.PreLabel := inferInstance
noncomputable instance instFtPreControl : Fintype SuccessOrient.PreControl := inferInstance

/-! ### Positivity of the canonical parameters (unconditional) -/

theorem pos_p (L : ℕ) : 0 < LookupSeed.width L := by unfold LookupSeed.width; positivity
theorem pos_q1 (L : ℕ) : 0 < width L - 2 := by
  have h := SourceProfileParameters.width_admissible L; omega
theorem pos_q2 (L : ℕ) : 0 < outerWidth L := by unfold outerWidth; positivity
theorem pos_w (L : ℕ) : 0 < ParameterizedCanonicalSource.restorationWidth L := by
  unfold ParameterizedCanonicalSource.restorationWidth RestorationWidthScheduleScratch.width
  positivity
theorem pos_Q (n m L Δ : ℕ) (γ : ℚ) : 0 < ParameterizedCanonicalSource.coverWidth n m L Δ γ := by
  rw [show ParameterizedCanonicalSource.coverWidth n m L Δ γ =
    2 ^ ParameterizedCanonicalSource.coverDepth n m L Δ γ from
    SourceOverheadBounds.actualQ_pow (V := Fin n) (E := Fin m) L γ Δ]
  positivity

/-! ### The physical tape and the generator outcome (scheduled branch) -/

/-- The physical sampler tape read from the selected tape. -/
def tapeOf (Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices) (k : ℕ)
    (hc : CompletePublicScheduleScratch.Checks (V := Fin g.vertices) (E := Fin g.edges.length)
      (Nat.clog 2 g.vertices) Δ γ)
    (t : (select hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape) :=
  SuccessIdent.physTape g.vertices (LookupSeed.width (Nat.clog 2 g.vertices))
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
    (SuccessIdent.selTape hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k hc t)

/-- The actual capped generator run on the physical tape (the `result` of `SuccessOrient.run`
at the canonical schedule). -/
def genOut (Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices) (k : ℕ)
    (hc : CompletePublicScheduleScratch.Checks (V := Fin g.vertices) (E := Fin g.edges.length)
      (Nat.clog 2 g.vertices) Δ γ)
    (t : (select hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape) : Option (List Bool) :=
  GeneratorCode.run
    (SuccessOrient.Bv g.vertices (LookupSeed.width (Nat.clog 2 g.vertices))
      (width (Nat.clog 2 g.vertices)) (width (Nat.clog 2 g.vertices) - 2)
      (outerWidth (Nat.clog 2 g.vertices))
      (ParameterizedCanonicalSource.restorationWidth (Nat.clog 2 g.vertices))
      (ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ))
    (SuccessOrient.Rv (LookupSeed.width (Nat.clog 2 g.vertices))
      (width (Nat.clog 2 g.vertices)) (width (Nat.clog 2 g.vertices) - 2)
      (outerWidth (Nat.clog 2 g.vertices))
      (ParameterizedCanonicalSource.restorationWidth (Nat.clog 2 g.vertices))
      (ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ) k
      (sourceRows (Nat.clog 2 g.vertices)
        (ParameterizedCanonicalSource.restorationDepth (Nat.clog 2 g.vertices))
        (ParameterizedCanonicalSource.coverDepth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ) k)
      (sourceCols (Nat.clog 2 g.vertices)
        (ParameterizedCanonicalSource.restorationDepth (Nat.clog 2 g.vertices))
        (ParameterizedCanonicalSource.coverDepth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ) k))
    (le_refl _)
    (SuccessOrient.Nv (LookupSeed.width (Nat.clog 2 g.vertices))
      (width (Nat.clog 2 g.vertices)) (width (Nat.clog 2 g.vertices) - 2)
      (outerWidth (Nat.clog 2 g.vertices))
      (ParameterizedCanonicalSource.restorationWidth (Nat.clog 2 g.vertices))
      (ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ) k
      (sourceRows (Nat.clog 2 g.vertices)
        (ParameterizedCanonicalSource.restorationDepth (Nat.clog 2 g.vertices))
        (ParameterizedCanonicalSource.coverDepth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ) k)
      (sourceCols (Nat.clog 2 g.vertices)
        (ParameterizedCanonicalSource.restorationDepth (Nat.clog 2 g.vertices))
        (ParameterizedCanonicalSource.coverDepth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ) k))
    (GeneratorStateSize.initialBounded
      (SuccessOrient.root g.vertices (LookupSeed.width (Nat.clog 2 g.vertices))
        (width (Nat.clog 2 g.vertices)) (width (Nat.clog 2 g.vertices) - 2)
        (outerWidth (Nat.clog 2 g.vertices))
        (ParameterizedCanonicalSource.restorationWidth (Nat.clog 2 g.vertices))
        (ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ) k
        (sourceRows (Nat.clog 2 g.vertices)
          (ParameterizedCanonicalSource.restorationDepth (Nat.clog 2 g.vertices))
          (ParameterizedCanonicalSource.coverDepth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ) k)
        (sourceCols (Nat.clog 2 g.vertices)
          (ParameterizedCanonicalSource.restorationDepth (Nat.clog 2 g.vertices))
          (ParameterizedCanonicalSource.coverDepth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ) k))
      (SamplerFallbackJoin.alphabet_bound g.vertices (LookupSeed.width (Nat.clog 2 g.vertices))
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
        hn (pos_p _) (SourceProfiles.width_ge_four _) (pos_q1 _) (pos_q2 _) (pos_w _) (pos_Q _ _ _ _ _)))
    (tapeOf Δ γ g hg hn k hc t)

/-- **Good** (the success outcome): `Checks` holds and the actual capped generator run on the physical
tape of the selected tape returns `some`. -/
def Good (Δ : ℕ) (γ : ℚ) : Run.Cond Δ γ := fun g hg hn k t =>
  ∃ hc : Run.ChecksCond Δ γ g hg hn k t, (genOut Δ γ g hg hn k hc t).isSome = true

/-- The literal word on the machine is the selected tape word. -/
theorem tapeOf_word (Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices)
    (k : ℕ) (hc : CompletePublicScheduleScratch.Checks (V := Fin g.vertices) (E := Fin g.edges.length)
      (Nat.clog 2 g.vertices) Δ γ)
    (t : (select hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape) :
    (RecursiveSamplingTape.writeTape _ _ _ (tapeOf Δ γ g hg hn k hc t)).val =
      (select hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).tapeBits t := by
  unfold tapeOf
  rw [SuccessIdent.physTape_word]
  exact (SuccessHeader.selTape_bits hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k hc t).symm

/-! ### The probe program -/

section Prog

variable (FS : Type) [Fintype FS] [DecidableEq FS]

/-- The admitted pre-stack placed in the probe-copy region. -/
def ιPP : SuccessOrient.PreStack ↪ Fin (a FS + 3) := SuccessOrient.preSlots.trans (ιPO FS)

theorem ιPP_apply (x : SuccessOrient.PreStack) : ιPP FS x = ιPO FS (.inl x) := rfl

abbrev NS : ℕ := Fintype.card SuccessOrient.Stack

def eS : SuccessOrient.Stack ≃ Fin NS := Fintype.equivFin _

/-- The copies master start region → probe-copy region, scratch `flag₂`. -/
def cpP (i : Fin NS) : Fin 3 ↪ Fin (a FS + 3) :=
  ⟨![ιOS FS (eS.symm i), ιPO FS (eS.symm i), flag₂ FS], by
    intro x y h
    fin_cases x <;> fin_cases y <;>
      simp_all [ιOS, ιPO, flag₂, (pos_injective FS).eq_iff]⟩

/-- The probe-copy cells, cleared at the end. -/
def csP (i : Fin NS) : Fin (a FS + 3) := ιPO FS (eS.symm i)

theorem csP_inj : Function.Injective (csP FS) := by
  intro i j h
  have := (ιPO FS).injective h
  exact eS.symm.injective this

def dProg := Dispatch.spProg (liftP (ιPP FS) SamplerFallbackJoin.program) SuccessOrient.status
  (flag₂ FS)

def tailP := BitMachineRawSequence.program (dProg FS) (ClearAll.prog (csP FS))
  (⟨0, by omega⟩ : Fin (NS + 1)) SamplerFallbackJoin.startControl (none : Option Bool)

/-- **The probe program.** -/
def pProg := BitMachineRawSequence.program (CopyAll.prog (cpP FS)) (tailP FS)
  (BitMachineRawSequence.leftLabel (.inl SamplerFallbackJoin.startLabel)) (none : Option Bool)
  (SamplerFallbackJoin.startControl, (none : Option Bool))

def pStart : BitMachineRawSequence.Label (CopyAll.Lab NS)
    (BitMachineRawSequence.Label (Dispatch.SPLabel SuccessOrient.PreLabel) (Fin (NS + 1))) :=
  BitMachineRawSequence.leftLabel (.inl ⟨0, by omega⟩)

def pCtl : Option Bool × (SuccessOrient.PreControl × Option Bool) :=
  ((none : Option Bool), (SamplerFallbackJoin.startControl, (none : Option Bool)))

/-! Constants (depend only on `FS`, `CM`, `EM`). -/
def PSc : ℕ := BitMachineStackGrowth.perStep (CopyAll.prog (cpP FS))
def PSd : ℕ := BitMachineStackGrowth.perStep (dProg FS)
def PSp : ℕ := BitMachineStackGrowth.perStep (pProg FS)
def Ac (CM : ℕ) : ℕ := 2 * NS * CM + (3 * NS + 1)
def A1 (CM : ℕ) : ℕ := CM + 2 * (a FS + 3) * PSc FS * Ac CM
def A3 (CM : ℕ) : ℕ := A1 FS CM + 2 * (a FS + 3) * PSd FS * 2
def Al (CM : ℕ) : ℕ := NS * A3 FS CM + (NS + 1)
def AT (CM : ℕ) : ℕ := Ac CM + Al FS CM + 4
/-- Probe constant (clock and final bank size). -/
def PC (CM : ℕ) : ℕ := AT FS CM + CM + 2 * (a FS + 3) * PSp FS * AT FS CM

end Prog

/-- Probe exponent. -/
def PE (EM : ℕ) : ℕ := max EM (2 * FallbackNoPreloadRun.noPreloadExponent)

/-! ### Linear bookkeeping -/

theorem lin1 (x y c d A Q : ℕ) (hQ : 1 ≤ Q) (hy : y ≤ A * Q) (hx : x ≤ c * y + d) :
    x ≤ (c * A + d) * Q := by
  have h1 : c * y ≤ c * (A * Q) := Nat.mul_le_mul_left c hy
  have h2 : d ≤ d * Q := Nat.le_mul_of_pos_right d hQ
  have e : (c * A + d) * Q = c * (A * Q) + d * Q := by ring
  omega

theorem lin2 (x y z c A B Q : ℕ) (hy : y ≤ A * Q) (hz : z ≤ B * Q) (hx : x ≤ y + c * z) :
    x ≤ (A + c * B) * Q := by
  have h1 : c * z ≤ c * (B * Q) := Nat.mul_le_mul_left c hz
  have e : (A + c * B) * Q = A * Q + c * (B * Q) := by ring
  omega

end

end Paper2.A3Assembly.Lift
