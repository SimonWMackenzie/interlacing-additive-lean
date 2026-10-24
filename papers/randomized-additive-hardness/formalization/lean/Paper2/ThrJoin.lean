import Paper2.SuccessGraphMain
import Paper2.ThrRun

/-! Unit 3, segment (5): the unary threshold produced and installed.

Joint bank `JT3 = SuccessGraph.JT2 ⊕ ThrProducer.TK`. ONE fixed program `thrJoin`:
1. six source-preserving copies of the admitted raw public counts p, s, q₂, w, Q, k of
   `SuccessOrient.startBank` (`SamplerParameterJoin.nrSrc` 5, 0, 2, 3, 4, 6) into the producer
   bank (`ThrProducer.T0 k ![p, s, q₂, w, Q]`);
2. `ThrProducer.thrProg` (lifted);
3. one copy `thr → thrM` (the header-join threshold cell, blank before).
`budget_eq`: at the canonical schedule the produced value is exactly
`sourceBudget L (restorationDepth L) (coverDepth n m L Δ γ) k`. -/

set_option maxHeartbeats 64000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.ThrJoin

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2.HeaderJoin (JH hjIn wOut thrM scrH)
open Paper2.SuccessXfer (OS JT)
open Paper2.SuccessGraph (JT2 preJHm)
open Paper2.ThrProducer (TK thrC ctrC scrC xC srcI outI T0 thrProg thrStart thrCtl Xv thrBd)

abbrev JT3 := JT2 ⊕ TK

instance instDecJT2 : DecidableEq JT2 := inferInstance
instance instDecTK : DecidableEq TK := inferInstance
instance instDecJT3 : DecidableEq JT3 := instDecidableEqSum

theorem budget_eq (n m Δ : ℕ) (γ : ℚ) (k : ℕ) :
    let L := Nat.clog 2 n
    k * Xv ![LookupSeed.width L, SourceProfileParameters.width L,
        SourceProfileParameters.outerWidth L, ParameterizedCanonicalSource.restorationWidth L,
        ParameterizedCanonicalSource.coverWidth n m L Δ γ] +
      (Nat.clog 2 (LookupSeed.width L) + 1) =
    SourceRecursiveNoSampling.sourceBudget L (ParameterizedCanonicalSource.restorationDepth L)
      (ParameterizedCanonicalSource.coverDepth n m L Δ γ) k := by
  intro L
  have h1 : Nat.clog 2 (LookupSeed.width L) = LookupSeed.exponent L := by
    unfold LookupSeed.width; exact Nat.clog_pow 2 _ (by norm_num)
  have h2 : Nat.clog 2 (SourceProfileParameters.width L) = SourceProfileParameters.exponent L := by
    unfold SourceProfileParameters.width; exact Nat.clog_pow 2 _ (by norm_num)
  have h3 : Nat.clog 2 (SourceProfileParameters.outerWidth L) =
      SourceProfileParameters.outerExponent L := by
    unfold SourceProfileParameters.outerWidth; exact Nat.clog_pow 2 _ (by norm_num)
  have h4 : Nat.clog 2 (ParameterizedCanonicalSource.restorationWidth L) =
      ParameterizedCanonicalSource.restorationDepth L := by
    unfold ParameterizedCanonicalSource.restorationWidth ParameterizedCanonicalSource.restorationDepth
      RestorationWidthScheduleScratch.width
    exact Nat.clog_pow 2 _ (by norm_num)
  have h5 : Nat.clog 2 (ParameterizedCanonicalSource.coverWidth n m L Δ γ) =
      ParameterizedCanonicalSource.coverDepth n m L Δ γ := rfl
  change k * (Nat.clog 2 (ParameterizedCanonicalSource.coverWidth n m L Δ γ) +
      (Nat.clog 2 (ParameterizedCanonicalSource.restorationWidth L) +
        (Nat.clog 2 (SourceProfileParameters.width L) +
          (Nat.clog 2 (SourceProfileParameters.outerWidth L) +
            Nat.clog 2 (SourceProfileParameters.width L))))) +
      (Nat.clog 2 (LookupSeed.width L) + 1) = _
  rw [h1, h2, h3, h4, h5]
  unfold SourceRecursiveNoSampling.sourceBudget
  ring

/-- The threshold cell of the header bank inside `JT3`. -/
def thrJ : JT3 := .inl (.inl (.inr (.inl thrM)))
def scrJ : JT3 := .inr scrC

theorem thr_fill (g : EncodedGraph.Graph) (r thr : ℕ) (output : List Bool) :
    Function.update (preJHm g r 0 output) thrM (List.replicate thr true) =
      preJHm g r thr output := by
  funext a
  by_cases ha : a = thrM
  · subst ha
    rw [Function.update_self]
    unfold preJHm
    rw [Function.update_of_ne (by simp [thrM, SuccessInstall.mC, SuccessXfer.wAux])]
    rfl
  · rw [Function.update_of_ne ha]
    unfold preJHm
    by_cases hz : a = SuccessInstall.mC SuccessGraph.zM
    · subst hz
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hz, Function.update_of_ne hz]
      rcases a with a | (b | c)
      · rfl
      · rfl
      · fin_cases c
        · exact absurd rfl ha
        · rfl

/-! ### Copies of the raw counts into the producer bank -/

def srcJ (j : Fin 9) : JT3 := .inl (.inl (.inl (SuccessInstall.srcC j)))

def dT : Fin 6 → TK := ![srcI 0, srcI 1, srcI 2, srcI 3, srcI 4, ctrC]
def sT : Fin 6 → Fin 9 := ![5, 0, 2, 3, 4, 6]

theorem dT_inj : ∀ i j, dT i = dT j → i = j := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [dT, srcI, ctrC]

def cpT (i : Fin 6) : Fin 3 ↪ JT3 :=
  ⟨![srcJ (sT i), .inr (dT i), scrJ], by
    intro a b h
    fin_cases i <;> fin_cases a <;> fin_cases b <;> simp_all [srcJ, scrJ, dT, srcI, ctrC, scrC]⟩

def cpM : Fin 1 → (Fin 3 ↪ JT3) := fun _ =>
  ⟨![.inr thrC, thrJ, scrJ], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [thrJ, scrJ, thrC, scrC]⟩

def ιT : TK ↪ JT3 := ⟨Sum.inr, Sum.inr_injective⟩
def ιL : JT2 ↪ JT3 := ⟨Sum.inl, Sum.inl_injective⟩

theorem bank_T (X : JT2 → List Bool) (Y Z : TK → List Bool) :
    bank ιT (Sum.elim X Y) Z = Sum.elim X Z := by
  funext c
  rcases c with c | c
  · exact bank_outside ιT _ Z (.inl c) (by rintro ⟨k, hk⟩; cases hk)
  · exact bank_at ιT _ Z c

theorem bank_L (X Z : JT2 → List Bool) (Y : TK → List Bool) :
    bank ιL (Sum.elim X Y) Z = Sum.elim Z Y := by
  funext c
  rcases c with c | c
  · exact bank_at ιL _ Z c
  · exact bank_outside ιL _ Z (.inr c) (by rintro ⟨k, hk⟩; cases hk)

def thrL := fun l => stackStmt ιT (thrProg l)
def fullL := fun l => stackStmt ιL (SuccessGraph.fullProg2 l)

def j1 := BitMachineRawSequence.program (CopyAll.prog cpT) thrL thrStart
  (none : Option Bool) thrCtl
/-- ONE fixed program: produce and install the threshold. -/
def thrJoin := BitMachineRawSequence.program j1 (CopyAll.prog cpM) (.inl ⟨0, by omega⟩)
  ((none : Option Bool), thrCtl) (none : Option Bool)

def jStart := SamplerFallbackJoin.labelOf fullL
  (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel (.inl ⟨0, by omega⟩))))
def jCtl := ((((none : Option Bool), SuccessGraph.gCtl), (none : Option Bool)),
  SuccessGraph.fCtl)

/-- ONE fixed program: threshold, then `SuccessGraph.fullProg2`. -/
def fullProg3 := BitMachineRawSequence.program thrJoin fullL jStart
  (((none : Option Bool), thrCtl), (none : Option Bool)) jCtl

end

#print axioms budget_eq
#print axioms thr_fill

end Paper2.ThrJoin
