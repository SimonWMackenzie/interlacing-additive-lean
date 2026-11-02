import Paper2.ThrMain
import Paper2.RepIdent

/-! Unit 3, segment (1), join: the unary repetition factor is PRODUCED inside the success branch.

Bank `JT5 = ThrJoin.JT3 ⊕ MS`, `MS = PublicGraphEndpointMachine.Stack ⊕ (RepProducer.RK ⊕ Fin 1)`
(a private side region: a second endpoint-machine region, the repetition-producer region and one copy
scratch cell).

ONE fixed program `preProg` (production `BitMachineRawSequence` handoffs):
1. copy the literal public graph bytes (master endpoint cell `zG`) into the side endpoint region;
2. the admitted `PublicGraphEndpointMachine.program` there (unary `m = |E(g)|` produced from the bytes);
3. three source-preserving copies: side unary `m`, the admitted raw count `s` (`SamplerParameterJoin.nrSrc 0`)
   and `q₂` (`nrSrc 2`) of the success start bank into the producer inputs;
4. `RepProducer.repProg` on the producer region;
5. copy the quotient into the (blank) master decode cell 1 (`zR`, unary `r`).

Then `repFull = preProg ; ThrJoin.fullProg3` (lifted). `success_run_rep`: from the admitted success start
bank beside `preJHm g 0 0 output` (NO unary `r`, no unary `m`, blank threshold) and blank side regions, all
conclusions of `ThrJoin.success_run_full` with `r = ParameterizedCanonicalSource.rep L m`. -/

set_option maxHeartbeats 64000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.RepJoin

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2.HeaderJoin (JH)
open Paper2.SuccessXfer (OS JT)
open Paper2.SuccessInstall (mC preJH0 auxPre0 master0)
open Paper2.SuccessGraph (JT2 preJHm zG zM gIn mOut PS)
open Paper2.ThrJoin (JT3)

abbrev MS := PS ⊕ (RepProducer.RK ⊕ Fin 1)
abbrev JT5 := JT3 ⊕ MS

/-- Master decode cell 1 (unary `r`). -/
def zR : SrcX.JX := .inl (.inr (.inl (.inl 1)))

def hj (a : JH WEntry.Kw) : JT5 := .inl (.inl (.inl (.inr (.inl a))))
def os (o : OS) : JT5 := .inl (.inl (.inl (.inl o)))
def ps (x : PS) : JT5 := .inr (.inl x)
def rk (x : RepProducer.RK) : JT5 := .inr (.inr (.inl x))
def sc5 : JT5 := .inr (.inr (.inr 0))

/-! ### The unary-`r` cell of the writer start bank -/

theorem zR_ne_zM : mC zR ≠ mC zM := by
  simp [mC, SuccessXfer.wAux, RLoop.mX, zR, zM]

theorem preJH0_zR (g : EncodedGraph.Graph) (r thr : ℕ) (output : List Bool) :
    preJH0 g r thr output (mC zR) = List.replicate r true := by
  change auxPre0 g r (WEntry.eqv.symm (WEntry.eqv _)) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem preJHm_zR (g : EncodedGraph.Graph) (r thr : ℕ) (output : List Bool) :
    preJHm g r thr output (mC zR) = List.replicate r true := by
  unfold preJHm
  rw [Function.update_of_ne zR_ne_zM, preJH0_zR]

/-- Outside the unary-`r` cell the writer start bank does not depend on `r`. -/
theorem preJH0_off (g : EncodedGraph.Graph) (r thr : ℕ) (output : List Bool) (a : JH WEntry.Kw)
    (ha : a ≠ mC zR) : preJH0 g 0 thr output a = preJH0 g r thr output a := by
  rcases a with ((c | e) | h)
  · rcases c with c | c
    · obtain ⟨b, rfl⟩ := WEntry.eqv.surjective c
      change auxPre0 g 0 (WEntry.eqv.symm (WEntry.eqv b)) =
        auxPre0 g r (WEntry.eqv.symm (WEntry.eqv b))
      rw [Equiv.symm_apply_apply]
      rcases b with b | b
      · rcases b with jt | (z | c2)
        · rfl
        · rcases z with ((bb | (jj | f4)) | lb)
          · rfl
          · rcases jj with d | rest
            · fin_cases d
              · rfl
              · exact absurd rfl ha
              all_goals rfl
            · rfl
          · rfl
          · rfl
        · rfl
      · rfl
    · fin_cases c <;> rfl
  · cases e <;> rfl
  · rfl

theorem preJHm_off (g : EncodedGraph.Graph) (r thr : ℕ) (output : List Bool) (a : JH WEntry.Kw)
    (ha : a ≠ mC zR) : preJHm g 0 thr output a = preJHm g r thr output a := by
  unfold preJHm
  by_cases hz : a = mC zM
  · subst hz
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hz, Function.update_of_ne hz]
    exact preJH0_off g r thr output a ha

/-! ### Copy specifications and the prefix program -/

def cpA : Fin 1 → (Fin 3 ↪ JT5) := fun _ =>
  ⟨![hj (mC zG), ps gIn, sc5], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [hj, ps, sc5]⟩

def srcCf : Fin 3 → JT5 :=
  ![ps mOut, os (SuccessInstall.srcC 0), os (SuccessInstall.srcC 2)]
def dstCf : Fin 3 → JT5 :=
  ![rk RepProducer.mC, rk RepProducer.sC, rk RepProducer.qC]

def cpC (i : Fin 3) : Fin 3 ↪ JT5 :=
  ⟨![srcCf i, dstCf i, sc5], by
    intro a b h
    fin_cases i <;> fin_cases a <;> fin_cases b <;>
      simp_all [srcCf, dstCf, ps, os, rk, sc5, RepProducer.mC, RepProducer.sC, RepProducer.qC]⟩

def cpE : Fin 1 → (Fin 3 ↪ JT5) := fun _ =>
  ⟨![rk RepProducer.rC, hj (mC zR), sc5], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [hj, rk, sc5]⟩

def ιPS : PS ↪ JT5 := ⟨fun x => .inr (.inl x), fun a b h => by simpa using h⟩
def ιRK : RepProducer.RK ↪ JT5 := ⟨fun x => .inr (.inr (.inl x)), fun a b h => by simpa using h⟩
def ιJ : JT3 ↪ JT5 := ⟨Sum.inl, Sum.inl_injective⟩

theorem bank_PS (X : JT3 → List Bool) (P Z : PS → List Bool) (R : RepProducer.RK ⊕ Fin 1 → List Bool) :
    bank ιPS (Sum.elim X (Sum.elim P R)) Z = Sum.elim X (Sum.elim Z R) := by
  funext c
  rcases c with c | (c | c)
  · exact bank_outside ιPS _ Z (.inl c) (by rintro ⟨k, hk⟩; cases hk)
  · exact bank_at ιPS _ Z c
  · exact bank_outside ιPS _ Z (.inr (.inr c)) (by rintro ⟨k, hk⟩; cases hk)

theorem bank_RK (X : JT3 → List Bool) (P : PS → List Bool) (Y Z : RepProducer.RK → List Bool)
    (W : Fin 1 → List Bool) :
    bank ιRK (Sum.elim X (Sum.elim P (Sum.elim Y W))) Z = Sum.elim X (Sum.elim P (Sum.elim Z W)) := by
  funext c
  rcases c with c | (c | (c | c))
  · exact bank_outside ιRK _ Z (.inl c) (by rintro ⟨k, hk⟩; cases hk)
  · exact bank_outside ιRK _ Z (.inr (.inl c)) (by rintro ⟨k, hk⟩; cases hk)
  · exact bank_at ιRK _ Z c
  · exact bank_outside ιRK _ Z (.inr (.inr (.inr c))) (by rintro ⟨k, hk⟩; cases hk)

theorem bank_J (X Z : JT3 → List Bool) (Y : MS → List Bool) :
    bank ιJ (Sum.elim X Y) Z = Sum.elim Z Y := by
  funext c
  rcases c with c | c
  · exact bank_at ιJ _ Z c
  · exact bank_outside ιJ _ Z (.inr c) (by rintro ⟨k, hk⟩; cases hk)

def graphP := fun l => stackStmt ιPS (PublicGraphEndpointMachine.program l)
def repL := fun l => stackStmt ιRK (RepProducer.repProg l)

def e1 := BitMachineRawSequence.program (CopyAll.prog cpA) graphP
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) (none : Option Bool) SuccessGraph.gCtl
def f1 := ((none : Option Bool), SuccessGraph.gCtl)
def e2 := BitMachineRawSequence.program e1 (CopyAll.prog cpC) (.inl ⟨0, by omega⟩) f1
  (none : Option Bool)
def f2 := (f1, (none : Option Bool))
def e3 := BitMachineRawSequence.program e2 repL RepProducer.repStart f2 RepProducer.repCtl
def f3 := (f2, RepProducer.repCtl)
/-- The prefix: produce unary `m` (second endpoint run), then unary `r`, and install it. ONE fixed program. -/
def preProg := BitMachineRawSequence.program e3 (CopyAll.prog cpE) (.inl ⟨0, by omega⟩) f3
  (none : Option Bool)
def preCtl := (f3, (none : Option Bool))
def preStart := SamplerFallbackJoin.labelOf preProg
  (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (.inl ⟨0, by omega⟩)))))

def fullJ := fun l => stackStmt ιJ (ThrJoin.fullProg3 l)
def fullStart := SamplerFallbackJoin.labelOf fullJ
  (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel (.inl ⟨0, by omega⟩))))
def fullCtl := ((((none : Option Bool), ThrProducer.thrCtl), (none : Option Bool)), ThrJoin.jCtl)

/-- ONE fixed program: the prefix, then owner-9's whole success branch `ThrJoin.fullProg3`. -/
def repFull := BitMachineRawSequence.program preProg fullJ fullStart preCtl fullCtl

/-! ### The prefix run -/

/-- Owner-9's `JT3` start bank with unary `r` in the master decode cell 1. -/
def Y (n p s q₁ q₂ w Q k mX mY : ℕ) (word : List Bool) (g : EncodedGraph.Graph) (r : ℕ)
    (output : List Bool) : JT3 → List Bool :=
  Sum.elim (Sum.elim (Sum.elim (SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word)
    (Sum.elim (preJHm g r 0 output) (fun _ => []))) (fun _ => [])) (fun _ => [])

/-- The side region at the exit of the prefix. -/
def MSfin (g : EncodedGraph.Graph) (hg : g.Valid) (s q₂ : ℕ)
    (c : ETHParameterScaleMachineLogCopy.logMachine.Config) : MS → List Bool :=
  Sum.elim (PublicGraphEndpointMachine.resultBank g hg)
    (Sum.elim (Sum.elim (RepProducer.fin1 s q₂ g.edges.length)
      (ETHParameterScaleMachineLogCopy.afterLog (RepProducer.u (12 * s * g.edges.length)) c).stk)
      (fun _ => []))

def quot (s q₂ m : ℕ) : ℕ := q₂ / 2 ^ Nat.clog 2 (12 * s * m)

def preBd (g : EncodedGraph.Graph) (s q₂ : ℕ) : ℕ :=
  (1 * (2 * (EncodedGraph.encode g).length + 3) + 1) +
    103 * ((EncodedGraph.encode g).length + 1) ^ 3 +
    (3 * (2 * (g.edges.length + s + q₂) + 3) + 1) + RepProducer.repBd s q₂ g.edges.length +
    (1 * (2 * quot s q₂ g.edges.length + 3) + 1) + 4

end

end Paper2.RepJoin
