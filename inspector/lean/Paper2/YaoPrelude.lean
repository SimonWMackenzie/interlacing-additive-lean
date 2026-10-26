import Paper2.YaoPrelCount
import Paper2.YaoPrelPay

/-! Unit 5 segment Y6 (lane a-yao-owner-2): the Yao prelude.

Consumers: the index decoder Y4 (`YaoIdxDecode.physical_index_decode`, divisor
cells `sel`, `pay`, `pow`), the position machine Y3 (`YaoPosFull.physical_position`,
cell `K`), and the one-entry callback Y5 (unary `e` for the controller start
bank, preserved).  One fixed program per `(t, lambda)`, `1 ≤ t`, placed by an
arbitrary embedding `θ : PCell t lambda ↪ J`, `PCell t lambda = CStack t lambda ⊕ Fin 22`.

Named cells (`θ (inr i)`): 1 unary `e` (input, preserved); outputs
2 `b = paddedEdgeBits e`, 3 `pow = paddedEdgeCount e = 2^b`,
4 `sel = selectorCount t b lambda`, 5 `pay = payloadCount t b lambda`,
6 `K = 2^t * 2^t`; 0 is not used (reserved for unary `v`); 7..21 and the whole
`inl` region are scratch, empty at entry and at exit.

Stages (two charged handoffs): the count stage `physical_count`; the payload
stage `physical_pay` (parts A, B, C); the admitted fixed-unary writer for `K`.
Every input is produced from unary `e` and the fixed `t, lambda`; nothing is
inserted as a desired value.  Exit bank exact. -/

noncomputable section

namespace Paper2.YaoPrelude

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.YaoLowerBound
open Paper2.YaoLookup

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

variable {J : Type*} [DecidableEq J]

/-! ## The composed payload stage -/

def payBC (t lambda : ℕ) (ι : Fin 17 ↪ J) :=
  BitMachineRawSequence.program (partB t lambda ι) (partC t ι)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) partBControl partCControl

/-- The fixed payload-count program. -/
def payStage (t lambda : ℕ) (ι : Fin 17 ↪ J) :=
  BitMachineRawSequence.program (partA t ι) (payBC t lambda ι)
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (0 : SourceClauseFixedUnary.Label (2 ^ t * 2 ^ t + 1))))
    partAControl (partBControl, partCControl)

def payControl := (partAControl, (partBControl, partCControl))

def payX (t lambda b : ℕ) : ℕ :=
  lambda + 2 ^ b * (2 ^ t * 2 ^ t + 1) * (Paper2.Yao.aliceNodes (b + 3 * t - 3) + 1)

def payClock (t lambda b : ℕ) : ℕ :=
  partAClock t b + partBClock t lambda (2 ^ b) (Paper2.Yao.aliceNodes (b + 3 * t - 3) + 1) +
    partCClock t b (payX t lambda b) + 2

/-- Y6 payload stage: from unary `b` and `pow = 2^b` to unary
`payloadCount t b lambda`; only cell 2 changes. -/
theorem physical_pay (t lambda : ℕ) (ht : 1 ≤ t) (ι : Fin 17 ↪ J) (S : J → List Bool) (b : ℕ)
    (h0 : S (ι 0) = List.replicate b true) (h1 : S (ι 1) = List.replicate (2 ^ b) true)
    (hs : ∀ k : Fin 17, 2 ≤ k.val → S (ι k) = []) :
    ∃ total ≤ payClock t lambda b, ∃ c',
      ((advance (payStage t lambda ι))^[total])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)), payControl, S⟩ :
          TM2.Cfg (fun _ : J => Bool) _ _) =
        ⟨none, c', Function.update S (ι 2)
          (List.replicate (payloadCount t b lambda) true)⟩ := by
  classical
  have hinj := ι.injective
  have e : ∀ k : Fin 17, 2 ≤ k.val → S (ι k) = [] := hs
  obtain ⟨ta, hta, ca, hra⟩ := part_A t ht ι S b h0 (e 3 (by decide)) (e 4 (by decide))
    (e 5 (by decide)) (e 6 (by decide)) (e 7 (by decide)) (e 14 (by decide))
    (e 15 (by decide)) (e 16 (by decide))
  set A1 := Paper2.Yao.aliceNodes (b + 3 * t - 3) + 1 with hA1
  set SA := Function.update S (ι 6) (List.replicate A1 true) with hSA
  obtain ⟨tb, htb, cb, hrb⟩ := part_B t lambda ι SA (2 ^ b) A1
    (by simp [hSA, hinj.eq_iff, h1]) (by simp [hSA])
    (by simp [hSA, hinj.eq_iff, e 8 (by decide)]) (by simp [hSA, hinj.eq_iff, e 9 (by decide)])
    (by simp [hSA, hinj.eq_iff, e 10 (by decide)]) (by simp [hSA, hinj.eq_iff, e 14 (by decide)])
  have hB : Function.update (Function.update SA (ι 6) []) (ι 10)
      (List.replicate (lambda + 2 ^ b * (2 ^ t * 2 ^ t + 1) * A1) true) =
      Function.update S (ι 10) (List.replicate (payX t lambda b) true) := by
    rw [hSA, Function.update_idem, (Function.update_eq_self_iff (f := S) (a := ι 6) (b := [])).mpr (e 6 (by decide)).symm]
    rfl
  rw [hB] at hrb
  set SB := Function.update S (ι 10) (List.replicate (payX t lambda b) true) with hSB
  obtain ⟨tc, htc, cc, hrc⟩ := part_C t ι SB b (payX t lambda b)
    (by simp [hSB, hinj.eq_iff, h0]) (by simp [hSB])
    (by simp [hSB, hinj.eq_iff, e 2 (by decide)]) (by simp [hSB, hinj.eq_iff, e 11 (by decide)])
    (by simp [hSB, hinj.eq_iff, e 12 (by decide)]) (by simp [hSB, hinj.eq_iff, e 13 (by decide)])
    (by simp [hSB, hinj.eq_iff, e 14 (by decide)]) (by simp [hSB, hinj.eq_iff, e 15 (by decide)])
    (by simp [hSB, hinj.eq_iff, e 16 (by decide)])
  have hC : Function.update (Function.update SB (ι 10) []) (ι 2)
      (List.replicate ((2 ^ (t - 4 + b) + payX t lambda b - 1) / 2 ^ (t - 4 + b)) true) =
      Function.update S (ι 2) (List.replicate (payloadCount t b lambda) true) := by
    rw [hSB, Function.update_idem, (Function.update_eq_self_iff (f := S) (a := ι 10) (b := [])).mpr (e 10 (by decide)).symm,
      payloadCount_eq, Nat.add_comm (t - 4) b]
    rfl
  rw [hC] at hrc
  obtain ⟨u2, hu2, hrun2⟩ := BitMachineRawSequence.runs (partB t lambda ι) (partC t ι)
    (BitMachineRawSequence.leftLabel (0 : SourceClauseFixedUnary.Label (2 ^ t * 2 ^ t + 1)))
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    partBControl cb partCControl cc SA SB _ tb tc hrb hrc
  obtain ⟨u1, hu1, hrun1⟩ := BitMachineRawSequence.runs (partA t ι) (payBC t lambda ι)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (0 : SourceClauseFixedUnary.Label (2 ^ t * 2 ^ t + 1))))
    partAControl ca (partBControl, partCControl) (partBControl, cc) S SA _ ta u2 hra hrun2
  rw [hA1] at htb
  exact ⟨u1, by unfold payClock; omega, _, hrun1⟩

#print axioms physical_pay

/-! ## The prelude placement -/

abbrev PCell (t lambda : ℕ) := CStack t lambda ⊕ Fin 22

/-- Count-stage names inside the prelude cells. -/
def cnt5 : Fin 5 ↪ Fin 22 := ⟨![1, 2, 3, 4, 7], by decide⟩
/-- Payload-stage names inside the prelude cells. -/
def pay17 : Fin 17 ↪ Fin 22 :=
  ⟨![2, 3, 5, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21], by decide⟩

def countPlace {t lambda : ℕ} (θ : PCell t lambda ↪ J) : CStack t lambda ⊕ Fin 5 ↪ J :=
  (Function.Embedding.sumMap (Function.Embedding.refl _) cnt5).trans θ

def payPlace {t lambda : ℕ} (θ : PCell t lambda ↪ J) : Fin 17 ↪ J :=
  (pay17.trans Function.Embedding.inr).trans θ

def preRest (t lambda : ℕ) (θ : PCell t lambda ↪ J) :=
  BitMachineRawSequence.program (payStage t lambda (payPlace θ))
    (SourceClauseFixedUnary.program (θ (.inr 6)) (2 ^ t * 2 ^ t))
    (0 : SourceClauseFixedUnary.Label (2 ^ t * 2 ^ t)) payControl ()

/-- The fixed prelude program (depends only on `t, lambda` and the placement). -/
def prelude (t lambda : ℕ) (θ : PCell t lambda ↪ J) :=
  BitMachineRawSequence.program (countProgram (countPlace θ)) (preRest t lambda θ)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
        BitMachineCopy.Label.scan)))
    (countStartControl t lambda) (payControl, ())

def preludeControl (t lambda : ℕ) := (countStartControl t lambda, (payControl, ()))

/-- The exact prelude exit bank. -/
def preludeOut {t lambda : ℕ} (θ : PCell t lambda ↪ J) (W : J → List Bool) (e : ℕ) :
    J → List Bool :=
  Function.update (Function.update (Function.update (Function.update (Function.update W
    (θ (.inr 2)) (List.replicate (paddedEdgeBits e) true))
    (θ (.inr 3)) (List.replicate (paddedEdgeCount e) true))
    (θ (.inr 4)) (List.replicate (selectorCount t (paddedEdgeBits e) lambda) true))
    (θ (.inr 5)) (List.replicate (payloadCount t (paddedEdgeBits e) lambda) true))
    (θ (.inr 6)) (List.replicate (2 ^ t * 2 ^ t) true)

def preludeClock (t lambda e : ℕ) : ℕ :=
  countClock t lambda e + payClock t lambda (paddedEdgeBits e) + (2 ^ t * 2 ^ t + 1) + 2

/-- Y6 main theorem: one physical run of the fixed prelude from charged unary
`e` to the exact exit bank holding `b`, `pow = 2^b`, `sel`, `pay` and `K`. -/
theorem physical_prelude (t lambda : ℕ) (ht : 1 ≤ t) (θ : PCell t lambda ↪ J)
    (W : J → List Bool) (e : ℕ)
    (he : W (θ (.inr 1)) = List.replicate e true)
    (hs : ∀ i : Fin 22, 2 ≤ i.val → W (θ (.inr i)) = [])
    (hreg : ∀ k, W (θ (.inl k)) = []) :
    ∃ total ≤ preludeClock t lambda e, ∃ c',
      ((advance (prelude t lambda θ))^[total])
        (⟨some (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
            BitMachineCopy.Label.scan)),
          preludeControl t lambda, W⟩ : TM2.Cfg (fun _ : J => Bool) _ _) =
        ⟨none, c', preludeOut θ W e⟩ := by
  classical
  have hinj := θ.injective
  -- stage 1: count
  obtain ⟨t1, ht1, c1, hr1⟩ := physical_count (countPlace θ) W e
    (by simpa [countPlace, cnt5] using he)
    (by simpa [countPlace, cnt5] using hs 2 (by decide))
    (by simpa [countPlace, cnt5] using hs 3 (by decide))
    (by simpa [countPlace, cnt5] using hs 4 (by decide))
    (by simpa [countPlace, cnt5] using hs 7 (by decide))
    (by intro k; simpa [countPlace] using hreg k)
  have hW1 : countOut (countPlace θ) W e =
      Function.update (Function.update (Function.update W
        (θ (.inr 2)) (List.replicate (paddedEdgeBits e) true))
        (θ (.inr 3)) (List.replicate (paddedEdgeCount e) true))
        (θ (.inr 4)) (List.replicate (selectorCount t (paddedEdgeBits e) lambda) true) := rfl
  rw [hW1] at hr1
  set W1 := Function.update (Function.update (Function.update W
        (θ (.inr 2)) (List.replicate (paddedEdgeBits e) true))
        (θ (.inr 3)) (List.replicate (paddedEdgeCount e) true))
        (θ (.inr 4)) (List.replicate (selectorCount t (paddedEdgeBits e) lambda) true) with hW1'
  -- stage 2: payload count
  have hpay : ∀ k : Fin 17, 2 ≤ k.val → W1 (payPlace θ k) = [] := by
    intro k hk
    have hk' : 5 ≤ (pay17 k).val := by
      fin_cases k <;> simp_all [pay17]
    simp only [hW1', payPlace, Function.Embedding.trans_apply, Function.Embedding.inr_apply]
    rw [Function.update_of_ne (by simp [hinj.eq_iff]; omega),
      Function.update_of_ne (by simp [hinj.eq_iff]; omega),
      Function.update_of_ne (by simp [hinj.eq_iff]; omega)]
    exact hs _ (by omega)
  obtain ⟨t2, ht2, c2, hr2⟩ := physical_pay t lambda ht (payPlace θ) W1 (paddedEdgeBits e)
    (by simp [hW1', payPlace, pay17, hinj.eq_iff])
    (by simp [hW1', payPlace, pay17, hinj.eq_iff, paddedEdgeCount]) hpay
  have hW2 : Function.update W1 (payPlace θ 2)
      (List.replicate (payloadCount t (paddedEdgeBits e) lambda) true) =
      Function.update W1 (θ (.inr 5))
        (List.replicate (payloadCount t (paddedEdgeBits e) lambda) true) := rfl
  rw [hW2] at hr2
  set W2 := Function.update W1 (θ (.inr 5))
    (List.replicate (payloadCount t (paddedEdgeBits e) lambda) true) with hW2'
  -- stage 3: write K
  have hr3 := SourceClauseFixedUnary.run (θ (.inr 6)) W2 (2 ^ t * 2 ^ t)
    (by simp [hW2', hW1', hinj.eq_iff, hs 6 (by decide)])
  obtain ⟨u2, hu2, hrun2⟩ := BitMachineRawSequence.runs (payStage t lambda (payPlace θ))
    (SourceClauseFixedUnary.program (θ (.inr 6)) (2 ^ t * 2 ^ t))
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    (0 : SourceClauseFixedUnary.Label (2 ^ t * 2 ^ t)) payControl c2 () () W1 W2 _ t2
    (2 ^ t * 2 ^ t + 1) hr2 hr3
  obtain ⟨u1, hu1, hrun1⟩ := BitMachineRawSequence.runs (countProgram (countPlace θ))
    (preRest t lambda θ) (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
        BitMachineCopy.Label.scan)))
    (countStartControl t lambda) c1 (payControl, ()) (payControl, ()) W W1 _ t1 u2 hr1 hrun2
  exact ⟨u1, by unfold preludeClock; omega, _, hrun1⟩

#print axioms physical_prelude

end Paper2.YaoPrelude

end
