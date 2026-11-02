import Paper2.A3LProbeSpec
import Paper2.A3H3ClockS
import Paper2.RepMain

/-!
# Unit 3 lift, segment 2: hSucc (the success chain) on the H_A3 layout bank

Lane `owner:a-h-a3-lift-2` (private, 26 September 2026). Paper A, lock v12.

ONE fixed program `sProg FS = copy ; lift(ιS, RepJoin.repFull)` (production `BitMachineRawSequence` handoff):
1. `CopyAll.prog cpS`: ONE charged source-preserving copy, packet cell 0 (`encode g`) into the success-region cell
   `ιS (hj (mC zG))` (the writer bank's graph cell), scratch `ιS sc5` (blank). This is the only nonblank cell of the
   writer start bank `preJHm g 0 0 []` (`preJHm_blank`);
2. the admitted `RepJoin.repFull` (wave14-a32; `RepJoin.success_run_rep`, which PRODUCES `r = rep L m` itself) lifted
   by the stack embedding `ιS`: its start region `os` goes to the master start region `ιOS` (Mid2 holds exactly the
   canonical `SuccessOrient.startBank` there), its writer output cell `hj wOut` to the common output cell `outJ`,
   every other `JT5` cell to its own success-region cell.
Clock: admitted `success_run_rep` bound = `preBd` (bounded here, `preBd_le`) + the literal success clock (frozen
owner-3 `Clocks.success_full_clock_HA3`). Final size by `size_run`.
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
open Paper2.HeaderJoin (JH wOut)
open Paper2.SuccessInstall (mC)
open Paper2.SuccessGraph (preJHm zG zM)

/-! ### Finite control of the success chain (own namespace; the only missing instance) -/

def cermEquiv : CanonicalEndpointRankMachine.Control ≃
    (CanonicalEndpointRankMachine.Kind × CanonicalEndpointRankMachine.ItemKind ×
      CanonicalEndpointRankMachine.Cmp × CanonicalEndpointRankMachine.Cmp ×
      CanonicalEndpointRankMachine.Cmp × Option Bool × Option Bool × Option Bool × Bool) where
  toFun c := (c.kind, c.item, c.uv, c.xu, c.xv, c.readU, c.readV, c.readX, c.active)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
    p.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2⟩
  left_inv c := by cases c; rfl
  right_inv p := rfl

noncomputable instance instFtCERMControl : Fintype CanonicalEndpointRankMachine.Control :=
  Fintype.ofEquiv _ cermEquiv.symm

/-! ### The writer start bank has exactly one nonblank cell -/

theorem preJHm_blank (g : EncodedGraph.Graph) (a : JH WEntry.Kw) (ha : a ≠ mC zG) :
    preJHm g 0 0 [] a = [] := by
  unfold preJHm
  by_cases hz : a = mC zM
  · subst hz; rw [Function.update_self]
  rw [Function.update_of_ne hz]
  rcases a with ((c | e) | h)
  · rcases c with c | c
    · obtain ⟨b, rfl⟩ := WEntry.eqv.surjective c
      change SuccessInstall.auxPre0 g 0 (WEntry.eqv.symm (WEntry.eqv b)) = []
      rw [Equiv.symm_apply_apply]
      rcases b with b | b
      · rcases b with jt | (z | c2)
        · rfl
        · rcases z with ((bb | (jj | f4)) | lb)
          · rfl
          · rcases jj with d | rest
            · fin_cases d
              all_goals first | rfl | exact absurd rfl hz
            · rcases rest with ((ps | (y | f)) | f') | rr
              · rcases ps with ((p | p) | p)
                all_goals first
                  | (fin_cases p <;> first | rfl | exact absurd rfl ha)
                  | rfl
              · rfl
              · fin_cases f <;> rfl
              · fin_cases f' <;> rfl
              · first | rfl | (fin_cases rr <;> rfl)
          · rfl
          · rfl
        · rfl
      · rfl
    · fin_cases c <;> rfl
  · cases e <;> rfl
  · rcases h with h | h
    · rfl
    · fin_cases h <;> rfl

theorem preJHm_zG (g : EncodedGraph.Graph) : preJHm g 0 0 [] (mC zG) = EncodedGraph.encode g := by
  rw [preJHm, Function.update_of_ne SuccessGraph.zG_ne_zM, SuccessGraph.preJH0_zG]

theorem mCzG_ne_wOut : mC zG ≠ (wOut : JH WEntry.Kw) := by
  simp [SuccessInstall.mC, SuccessXfer.wAux, HeaderJoin.wOut]

/-! ### The prefix clock `RepJoin.preBd` in polynomial shape -/

/-- The constant of the prefix bound. -/
def PBc : ℕ := 4000 + 169 * (UnaryBinaryEncoding.coefficient + 6)

theorem preBd_le (g : EncodedGraph.Graph) (s q₂ B : ℕ) (hB : 1 ≤ B)
    (he : (EncodedGraph.encode g).length ≤ B) (hm : g.edges.length ≤ B) (hs : s ≤ B) (hq : q₂ ≤ B) :
    RepJoin.preBd g s q₂ ≤ PBc * B ^ 4 := by
  have hB2 : B ≤ B ^ 2 := by nlinarith
  have hB3 : B ^ 2 ≤ B ^ 3 := by nlinarith
  have hB4 : B ^ 3 ≤ B ^ 4 := by nlinarith
  have hsm : s * g.edges.length ≤ B ^ 2 := by
    calc s * g.edges.length ≤ B * B := Nat.mul_le_mul hs hm
      _ = B ^ 2 := by ring
  obtain ⟨x, hxdef⟩ : ∃ x, x = 12 * s * g.edges.length := ⟨_, rfl⟩
  have hx : x ≤ 12 * B ^ 2 := by rw [hxdef, mul_assoc]; omega
  have hx2 : x + 2 ≤ 14 * B ^ 2 := by omega
  have h2c : 2 ^ Nat.clog 2 x ≤ 196 * B ^ 4 := by
    have h := Paper2.A3Assembly.Clock.two_pow_clog_le x
    have h' : (x + 2) ^ 2 ≤ (14 * B ^ 2) ^ 2 := Nat.pow_le_pow_left hx2 2
    have e : (14 * B ^ 2) ^ 2 = 196 * B ^ 4 := by ring
    omega
  have hcl : Nat.clog 2 x ≤ 196 * B ^ 4 := (Nat.lt_two_pow_self).le.trans h2c
  have hx1 : (x + 1) ^ 2 ≤ 169 * B ^ 4 := by
    have h' : (x + 1) ^ 2 ≤ (13 * B ^ 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have e : (13 * B ^ 2) ^ 2 = 169 * B ^ 4 := by ring
    omega
  have hlog : (UnaryBinaryEncoding.coefficient + 6) * (x + 1) ^ 2 ≤
      (UnaryBinaryEncoding.coefficient + 6) * (169 * B ^ 4) := Nat.mul_le_mul_left _ hx1
  have hD1 : 1 ≤ 2 ^ Nat.clog 2 x := Nat.one_le_two_pow
  have hdiv : MatrixUnaryDivision.exactTime q₂ (2 ^ Nat.clog 2 x) ≤
      8 * q₂ + 3 * 2 ^ Nat.clog 2 x + 4 := by
    unfold MatrixUnaryDivision.exactTime
    have h1 : q₂ / 2 ^ Nat.clog 2 x * 2 ^ Nat.clog 2 x ≤ q₂ := Nat.div_mul_le_self _ _
    have h2 : q₂ / 2 ^ Nat.clog 2 x ≤ q₂ := Nat.div_le_self _ _
    have e : q₂ / 2 ^ Nat.clog 2 x * (4 * 2 ^ Nat.clog 2 x + 4) =
        4 * (q₂ / 2 ^ Nat.clog 2 x * 2 ^ Nat.clog 2 x) + 4 * (q₂ / 2 ^ Nat.clog 2 x) := by ring
    omega
  have hquot : RepJoin.quot s q₂ g.edges.length ≤ q₂ := Nat.div_le_self _ _
  have he3 : ((EncodedGraph.encode g).length + 1) ^ 3 ≤ 8 * B ^ 3 := by
    have h' : ((EncodedGraph.encode g).length + 1) ^ 3 ≤ (2 * B) ^ 3 :=
      Nat.pow_le_pow_left (by omega) 3
    have e : (2 * B) ^ 3 = 8 * B ^ 3 := by ring
    omega
  have hsB : 2 * (12 * s) * g.edges.length ≤ 24 * B ^ 2 := by
    have e : 2 * (12 * s) * g.edges.length = 24 * (s * g.edges.length) := by ring
    omega
  unfold RepJoin.preBd RepProducer.repBd MatrixAddressMachine.exactTime
  rw [← hxdef]
  unfold PBc
  simp only [RepProducer.logBd] at *
  nlinarith [hlog, hdiv, h2c, hcl, hx, he3, hsB, hB2, hB3, hB4, hquot]

/-! ### The success program on the layout bank -/

section Prog

variable (FS : Type) [Fintype FS] [DecidableEq FS]

/-- The success-region cell of a `JT5` cell. -/
def sReg (x : RepJoin.JT5) : W FS := .inr (.inr (.inr (.inr (.inl x))))

/-- Layout position map of the success bank: its start region goes to the master start region,
its writer output cell to the common output cell, every other cell to its own success-region cell. -/
def sMap : RepJoin.JT5 → W FS ⊕ Fin 3
  | .inl (.inl (.inl (.inl o))) => .inl (.inr (.inl o))
  | .inl (.inl (.inl (.inr (.inl a)))) =>
      if a = wOut then .inl (.inl 2) else .inl (sReg FS (.inl (.inl (.inl (.inr (.inl a))))))
  | .inl (.inl (.inl (.inr (.inr y)))) => .inl (sReg FS (.inl (.inl (.inl (.inr (.inr y))))))
  | .inl (.inl (.inr p)) => .inl (sReg FS (.inl (.inl (.inr p))))
  | .inl (.inr t) => .inl (sReg FS (.inl (.inr t)))
  | .inr m => .inl (sReg FS (.inr m))

theorem sMap_injective : Function.Injective (sMap FS) := by
  intro x y h
  rcases x with (((x | (x | x)) | x) | x) | x <;> rcases y with (((y | (y | y)) | y) | y) | y <;>
    simp only [sMap, sReg] at h <;> (try split_ifs at h) <;> simp_all

def ιS : RepJoin.JT5 ↪ Fin (a FS + 3) :=
  ⟨fun x => pos FS (sMap FS x), fun x y h => sMap_injective FS (pos_injective FS h)⟩

theorem ιS_os (o : SuccessOrient.Stack) : ιS FS (RepJoin.os o) = ιOS FS o := rfl

theorem ιS_out : ιS FS (RepJoin.hj wOut) = outJ FS := by
  simp [ιS, sMap, RepJoin.hj, outJ]

theorem ιS_hj (a : JH WEntry.Kw) (ha : a ≠ wOut) :
    ιS FS (RepJoin.hj a) = pos FS (.inl (sReg FS (RepJoin.hj a))) := by
  simp [ιS, sMap, RepJoin.hj, ha]

/-- The single charged copy: packet cell 0 into the writer graph cell, scratch `ιS sc5`. -/
def cpS (_ : Fin 1) : Fin 3 ↪ Fin (a FS + 3) :=
  ⟨![pk FS 0, ιS FS (RepJoin.hj (mC zG)), ιS FS RepJoin.sc5], by
    intro x y h
    fin_cases x <;> fin_cases y <;>
      simp_all [pk, ιS, sMap, sReg, RepJoin.hj, RepJoin.sc5, mCzG_ne_wOut,
        (pos_injective FS).eq_iff]⟩

/-- **The success branch program.** -/
def sProg := BitMachineRawSequence.program (CopyAll.prog (cpS FS)) (liftP (ιS FS) RepJoin.repFull)
  (BitMachineRawSequence.leftLabel RepJoin.preStart) (none : Option Bool)
  (RepJoin.preCtl, RepJoin.fullCtl)

def PSs : ℕ := BitMachineStackGrowth.perStep (sProg FS)

end Prog

def sStart : BitMachineRawSequence.Label (CopyAll.Lab 1) (SuccessOrient.LabelOf RepJoin.repFull) :=
  BitMachineRawSequence.leftLabel (.inl ⟨0, by omega⟩)

def sCtl := ((none : Option Bool), (RepJoin.preCtl, RepJoin.fullCtl))

/-- Success branch exponent (the literal exponent of `Clocks.success_full_clock_HA3`, written out so that no
unifier ever compares it with another term: its atoms are finite-machine constants such as `perStep`, whose
evaluation is infeasible). -/
def SE (EM : ℕ) : ℕ := max (4 * max EM 14) (2 * (FallbackNoPreloadRun.noPreloadExponent +
  Paper2.SuccessClock2Pre.preExponent + Paper2.SuccessClock.entryExponent 2601 + 65))

/-- Success clock constant. -/
def SCk (CM : ℕ) : ℕ := 2 * CM + PBc * (CM + 4) ^ 4 + 8

/-- Success branch constant (clock and final bank size). -/
def SC (FS : Type) [Fintype FS] [DecidableEq FS] (CM : ℕ) : ℕ :=
  SCk CM + CM + 2 * (a FS + 3) * PSs FS * SCk CM

end

end Paper2.A3Assembly.Lift
