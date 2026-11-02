import Paper2.TagDispatch
import EthInapproximability.CurrentPaper.BitMachineRawSequence
import EthInapproximability.CurrentPaper.BitMachineInline

/-!
# Unit 3 endpoint, segment 3: the bit-branch combinators and the dispatch program

Lane `owner:a-h-a3-assembly-2` (private, 26 September 2026). Paper A, lock v12.

* **Bit-branch combinator.** It is the admitted `TagDispatch.ifProgram`: ONE fixed program that pops a dispatch bit from a named
  cell of a shared bank and continues with one of two programs. The pop is charged one step, and each branch is inlined by the
  production `BitMachineInline.stmt` (`TagDispatch.if_false`, `TagDispatch.if_true`). It is used here unchanged.
* **Status push (new, `spProg`).** It runs a program `A` inlined, then makes ONE charged transition that pushes the Boolean
  `ok v` of `A`'s actual final finite control `v` onto a named cell. This is how the some/none outcome of the admitted generator
  run becomes a physical dispatch bit (route (i)). The bit is read from finite control, never supplied.
* **Dispatch (`dispatchProg`).** It is ONE fixed program over arbitrary component programs:
  `Pc ; if cBit then (Pp ; spProg Pd ok oBit ; if oBit then Ps else Pn) else Pu`.
  Sequencing is production `BitMachineRawSequence`, the branches are `TagDispatch.ifProgram`, and every handoff is charged.
  `dispatch_unsched`, `dispatch_none` and `dispatch_some` give the exact exit bank and the explicit clock on each of the three paths
  from the component run specifications.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

namespace Paper2.A3Assembly.Dispatch

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open BitMachineRawSequence (leftLabel)

/-! ### Status push -/

section SP

variable {K LA VA : Type*} [DecidableEq K]

abbrev SPLabel (LA : Type*) := LA ⊕ Unit

def spProg (A : LA → TM2.Stmt (fun _ : K => Bool) LA VA) (ok : VA → Bool) (cell : K) :
    SPLabel LA → TM2.Stmt (fun _ : K => Bool) (SPLabel LA) VA
  | .inl l => BitMachineInline.stmt Sum.inl id id (some (.inr ())) (A l)
  | .inr _ => push cell (fun v => ok v) halt

theorem sp_push (A : LA → TM2.Stmt (fun _ : K => Bool) LA VA) (ok : VA → Bool) (cell : K)
    (v : VA) (T : K → List Bool) :
    advance (spProg A ok cell)
        (⟨some (.inr ()), v, T⟩ : TM2.Cfg (fun _ : K => Bool) (SPLabel LA) VA) =
      ⟨none, v, Function.update T cell (ok v :: T cell)⟩ := by
  simp [advance, TM2.step, TM2.stepAux, spProg]

/-- The status push: `A`'s run, then ONE charged push of `ok` of its actual final control. -/
theorem sp_run (A : LA → TM2.Stmt (fun _ : K => Bool) LA VA) (ok : VA → Bool) (cell : K)
    (a₀ : LA) (u v₁ : VA) (S T : K → List Bool) (ta : ℕ)
    (ha : ((advance A)^[ta]) (⟨some a₀, u, S⟩ : TM2.Cfg (fun _ : K => Bool) LA VA) =
      ⟨none, v₁, T⟩) :
    ∃ t ≤ ta + 1, ((advance (spProg A ok cell))^[t])
        (⟨some (.inl a₀), u, S⟩ : TM2.Cfg (fun _ : K => Bool) (SPLabel LA) VA) =
      ⟨none, v₁, Function.update T cell (ok v₁ :: T cell)⟩ := by
  have hah : (((advance A)^[ta])
      (⟨some a₀, u, S⟩ : TM2.Cfg (fun _ : K => Bool) LA VA)).l = none := by rw [ha]
  obtain ⟨a, hat, har⟩ := BitMachineInline.outputs (Sum.inl : LA → SPLabel LA) (id : VA → VA) id
    (fun _ => rfl) (some (.inr ())) A (spProg A ok cell) (fun _ => rfl)
    (⟨some a₀, u, S⟩ : TM2.Cfg (fun _ : K => Bool) LA VA) ta hah
  rw [ha] at har
  simp only [BitMachineInline.cfg, id] at har
  refine ⟨a + 1, by omega, ?_⟩
  rw [Function.iterate_succ_apply', har]
  exact sp_push A ok cell v₁ T

end SP

/-! ### The dispatch program -/

section D

variable {K : Type*} [DecidableEq K]
variable {LC VC LU VU LP VP LD VD LN VN LS VS : Type*}

/-- Scheduled branch: preparation, status push of the decision run, then the outcome branch. -/
def schedProg (Pp : LP → TM2.Stmt (fun _ : K => Bool) LP VP)
    (Pd : LD → TM2.Stmt (fun _ : K => Bool) LD VD) (ok : VD → Bool) (oBit : K)
    (Pn : LN → TM2.Stmt (fun _ : K => Bool) LN VN)
    (Ps : LS → TM2.Stmt (fun _ : K => Bool) LS VS)
    (d₀ : LD) (n₀ : LN) (s₀ : LS) (vp₀ : VP) (vd₀ : VD) (vn₀ : VN) (vs₀ : VS) :=
  BitMachineRawSequence.program
    (BitMachineRawSequence.program Pp (spProg Pd ok oBit) (.inl d₀) vp₀ vd₀)
    (TagDispatch.ifProgram oBit Pn Ps n₀ s₀ vn₀ vs₀) (.inl ()) (vp₀, vd₀)
    ((none : Option Bool), (vn₀, vs₀))

/-- ONE fixed dispatch program. -/
def dispatchProg (Pc : LC → TM2.Stmt (fun _ : K => Bool) LC VC) (cBit : K)
    (Pu : LU → TM2.Stmt (fun _ : K => Bool) LU VU)
    (Pp : LP → TM2.Stmt (fun _ : K => Bool) LP VP)
    (Pd : LD → TM2.Stmt (fun _ : K => Bool) LD VD) (ok : VD → Bool) (oBit : K)
    (Pn : LN → TM2.Stmt (fun _ : K => Bool) LN VN)
    (Ps : LS → TM2.Stmt (fun _ : K => Bool) LS VS)
    (u₀ : LU) (p₀ : LP) (d₀ : LD) (n₀ : LN) (s₀ : LS)
    (vc₀ : VC) (vu₀ : VU) (vp₀ : VP) (vd₀ : VD) (vn₀ : VN) (vs₀ : VS) :=
  BitMachineRawSequence.program Pc
    (TagDispatch.ifProgram cBit Pu (schedProg Pp Pd ok oBit Pn Ps d₀ n₀ s₀ vp₀ vd₀ vn₀ vs₀)
      u₀ (leftLabel (leftLabel p₀)) vu₀ ((vp₀, vd₀), ((none : Option Bool), (vn₀, vs₀))))
    (.inl ()) vc₀ ((none : Option Bool), (vu₀, ((vp₀, vd₀), ((none : Option Bool), (vn₀, vs₀)))))

theorem pop_back (T : K → List Bool) (cell : K) (b : Bool) :
    Function.update (Function.update T cell (b :: T cell)) cell (T cell) = T := by
  rw [Function.update_idem, Function.update_eq_self]

/-- Scheduled branch on the outcome `ok vd₁ = false` (none). -/
theorem sched_none (Pp : LP → TM2.Stmt (fun _ : K => Bool) LP VP)
    (Pd : LD → TM2.Stmt (fun _ : K => Bool) LD VD) (ok : VD → Bool) (oBit : K)
    (Pn : LN → TM2.Stmt (fun _ : K => Bool) LN VN)
    (Ps : LS → TM2.Stmt (fun _ : K => Bool) LS VS)
    (p₀ : LP) (d₀ : LD) (n₀ : LN) (s₀ : LS) (vp₀ vp₁ : VP) (vd₀ vd₁ : VD) (vn₀ vn₁ : VN)
    (vs₀ : VS) (S Ep Ed En : K → List Bool) (tp td tn : ℕ)
    (hp : ((advance Pp)^[tp]) (⟨some p₀, vp₀, S⟩ : TM2.Cfg (fun _ : K => Bool) LP VP) =
      ⟨none, vp₁, Ep⟩)
    (hd : ((advance Pd)^[td]) (⟨some d₀, vd₀, Ep⟩ : TM2.Cfg (fun _ : K => Bool) LD VD) =
      ⟨none, vd₁, Ed⟩)
    (hok : ok vd₁ = false)
    (hn : ((advance Pn)^[tn]) (⟨some n₀, vn₀, Ed⟩ : TM2.Cfg (fun _ : K => Bool) LN VN) =
      ⟨none, vn₁, En⟩) :
    ∃ t ≤ (tp + (td + 1) + 1) + (tn + 1) + 1,
      ((advance (schedProg Pp Pd ok oBit Pn Ps d₀ n₀ s₀ vp₀ vd₀ vn₀ vs₀))^[t])
        (⟨some (leftLabel (leftLabel p₀)), ((vp₀, vd₀), ((none : Option Bool), (vn₀, vs₀))), S⟩ :
          TM2.Cfg (fun _ : K => Bool) _ _) =
        ⟨none, ((vp₀, vd₀), (some false, (vn₁, vs₀))), En⟩ := by
  obtain ⟨t1, ht1, r1⟩ := sp_run Pd ok oBit d₀ vd₀ vd₁ Ep Ed td hd
  rw [hok] at r1
  obtain ⟨t2, ht2, r2⟩ := BitMachineRawSequence.runs Pp (spProg Pd ok oBit) p₀ (.inl d₀)
    vp₀ vp₁ vd₀ vd₁ S Ep _ tp t1 hp r1
  have hn' : ((advance Pn)^[tn]) (⟨some n₀, vn₀,
      Function.update (Function.update Ed oBit (false :: Ed oBit)) oBit (Ed oBit)⟩ :
        TM2.Cfg (fun _ : K => Bool) LN VN) = ⟨none, vn₁, En⟩ := by
    rw [pop_back]; exact hn
  obtain ⟨t3, ht3, r3⟩ := TagDispatch.if_false oBit Pn Ps n₀ s₀ vn₀ vs₀
    (Function.update Ed oBit (false :: Ed oBit)) (Ed oBit) (by rw [Function.update_self])
    tn vn₁ En hn'
  obtain ⟨t4, ht4, r4⟩ := BitMachineRawSequence.runs
    (BitMachineRawSequence.program Pp (spProg Pd ok oBit) (.inl d₀) vp₀ vd₀)
    (TagDispatch.ifProgram oBit Pn Ps n₀ s₀ vn₀ vs₀) (leftLabel p₀) (.inl ())
    (vp₀, vd₀) (vp₀, vd₁) ((none : Option Bool), (vn₀, vs₀)) (some false, (vn₁, vs₀))
    S _ En t2 t3 r2 r3
  exact ⟨t4, by omega, r4⟩

/-- Scheduled branch on the outcome `ok vd₁ = true` (some). -/
theorem sched_some (Pp : LP → TM2.Stmt (fun _ : K => Bool) LP VP)
    (Pd : LD → TM2.Stmt (fun _ : K => Bool) LD VD) (ok : VD → Bool) (oBit : K)
    (Pn : LN → TM2.Stmt (fun _ : K => Bool) LN VN)
    (Ps : LS → TM2.Stmt (fun _ : K => Bool) LS VS)
    (p₀ : LP) (d₀ : LD) (n₀ : LN) (s₀ : LS) (vp₀ vp₁ : VP) (vd₀ vd₁ : VD) (vn₀ : VN)
    (vs₀ vs₁ : VS) (S Ep Ed Es : K → List Bool) (tp td ts : ℕ)
    (hp : ((advance Pp)^[tp]) (⟨some p₀, vp₀, S⟩ : TM2.Cfg (fun _ : K => Bool) LP VP) =
      ⟨none, vp₁, Ep⟩)
    (hd : ((advance Pd)^[td]) (⟨some d₀, vd₀, Ep⟩ : TM2.Cfg (fun _ : K => Bool) LD VD) =
      ⟨none, vd₁, Ed⟩)
    (hok : ok vd₁ = true)
    (hs : ((advance Ps)^[ts]) (⟨some s₀, vs₀, Ed⟩ : TM2.Cfg (fun _ : K => Bool) LS VS) =
      ⟨none, vs₁, Es⟩) :
    ∃ t ≤ (tp + (td + 1) + 1) + (ts + 1) + 1,
      ((advance (schedProg Pp Pd ok oBit Pn Ps d₀ n₀ s₀ vp₀ vd₀ vn₀ vs₀))^[t])
        (⟨some (leftLabel (leftLabel p₀)), ((vp₀, vd₀), ((none : Option Bool), (vn₀, vs₀))), S⟩ :
          TM2.Cfg (fun _ : K => Bool) _ _) =
        ⟨none, ((vp₀, vd₀), (some true, (vn₀, vs₁))), Es⟩ := by
  obtain ⟨t1, ht1, r1⟩ := sp_run Pd ok oBit d₀ vd₀ vd₁ Ep Ed td hd
  rw [hok] at r1
  obtain ⟨t2, ht2, r2⟩ := BitMachineRawSequence.runs Pp (spProg Pd ok oBit) p₀ (.inl d₀)
    vp₀ vp₁ vd₀ vd₁ S Ep _ tp t1 hp r1
  have hs' : ((advance Ps)^[ts]) (⟨some s₀, vs₀,
      Function.update (Function.update Ed oBit (true :: Ed oBit)) oBit (Ed oBit)⟩ :
        TM2.Cfg (fun _ : K => Bool) LS VS) = ⟨none, vs₁, Es⟩ := by
    rw [pop_back]; exact hs
  obtain ⟨t3, ht3, r3⟩ := TagDispatch.if_true oBit Pn Ps n₀ s₀ vn₀ vs₀
    (Function.update Ed oBit (true :: Ed oBit)) (Ed oBit) (by rw [Function.update_self])
    ts vs₁ Es hs'
  obtain ⟨t4, ht4, r4⟩ := BitMachineRawSequence.runs
    (BitMachineRawSequence.program Pp (spProg Pd ok oBit) (.inl d₀) vp₀ vd₀)
    (TagDispatch.ifProgram oBit Pn Ps n₀ s₀ vn₀ vs₀) (leftLabel p₀) (.inl ())
    (vp₀, vd₀) (vp₀, vd₁) ((none : Option Bool), (vn₀, vs₀)) (some true, (vn₀, vs₁))
    S _ Es t2 t3 r2 r3
  exact ⟨t4, by omega, r4⟩

/-- **Dispatch, unscheduled path**: the Checks-bit producer leaves `false` on `cBit`. -/
theorem dispatch_unsched (Pc : LC → TM2.Stmt (fun _ : K => Bool) LC VC) (cBit : K)
    (Pu : LU → TM2.Stmt (fun _ : K => Bool) LU VU)
    (Pp : LP → TM2.Stmt (fun _ : K => Bool) LP VP)
    (Pd : LD → TM2.Stmt (fun _ : K => Bool) LD VD) (ok : VD → Bool) (oBit : K)
    (Pn : LN → TM2.Stmt (fun _ : K => Bool) LN VN)
    (Ps : LS → TM2.Stmt (fun _ : K => Bool) LS VS)
    (c₀ : LC) (u₀ : LU) (p₀ : LP) (d₀ : LD) (n₀ : LN) (s₀ : LS)
    (vc₀ vc₁ : VC) (vu₀ vu₁ : VU) (vp₀ : VP) (vd₀ : VD) (vn₀ : VN) (vs₀ : VS)
    (E0 Ec Eu : K → List Bool) (w : List Bool) (tc tu : ℕ)
    (hc : ((advance Pc)^[tc]) (⟨some c₀, vc₀, E0⟩ : TM2.Cfg (fun _ : K => Bool) LC VC) =
      ⟨none, vc₁, Ec⟩)
    (hbit : Ec cBit = false :: w)
    (hu : ((advance Pu)^[tu]) (⟨some u₀, vu₀, Function.update Ec cBit w⟩ :
      TM2.Cfg (fun _ : K => Bool) LU VU) = ⟨none, vu₁, Eu⟩) :
    ∃ t ≤ tc + (tu + 1) + 1, ∃ v,
      ((advance (dispatchProg Pc cBit Pu Pp Pd ok oBit Pn Ps u₀ p₀ d₀ n₀ s₀
          vc₀ vu₀ vp₀ vd₀ vn₀ vs₀))^[t])
        (⟨some (leftLabel c₀), (vc₀, ((none : Option Bool), (vu₀, ((vp₀, vd₀),
            ((none : Option Bool), (vn₀, vs₀)))))), E0⟩ : TM2.Cfg (fun _ : K => Bool) _ _) =
        ⟨none, v, Eu⟩ := by
  obtain ⟨t1, ht1, r1⟩ := TagDispatch.if_false cBit Pu
    (schedProg Pp Pd ok oBit Pn Ps d₀ n₀ s₀ vp₀ vd₀ vn₀ vs₀) u₀ (leftLabel (leftLabel p₀)) vu₀
    ((vp₀, vd₀), ((none : Option Bool), (vn₀, vs₀))) Ec w hbit tu vu₁ Eu hu
  obtain ⟨t2, ht2, r2⟩ := BitMachineRawSequence.runs Pc
    (TagDispatch.ifProgram cBit Pu (schedProg Pp Pd ok oBit Pn Ps d₀ n₀ s₀ vp₀ vd₀ vn₀ vs₀)
      u₀ (leftLabel (leftLabel p₀)) vu₀ ((vp₀, vd₀), ((none : Option Bool), (vn₀, vs₀))))
    c₀ (.inl ()) vc₀ vc₁ _ _ E0 Ec Eu
    tc t1 hc r1
  exact ⟨t2, by omega, _, r2⟩

/-- **Dispatch, scheduled path, none outcome.** -/
theorem dispatch_none (Pc : LC → TM2.Stmt (fun _ : K => Bool) LC VC) (cBit : K)
    (Pu : LU → TM2.Stmt (fun _ : K => Bool) LU VU)
    (Pp : LP → TM2.Stmt (fun _ : K => Bool) LP VP)
    (Pd : LD → TM2.Stmt (fun _ : K => Bool) LD VD) (ok : VD → Bool) (oBit : K)
    (Pn : LN → TM2.Stmt (fun _ : K => Bool) LN VN)
    (Ps : LS → TM2.Stmt (fun _ : K => Bool) LS VS)
    (c₀ : LC) (u₀ : LU) (p₀ : LP) (d₀ : LD) (n₀ : LN) (s₀ : LS)
    (vc₀ vc₁ : VC) (vu₀ : VU) (vp₀ vp₁ : VP) (vd₀ vd₁ : VD) (vn₀ vn₁ : VN) (vs₀ : VS)
    (E0 Ec Ep Ed En : K → List Bool) (w : List Bool) (tc tp td tn : ℕ)
    (hc : ((advance Pc)^[tc]) (⟨some c₀, vc₀, E0⟩ : TM2.Cfg (fun _ : K => Bool) LC VC) =
      ⟨none, vc₁, Ec⟩)
    (hbit : Ec cBit = true :: w)
    (hp : ((advance Pp)^[tp]) (⟨some p₀, vp₀, Function.update Ec cBit w⟩ :
      TM2.Cfg (fun _ : K => Bool) LP VP) = ⟨none, vp₁, Ep⟩)
    (hd : ((advance Pd)^[td]) (⟨some d₀, vd₀, Ep⟩ : TM2.Cfg (fun _ : K => Bool) LD VD) =
      ⟨none, vd₁, Ed⟩)
    (hok : ok vd₁ = false)
    (hn : ((advance Pn)^[tn]) (⟨some n₀, vn₀, Ed⟩ : TM2.Cfg (fun _ : K => Bool) LN VN) =
      ⟨none, vn₁, En⟩) :
    ∃ t ≤ tc + ((tp + (td + 1) + 1) + (tn + 1) + 1 + 1) + 1, ∃ v,
      ((advance (dispatchProg Pc cBit Pu Pp Pd ok oBit Pn Ps u₀ p₀ d₀ n₀ s₀
          vc₀ vu₀ vp₀ vd₀ vn₀ vs₀))^[t])
        (⟨some (leftLabel c₀), (vc₀, ((none : Option Bool), (vu₀, ((vp₀, vd₀),
            ((none : Option Bool), (vn₀, vs₀)))))), E0⟩ : TM2.Cfg (fun _ : K => Bool) _ _) =
        ⟨none, v, En⟩ := by
  obtain ⟨t0, ht0, r0⟩ := sched_none Pp Pd ok oBit Pn Ps p₀ d₀ n₀ s₀ vp₀ vp₁ vd₀ vd₁ vn₀ vn₁ vs₀
    (Function.update Ec cBit w) Ep Ed En tp td tn hp hd hok hn
  obtain ⟨t1, ht1, r1⟩ := TagDispatch.if_true cBit Pu
    (schedProg Pp Pd ok oBit Pn Ps d₀ n₀ s₀ vp₀ vd₀ vn₀ vs₀) u₀ (leftLabel (leftLabel p₀)) vu₀
    ((vp₀, vd₀), ((none : Option Bool), (vn₀, vs₀))) Ec w hbit t0 _ En r0
  obtain ⟨t2, ht2, r2⟩ := BitMachineRawSequence.runs Pc
    (TagDispatch.ifProgram cBit Pu (schedProg Pp Pd ok oBit Pn Ps d₀ n₀ s₀ vp₀ vd₀ vn₀ vs₀)
      u₀ (leftLabel (leftLabel p₀)) vu₀ ((vp₀, vd₀), ((none : Option Bool), (vn₀, vs₀))))
    c₀ (.inl ()) vc₀ vc₁ _ _ E0 Ec En
    tc t1 hc r1
  exact ⟨t2, by omega, _, r2⟩

/-- **Dispatch, scheduled path, some outcome.** -/
theorem dispatch_some (Pc : LC → TM2.Stmt (fun _ : K => Bool) LC VC) (cBit : K)
    (Pu : LU → TM2.Stmt (fun _ : K => Bool) LU VU)
    (Pp : LP → TM2.Stmt (fun _ : K => Bool) LP VP)
    (Pd : LD → TM2.Stmt (fun _ : K => Bool) LD VD) (ok : VD → Bool) (oBit : K)
    (Pn : LN → TM2.Stmt (fun _ : K => Bool) LN VN)
    (Ps : LS → TM2.Stmt (fun _ : K => Bool) LS VS)
    (c₀ : LC) (u₀ : LU) (p₀ : LP) (d₀ : LD) (n₀ : LN) (s₀ : LS)
    (vc₀ vc₁ : VC) (vu₀ : VU) (vp₀ vp₁ : VP) (vd₀ vd₁ : VD) (vn₀ : VN) (vs₀ vs₁ : VS)
    (E0 Ec Ep Ed Es : K → List Bool) (w : List Bool) (tc tp td ts : ℕ)
    (hc : ((advance Pc)^[tc]) (⟨some c₀, vc₀, E0⟩ : TM2.Cfg (fun _ : K => Bool) LC VC) =
      ⟨none, vc₁, Ec⟩)
    (hbit : Ec cBit = true :: w)
    (hp : ((advance Pp)^[tp]) (⟨some p₀, vp₀, Function.update Ec cBit w⟩ :
      TM2.Cfg (fun _ : K => Bool) LP VP) = ⟨none, vp₁, Ep⟩)
    (hd : ((advance Pd)^[td]) (⟨some d₀, vd₀, Ep⟩ : TM2.Cfg (fun _ : K => Bool) LD VD) =
      ⟨none, vd₁, Ed⟩)
    (hok : ok vd₁ = true)
    (hs : ((advance Ps)^[ts]) (⟨some s₀, vs₀, Ed⟩ : TM2.Cfg (fun _ : K => Bool) LS VS) =
      ⟨none, vs₁, Es⟩) :
    ∃ t ≤ tc + ((tp + (td + 1) + 1) + (ts + 1) + 1 + 1) + 1, ∃ v,
      ((advance (dispatchProg Pc cBit Pu Pp Pd ok oBit Pn Ps u₀ p₀ d₀ n₀ s₀
          vc₀ vu₀ vp₀ vd₀ vn₀ vs₀))^[t])
        (⟨some (leftLabel c₀), (vc₀, ((none : Option Bool), (vu₀, ((vp₀, vd₀),
            ((none : Option Bool), (vn₀, vs₀)))))), E0⟩ : TM2.Cfg (fun _ : K => Bool) _ _) =
        ⟨none, v, Es⟩ := by
  obtain ⟨t0, ht0, r0⟩ := sched_some Pp Pd ok oBit Pn Ps p₀ d₀ n₀ s₀ vp₀ vp₁ vd₀ vd₁ vn₀ vs₀ vs₁
    (Function.update Ec cBit w) Ep Ed Es tp td ts hp hd hok hs
  obtain ⟨t1, ht1, r1⟩ := TagDispatch.if_true cBit Pu
    (schedProg Pp Pd ok oBit Pn Ps d₀ n₀ s₀ vp₀ vd₀ vn₀ vs₀) u₀ (leftLabel (leftLabel p₀)) vu₀
    ((vp₀, vd₀), ((none : Option Bool), (vn₀, vs₀))) Ec w hbit t0 _ Es r0
  obtain ⟨t2, ht2, r2⟩ := BitMachineRawSequence.runs Pc
    (TagDispatch.ifProgram cBit Pu (schedProg Pp Pd ok oBit Pn Ps d₀ n₀ s₀ vp₀ vd₀ vn₀ vs₀)
      u₀ (leftLabel (leftLabel p₀)) vu₀ ((vp₀, vd₀), ((none : Option Bool), (vn₀, vs₀))))
    c₀ (.inl ()) vc₀ vc₁ _ _ E0 Ec Es
    tc t1 hc r1
  exact ⟨t2, by omega, _, r2⟩

end D

#print axioms sp_push
#print axioms sp_run
#print axioms sched_none
#print axioms sched_some
#print axioms dispatch_unsched
#print axioms dispatch_none
#print axioms dispatch_some

end Paper2.A3Assembly.Dispatch
