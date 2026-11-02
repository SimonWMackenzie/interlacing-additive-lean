import EthInapproximability.CurrentPaper.FamilyRowBody
import EthInapproximability.CurrentPaper.PrimeSamplerFamilyTableCoordinate

/-!
# Physical producer of both Stage-4 one-hot family tables

Lane owner:b-stage4-entry-program, segment 1 (loop and table identity).

ONE fixed controller `program`: a top label pops the unary row counter; while
it is nonempty the fixed row body `FamilyRowBody.bodyProgram` (inlined, its
halt redirected to the top label) processes row `r = counter`, prepending that
row's two one-hot words; on the empty counter the machine halts. Starting
from the counter `unary (L*q)` and two BLANK accumulators, the exit bank holds
exactly `fieldTable (familyFirst family)` and `fieldTable (familyRow family)`
for `family = PrimeSamplerFamilyTableCoordinate.actualFamily a q t rx hm`,
every operand word retained, every scratch cell blank, the counter empty.

No family value, table word or entry value is an input; every bit is written
by the production one-hot writer program `PrimeSamplerFamilyTableOneHot.program`
(NOT admitted: staged privately as `StagedFamilyTableOneHot`) from a value
computed by the admitted prime-polynomial accessor. Operand words (prime, `t`, `q`, `rx`, `qOne a`,
`qOne a * rx`) and the counter `L*q` are the declared inputs of this machine.
-/

namespace EthInapproximability.CurrentPaper.FamilyTableLoop

open Turing BitMachineEncoding FamilyRowBody FamilyRowGeneric
open Construction MatrixStage4FamilyData

abbrev Label := Unit ⊕ L1
abbrev Control := C1 × Option Bool

def embed (v : C1) : Control := (v, none)

def top : Label := .inl ()

def program : Label → TM2.Stmt (fun _ : Cell => Bool) Label Control
  | .inl () => .pop Cell.cnt (fun v b => (v.1, b))
      (.branch (fun v => v.2.isSome)
        (.load (fun _ => (i1, none)) (.goto (fun _ => .inr s1)))
        .halt)
  | .inr l => BitMachineInline.stmt Sum.inr embed Prod.fst (some top) (bodyProgram l)

theorem top_cons (v : Control) (S : Cell → List Bool) (k : ℕ)
    (hS : S .cnt = List.replicate (k + 1) true) :
    advance program (⟨some top, v, S⟩ : TM2.Cfg (fun _ : Cell => Bool) Label Control) =
      ⟨some (.inr s1), (i1, none), Function.update S .cnt (List.replicate k true)⟩ := by
  simp [advance, TM2.step, TM2.stepAux, program, top, hS, List.replicate_succ]

theorem top_nil (v : Control) (S : Cell → List Bool) (hS : S .cnt = []) :
    advance program (⟨some top, v, S⟩ : TM2.Cfg (fun _ : Cell => Bool) Label Control) =
      ⟨none, (v.1, none), S⟩ := by
  have hu : Function.update S Cell.cnt [] = S := by
    rw [← hS]; exact Function.update_eq_self _ _
  simp [advance, TM2.step, TM2.stepAux, program, top, hS, hu]

theorem update_cnt (r k P T Q RX Wd Md : ℕ) (A1 A2 : List Bool) :
    Function.update (rowBank r P T Q RX Wd Md A1 A2) Cell.cnt (List.replicate k true) =
      rowBank k P T Q RX Wd Md A1 A2 := by
  funext c
  cases c <;> rfl

theorem body_in_loop (r P T Q RX Wd Md : ℕ) (A1 A2 : List Bool)
    (hP : 0 < P) (hj : r % Q < P) (hl : r / Q < P ^ T) (hRX : 0 < RX)
    (hW : PrimeSampler.entry P T Md (r / Q) (r % Q) / RX < Wd) :
    ∃ n ≤ bodyTime r P T Q RX Wd Md,
      ((advance program)^[n])
        (⟨some (.inr s1), (i1, none), rowBank r P T Q RX Wd Md A1 A2⟩ :
          TM2.Cfg (fun _ : Cell => Bool) Label Control) =
        ⟨some top, (i1, none), rowBank r P T Q RX Wd Md
          (oneHot Wd ⟨PrimeSampler.entry P T Md (r / Q) (r % Q) / RX, hW⟩ ++ A1)
          (oneHot RX ⟨PrimeSampler.entry P T Md (r / Q) (r % Q) % RX,
            Nat.mod_lt _ hRX⟩ ++ A2)⟩ := by
  obtain ⟨t, ht, h⟩ := body_run r P T Q RX Wd Md A1 A2 hP hj hl hRX hW
  have hh : (((advance bodyProgram)^[t])
      (⟨some s1, i1, rowBank r P T Q RX Wd Md A1 A2⟩ :
        TM2.Cfg (fun _ : Cell => Bool) L1 C1)).l = none := by rw [h]
  obtain ⟨n, hn, hr⟩ := BitMachineInline.outputs Sum.inr embed Prod.fst
    (fun _ => rfl) (some top) bodyProgram program (fun _ => rfl)
    (⟨some s1, i1, rowBank r P T Q RX Wd Md A1 A2⟩ :
      TM2.Cfg (fun _ : Cell => Bool) L1 C1) t hh
  rw [h] at hr
  exact ⟨n, hn.trans ht, hr⟩

/-- The loop: from counter `k` with accumulators `acc k`, the SAME fixed
program halts with counter `0` and accumulators `acc 0`. -/
theorem loop_run (P T Q RX Wd Md U N : ℕ) (acc1 acc2 : ℕ → List Bool)
    (hstep : ∀ k < N, ∃ n ≤ U,
      ((advance program)^[n])
        (⟨some (.inr s1), (i1, none),
          rowBank k P T Q RX Wd Md (acc1 (k + 1)) (acc2 (k + 1))⟩ :
          TM2.Cfg (fun _ : Cell => Bool) Label Control) =
        ⟨some top, (i1, none), rowBank k P T Q RX Wd Md (acc1 k) (acc2 k)⟩) :
    ∀ k ≤ N, ∃ n ≤ k * (U + 1) + 1,
      ((advance program)^[n])
        (⟨some top, (i1, none), rowBank k P T Q RX Wd Md (acc1 k) (acc2 k)⟩ :
          TM2.Cfg (fun _ : Cell => Bool) Label Control) =
        ⟨none, (i1, none), rowBank 0 P T Q RX Wd Md (acc1 0) (acc2 0)⟩ := by
  intro k
  induction k with
  | zero =>
      intro _
      refine ⟨1, by omega, ?_⟩
      exact top_nil (i1, none) (rowBank 0 P T Q RX Wd Md (acc1 0) (acc2 0)) rfl
  | succ k ih =>
      intro hk
      obtain ⟨n₂, hn₂, h₂⟩ := ih (by omega)
      obtain ⟨n₁, hn₁, h₁⟩ := hstep k (by omega)
      have h₀ := top_cons (i1, none)
        (rowBank (k + 1) P T Q RX Wd Md (acc1 (k + 1)) (acc2 (k + 1))) k rfl
      rw [update_cnt] at h₀
      refine ⟨n₂ + n₁ + 1, ?_, ?_⟩
      · have : (k + 1) * (U + 1) + 1 = k * (U + 1) + 1 + (U + 1) := by ring
        omega
      · rw [Function.iterate_add_apply, Function.iterate_add_apply,
          Function.iterate_one, h₀, h₁, h₂]

/-! ## Table identity -/

theorem drop_fieldTable {rows m : ℕ} (f : Fin rows → Fin m) (k : ℕ) (hk : k < rows) :
    List.drop (k * m) (fieldTable f) =
      oneHot m (f ⟨k, hk⟩) ++ List.drop ((k + 1) * m) (fieldTable f) := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_drop]
  by_cases hi : i < m
  · rw [List.getElem?_append_left (by simp; exact hi)]
    have he := MatrixMaterialization.rowMajor_entry
      (fun r (j : Fin m) => (oneHot m (f r)).get ⟨j.val, by rw [oneHot_length]; exact j.isLt⟩)
      ⟨k, hk⟩ ⟨i, hi⟩
    unfold fieldTable
    rw [he]
    simp [List.getElem?_eq_getElem (show i < (oneHot m (f ⟨k, hk⟩)).length by simp; exact hi)]
  · rw [List.getElem?_append_right (by simp; omega), List.getElem?_drop]
    congr 1
    simp only [oneHot_length, Nat.succ_mul]
    omega

theorem drop_fieldTable_last {rows m : ℕ} (f : Fin rows → Fin m) :
    List.drop (rows * m) (fieldTable f) = [] := by
  apply List.drop_of_length_le
  simp

theorem row_coordinates (a q t rx : ℕ) (hm : 0 < qOne a * rx) (hrx : 0 < rx)
    (k : ℕ) (hk : k < PrimeSampler.size q t (qOne a * rx) * q) :
    let family := PrimeSamplerFamilyTableCoordinate.actualFamily a q t rx hm
    let p := PrimeSampler.prime q t (qOne a * rx)
    (familyFirst family ⟨k, hk⟩).val =
      PrimeSampler.entry p t (qOne a * rx) (k / q) (k % q) / rx ∧
    (familyRow family ⟨k, hk⟩).val =
      PrimeSampler.entry p t (qOne a * rx) (k / q) (k % q) % rx := by
  intro family p
  have hq : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h; simp at hk
    · exact h
  have hl : k / q < PrimeSampler.size q t (qOne a * rx) :=
    (Nat.div_lt_iff_lt_mul hq).2 hk
  let ℓ : Fin (PrimeSampler.size q t (qOne a * rx)) := ⟨k / q, hl⟩
  let α : Fin q := ⟨k % q, Nat.mod_lt _ hq⟩
  have hidx : finProdFinEquiv (ℓ, α) = (⟨k, hk⟩ : Fin _) := by
    apply Fin.ext
    simp only [finProdFinEquiv_apply_val, ℓ, α]
    exact Nat.mod_add_div k q
  have hc := PrimeSamplerFamilyTableCoordinate.field_coordinates a q t rx hm hrx ℓ α
  rw [hidx] at hc
  exact hc

/-- Upper bound on the per-row clock, uniform over the rows `r < N`. -/
def bodyBound (N P T Q RX Wd Md : ℕ) : ℕ :=
  (2 * N + 2) + (8 * N + 3 * Q + 4) + (2 * P + 2) + (2 * T + 2) + (2 * Md + 2) +
    500 * (T + N + P + N + Md + 1) ^ 3 + (8 * Md + 3 * RX + 4) + (2 * Wd + 2) +
    (2 * Wd + 5) + (2 * RX + 2) + (2 * RX + 5) + (P + P + P + Md + 6) + 11

theorem bodyTime_le (N r P T Q RX Wd Md : ℕ) (hr : r < N) (hP : 0 < P)
    (hj : r % Q < P) (hRX : 0 < RX)
    (he : PrimeSampler.entry P T Md (r / Q) (r % Q) < Md)
    (hW : PrimeSampler.entry P T Md (r / Q) (r % Q) / RX < Wd) :
    bodyTime r P T Q RX Wd Md ≤ bodyBound N P T Q RX Wd Md := by
  have h1 := MatrixUnaryDivision.totalTime_bound r Q
  have h2 := PrimeSamplerEntryMachine.timeBound_polynomial P T (r / Q) (r % Q) Md
  have hdiv : r / Q ≤ N := (Nat.div_le_self r Q).trans hr.le
  have hmod : r % Q ≤ N := (Nat.mod_le r Q).trans hr.le
  have h3 : 500 * (T + r / Q + P + r % Q + Md + 1) ^ 3 ≤
      500 * (T + N + P + N + Md + 1) ^ 3 :=
    Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left (by omega) 3)
  have h4 := MatrixUnaryDivision.totalTime_bound
    (PrimeSampler.entry P T Md (r / Q) (r % Q)) RX
  have h5 : PrimeSampler.entry P T Md (r / Q) (r % Q) % RX < RX := Nat.mod_lt _ hRX
  have h6 := PrimeSamplerEntryAlgorithm.horner_lt P (r % Q) T (r / Q) hP
  have h7 : PrimeSamplerEntryAlgorithm.horner P (r % Q) T (r / Q) / Md ≤
      PrimeSamplerEntryAlgorithm.horner P (r % Q) T (r / Q) := Nat.div_le_self _ _
  unfold bodyTime bodyBound ohTime
  omega

/-- Segment 1 main theorem: the fixed producer writes both literal one-hot
family tables of the actual prime family. -/
theorem family_tables (a q t rx : ℕ) (hm : 0 < qOne a * rx) (hrx : 0 < rx) :
    let m := qOne a * rx
    let p := PrimeSampler.prime q t m
    let N := PrimeSampler.size q t m * q
    let family := PrimeSamplerFamilyTableCoordinate.actualFamily a q t rx hm
    ∃ n ≤ N * (bodyBound N p t q rx (qOne a) m + 1) + 1,
      ((advance program)^[n])
        (⟨some top, (i1, none), rowBank N p t q rx (qOne a) m [] []⟩ :
          TM2.Cfg (fun _ : Cell => Bool) Label Control) =
        ⟨none, (i1, none), rowBank 0 p t q rx (qOne a) m
          (fieldTable (familyFirst family)) (fieldTable (familyRow family))⟩ := by
  intro m p N family
  let acc1 : ℕ → List Bool := fun k => List.drop (k * qOne a) (fieldTable (familyFirst family))
  let acc2 : ℕ → List Bool := fun k => List.drop (k * rx) (fieldTable (familyRow family))
  have hpprime := PrimeSampler.prime_isPrime q t m
  have hP : 0 < p := hpprime.pos
  have hstep : ∀ k < N, ∃ n ≤ bodyBound N p t q rx (qOne a) m,
      ((advance program)^[n])
        (⟨some (.inr s1), (i1, none),
          rowBank k p t q rx (qOne a) m (acc1 (k + 1)) (acc2 (k + 1))⟩ :
          TM2.Cfg (fun _ : Cell => Bool) Label Control) =
        ⟨some top, (i1, none), rowBank k p t q rx (qOne a) m (acc1 k) (acc2 k)⟩ := by
    intro k hk
    have hq : 0 < q := by
      rcases Nat.eq_zero_or_pos q with h | h
      · subst h; simp [N] at hk
      · exact h
    have hthr : q ≤ p := by
      have hw := (PrimeSampler.prime_window q t m).1
      have : q ≤ PrimeSampler.threshold q t m := by
        unfold PrimeSampler.threshold
        exact (le_max_left _ _).trans (le_max_left _ _)
      exact this.trans hw
    have hj : k % q < p := (Nat.mod_lt _ hq).trans_le hthr
    have hl : k / q < p ^ t := by
      rw [← PrimeSampler.size_exact]
      exact (Nat.div_lt_iff_lt_mul hq).2 hk
    have he : PrimeSampler.entry p t m (k / q) (k % q) < m := by
      rw [← PrimeSamplerEntryAlgorithm.entry_eq]
      exact Nat.mod_lt _ hm
    have hW : PrimeSampler.entry p t m (k / q) (k % q) / rx < qOne a :=
      (Nat.div_lt_iff_lt_mul hrx).2 he
    obtain ⟨n, hn, hrun⟩ := body_in_loop k p t q rx (qOne a) m
      (acc1 (k + 1)) (acc2 (k + 1)) hP hj hl hrx hW
    obtain ⟨hc1, hc2⟩ := row_coordinates a q t rx hm hrx k hk
    have hb := bodyTime_le N k p t q rx (qOne a) m hk hP hj hrx he hW
    refine ⟨n, hn.trans hb, ?_⟩
    rw [hrun]
    have e1 : oneHot (qOne a) ⟨PrimeSampler.entry p t m (k / q) (k % q) / rx, hW⟩ ++
        acc1 (k + 1) = acc1 k := by
      simp only [acc1]
      rw [drop_fieldTable (familyFirst family) k hk]
      congr 2
    have e2 : oneHot rx ⟨PrimeSampler.entry p t m (k / q) (k % q) % rx,
        Nat.mod_lt _ hrx⟩ ++ acc2 (k + 1) = acc2 k := by
      simp only [acc2]
      rw [drop_fieldTable (familyRow family) k hk]
      congr 2
    rw [e1, e2]
  obtain ⟨n, hn, hrun⟩ := loop_run p t q rx (qOne a) m
    (bodyBound N p t q rx (qOne a) m) N acc1 acc2 hstep N le_rfl
  refine ⟨n, hn, ?_⟩
  have hN1 : acc1 N = [] := drop_fieldTable_last (familyFirst family)
  have hN2 : acc2 N = [] := drop_fieldTable_last (familyRow family)
  have h01 : acc1 0 = fieldTable (familyFirst family) := by simp [acc1]
  have h02 : acc2 0 = fieldTable (familyRow family) := by simp [acc2]
  rw [hN1, hN2, h01, h02] at hrun
  exact hrun

#print axioms top_cons
#print axioms top_nil
#print axioms body_in_loop
#print axioms loop_run
#print axioms drop_fieldTable
#print axioms row_coordinates
#print axioms bodyTime_le
#print axioms family_tables

end EthInapproximability.CurrentPaper.FamilyTableLoop
