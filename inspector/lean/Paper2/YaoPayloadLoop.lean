import Paper2.YaoMaterializationTape
import EthInapproximability.CurrentPaper.MatrixStrideGather
import EthInapproximability.CurrentPaper.BitMachineSubroutine
import Paper2.YaoPhysicalSlice

/-! A fixed-controller strided payload gather with a charged final reversal.
The source, base offset, stride and address count enter as literal stacks. -/

namespace Paper2.YaoPayloadLoop

set_option maxRecDepth 2048

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineComposition
open EthInapproximability.CurrentPaper.BitMachineSubroutine
open Paper2.YaoLowerBound Paper2.YaoLowerBound.Materialization

abbrev Label := MatrixStrideGather.Label ⊕ Unit
abbrev Control := MatrixStrideGather.Control × Option Bool
abbrev Stack := (Fin 7 ⊕ Fin 3) ⊕ Fin 1
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt (some ()) (MatrixStrideGather.program l)
  | .inr () => pop (.inl (.inl 5)) (fun s b => (s.1, b))
      (branch (fun s => s.2.isSome)
        (push (.inr 0) (fun s => s.2.getD false) (goto (fun _ => .inr ())))
        (load (fun s => (s.1, none)) halt))

def cfg (label : Option Label) (flag : Bool) (last : Option Bool)
    (index source buffer counter stride work final : List Bool) : Config :=
  ⟨label, ((MatrixStrideGather.baseControl, flag), last),
    Sum.elim (Sum.elim (![index, [], [], source, [], buffer, []] : Fin 7 → List Bool)
      (![counter, stride, work] : Fin 3 → List Bool)) (fun _ => final)⟩

def run (n : ℕ) (c : Config) : Config := ((advance program)^[n]) c

private theorem run_succ {c d : Config} (h : TM2.step program c = some d) (n : ℕ) :
    run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : Config} {m : ℕ} (h : run m c = d) (n : ℕ) :
    run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem reverse_step_symbolic (s : Control) (bank : Stack → List Bool)
    (bit : Bool) (buffer : List Bool) (hb : bank (.inl (.inl 5)) = bit :: buffer) :
    TM2.step program ⟨some (.inr ()), s, bank⟩ =
      some ⟨some (.inr ()), (s.1, some bit),
        Function.update (Function.update bank (.inl (.inl 5)) buffer) (.inr 0)
          (bit :: bank (.inr 0))⟩ := by
  simp only [TM2.step, program, TM2.stepAux, hb, List.head?_cons, List.tail_cons,
    Option.isSome_some, Option.getD_some,
    Function.update_of_ne (show (Sum.inr (0 : Fin 1) : Stack) ≠ .inl (.inl 5) by decide)]
  rfl

private theorem reverse_stack (bit : Bool)
    (index source buffer counter stride work final : List Bool) :
    Function.update
      (Function.update
        (Sum.elim
          (Sum.elim (![index, [], [], source, [], bit :: buffer, []] : Fin 7 → List Bool)
            (![counter, stride, work] : Fin 3 → List Bool))
          (fun _ : Fin 1 => final)) (.inl (.inl 5)) buffer)
      (.inr 0) (bit :: final) =
    Sum.elim
      (Sum.elim (![index, [], [], source, [], buffer, []] : Fin 7 → List Bool)
        (![counter, stride, work] : Fin 3 → List Bool))
      (fun _ : Fin 1 => bit :: final) := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inl k =>
          fin_cases k <;> norm_num only [Function.update_apply, Sum.elim_inl,
            Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_succ, reduceCtorEq]
          all_goals split_ifs <;> simp_all
      | inr k =>
          fin_cases k <;> norm_num only [Function.update_apply, Sum.elim_inl,
            Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_succ, reduceCtorEq]
          all_goals split_ifs <;> simp_all
  | inr k =>
      fin_cases k <;> norm_num only [Function.update_apply, Sum.elim_inl,
        Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_succ, reduceCtorEq]
      all_goals split_ifs <;> simp_all

private theorem step_reverse_cons (flag : Bool) (last : Option Bool)
    (index source counter stride work final : List Bool) (bit : Bool) (buffer : List Bool) :
    TM2.step program (cfg (some (.inr ())) flag last index source (bit :: buffer)
      counter stride work final) =
      some (cfg (some (.inr ())) flag (some bit) index source buffer
        counter stride work (bit :: final)) := by
  exact (reverse_step_symbolic _ _ bit buffer rfl).trans
    (congrArg (fun S => some
      (⟨some (.inr ()), ((MatrixStrideGather.baseControl, flag), some bit), S⟩ : Config))
      (reverse_stack bit index source buffer counter stride work final))

private theorem step_reverse_nil (flag : Bool) (last : Option Bool)
    (index source counter stride work final : List Bool) :
    TM2.step program (cfg (some (.inr ())) flag last index source []
      counter stride work final) =
      some (cfg none flag none index source [] counter stride work final) := by
  apply congrArg (fun S => some
    (⟨none, ((MatrixStrideGather.baseControl, flag), none), S⟩ : Config))
  funext k
  cases k with
  | inl k =>
      cases k with
      | inl k => fin_cases k <;> rfl
      | inr k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

theorem reverse_run (buffer : List Bool) (flag : Bool) (last : Option Bool)
    (index source counter stride work final : List Bool) :
    run (buffer.length + 1)
      (cfg (some (.inr ())) flag last index source buffer counter stride work final) =
      cfg none flag none index source [] counter stride work (buffer.reverse ++ final) := by
  induction buffer generalizing last final with
  | nil =>
      simpa using run_succ
        (step_reverse_nil flag last index source counter stride work final) 0
  | cons bit buffer ih =>
      rw [List.length_cons, run_succ
        (step_reverse_cons flag last index source counter stride work final bit buffer)]
      simpa [List.reverse_cons, List.append_assoc] using ih (some bit) (bit :: final)

/-- One physical program invokes the existing fixed strided-read loop and
then reverses its accumulated buffer. Every read, unary stride increment,
counter pop, handoff and final reverse is charged. -/
theorem gather_forward (width start stride : ℕ) (source : List Bool) :
    ∃ steps ≤
      width * (3 * (start + width * stride) + 3 * source.length +
        2 * stride + 12) + 1 + (width + 1),
      run steps (cfg (some (.inl (.inr .test))) false none
        (List.replicate start true) source []
        (List.replicate width true) (List.replicate stride true) [] []) =
      cfg none false none (List.replicate (start + width * stride) true)
        source [] [] (List.replicate stride true) []
        (MatrixStrideGather.word stride start width source) := by
  obtain ⟨tg, htg, hg⟩ := MatrixStrideGather.gather_run width start stride false source []
  have hh : (((advance MatrixStrideGather.program)^[tg])
    (MatrixStrideGather.cfg (some (.inr .test)) false (List.replicate start true) source []
      (List.replicate width true) (List.replicate stride true) [])).l = none := by
    change (MatrixStrideGather.run tg _).l = none
    rw [hg]; rfl
  obtain ⟨t, ht, hr⟩ := lift_outputs MatrixStrideGather.program program (some ())
    (fun _ => rfl) none (fun _ : Fin 1 => [])
    (MatrixStrideGather.cfg (some (.inr .test)) false (List.replicate start true) source []
      (List.replicate width true) (List.replicate stride true) []) tg hh
  change run t _ = _ at hr
  change (((advance MatrixStrideGather.program)^[tg]) _) = _ at hg
  rw [hg] at hr
  have hrev := reverse_run (MatrixStrideGather.word stride start width source).reverse false none
    (List.replicate (start + width * stride) true) source []
    (List.replicate stride true) [] []
  simp only [List.append_nil] at hr
  refine ⟨t + (width + 1), ?_, ?_⟩
  · have hw := MatrixStrideGather.word_length stride start width source
    simp only [List.length_reverse, hw] at hrev
    omega
  · have hw := MatrixStrideGather.word_length stride start width source
    simp only [List.length_reverse, hw] at hrev
    simpa [cfg, List.reverse_reverse] using (run_add hr (width + 1)).trans hrev

/-- Exact first flat-tape index of the payload slice at label `l` and
edge position `p`, with subsequent addresses separated by `K+1`. -/
def payloadBase (t b lambda : ℕ)
    (l : Fin (payloadCount t b lambda))
    (p : Fin (2 ^ t * 2 ^ t + 1)) : ℕ :=
  selectorCount t b lambda * 2 ^ (t - 1) * b +
    l.val * 2 ^ b * (2 ^ t * 2 ^ t + 1) + p.val

def payloadStride (t : ℕ) : ℕ := 2 ^ t * 2 ^ t + 1

/-- Same literal payload-slice definition as the prior physical-entry
increment, stated locally to avoid importing a still-frozen scratch file. -/
def actualPayloadSlice (t b lambda : ℕ)
    (bits : SerializedTape t b lambda)
    (l : Fin (payloadCount t b lambda))
    (p : Fin (2 ^ t * 2 ^ t + 1)) : List Bool :=
  List.ofFn (fun h : Fin (2 ^ b) => readTape t b lambda bits (.inr (l, h, p)))

theorem actualPayloadSlice_eq_prior (t b lambda : ℕ)
    (bits : SerializedTape t b lambda)
    (l : Fin (payloadCount t b lambda))
    (p : Fin (2 ^ t * 2 ^ t + 1)) :
    actualPayloadSlice t b lambda bits l p =
      Paper2.YaoPhysicalSlice.payloadSlice t b lambda bits l p := rfl

theorem strided_word_eq_payload_slice (t b lambda : ℕ)
    (bits : SerializedTape t b lambda)
    (l : Fin (payloadCount t b lambda))
    (p : Fin (2 ^ t * 2 ^ t + 1)) :
    MatrixStrideGather.word (payloadStride t) (payloadBase t b lambda l p)
      (2 ^ b) bits.val = actualPayloadSlice t b lambda bits l p := by
  rw [MatrixStrideGather.word_eq_ofFn]
  apply congrArg List.ofFn
  funext h
  have he : payloadBase t b lambda l p + h.val * payloadStride t =
      selectorCount t b lambda * 2 ^ (t - 1) * b +
        (l.val * 2 ^ b + h.val) * (2 ^ t * 2 ^ t + 1) + p.val := by
    simp [payloadBase, payloadStride]
    ring
  have hk : payloadBase t b lambda l p + h.val * payloadStride t < bits.val.length := by
    rw [he, bits.property]
    exact payload_offset_lt t b lambda l h p
  rw [readTape_payload]
  rw [he] at hk ⊢
  rw [List.getElem?_eq_getElem hk]
  rfl

/-- The whole prior entry theorem's payload-slice bank, assembled from the
literal preserved flat tape by one fixed-control strided loop and charged
final reversal. Initial unary base/stride/count banks are supplied inputs. -/
theorem physical_actual_payload_slice (t b lambda : ℕ)
    (bits : SerializedTape t b lambda)
    (l : Fin (payloadCount t b lambda))
    (p : Fin (2 ^ t * 2 ^ t + 1)) :
    ∃ steps ≤ (2 ^ b) *
        (3 * (payloadBase t b lambda l p + (2 ^ b) * payloadStride t) +
          3 * bits.val.length + 2 * payloadStride t + 12) + 1 + ((2 ^ b) + 1),
      run steps (cfg (some (.inl (.inr .test))) false none
        (List.replicate (payloadBase t b lambda l p) true) bits.val []
        (List.replicate (2 ^ b) true) (List.replicate (payloadStride t) true) [] []) =
      cfg none false none
        (List.replicate (payloadBase t b lambda l p + (2 ^ b) * payloadStride t) true)
        bits.val [] [] (List.replicate (payloadStride t) true) []
        (actualPayloadSlice t b lambda bits l p) := by
  obtain ⟨steps, ht, hr⟩ := gather_forward (2 ^ b)
    (payloadBase t b lambda l p) (payloadStride t) bits.val
  refine ⟨steps, ht, ?_⟩
  simpa only [strided_word_eq_payload_slice] using hr

/-- The final bank is the *named* payload-slice input of the earlier
physical-entry theorem, not merely an isomorphic or same-length list. -/
theorem physical_prior_payload_slice (t b lambda : ℕ)
    (bits : SerializedTape t b lambda)
    (l : Fin (payloadCount t b lambda))
    (p : Fin (2 ^ t * 2 ^ t + 1)) :
    ∃ steps ≤ (2 ^ b) *
        (3 * (payloadBase t b lambda l p + (2 ^ b) * payloadStride t) +
          3 * bits.val.length + 2 * payloadStride t + 12) + 1 + ((2 ^ b) + 1),
      run steps (cfg (some (.inl (.inr .test))) false none
        (List.replicate (payloadBase t b lambda l p) true) bits.val []
        (List.replicate (2 ^ b) true) (List.replicate (payloadStride t) true) [] []) =
      cfg none false none
        (List.replicate (payloadBase t b lambda l p + (2 ^ b) * payloadStride t) true)
        bits.val [] [] (List.replicate (payloadStride t) true) []
        (Paper2.YaoPhysicalSlice.payloadSlice t b lambda bits l p) := by
  simpa only [actualPayloadSlice_eq_prior] using
    physical_actual_payload_slice t b lambda bits l p

#print axioms gather_forward
#print axioms strided_word_eq_payload_slice
#print axioms physical_actual_payload_slice
#print axioms physical_prior_payload_slice

end Paper2.YaoPayloadLoop
