import EthInapproximability.CurrentPaper.SourceNormalizationMachineOffsetWidth
import EthInapproximability.CurrentPaper.SourceNormalizationMachineMark

/-!
# Physical copy-offset shift of locally ranked endpoint fields

The input is a copy-major stream of unary fields. A unary field counter
marks each copy boundary; the controller scans the retained support vector
to add its true count to the offset before the next copy. All counters,
stream traversals, and final reversal are actual machine transitions.
-/

namespace EthInapproximability.CurrentPaper.SourceNormalizationMachineShiftCopies

open Turing TM2.Stmt BitMachineEncoding

inductive Phase where
  | peek | checkCount | widthScan | widthRestore | resetCount
  | copyOffset | restoreOffset | writeFirst | copyField | finish
  deriving DecidableEq, Fintype

abbrev Stack := Fin 9
abbrev Control := Bool × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Phase Control

def program : Phase → TM2.Stmt (fun _ : Stack => Bool) Phase Control
  | .peek => pop 0 (fun v b => (b.getD false,b))
      (branch (fun v => v.2.isSome)
        (goto (fun _ => .checkCount))
        (goto (fun _ => .finish)))
  | .checkCount => pop 5 (fun v b => (v.1,b))
      (branch (fun v => v.2.isSome)
        (push 6 (fun _ => true) (goto (fun _ => .copyOffset)))
        (goto (fun _ => .widthScan)))
  | .widthScan => pop 7 (fun v b => (v.1,b))
      (branch (fun v => v.2.isSome)
        (push 8 (fun v => v.2.getD false)
          (branch (fun v => v.2.getD false)
            (push 1 (fun _ => true) (goto (fun _ => .widthScan)))
            (goto (fun _ => .widthScan))))
        (goto (fun _ => .widthRestore)))
  | .widthRestore => pop 8 (fun v b => (v.1,b))
      (branch (fun v => v.2.isSome)
        (push 7 (fun v => v.2.getD false) (goto (fun _ => .widthRestore)))
        (goto (fun _ => .resetCount)))
  | .resetCount => pop 6 (fun v b => (v.1,b))
      (branch (fun v => v.2.isSome)
        (push 5 (fun _ => true) (goto (fun _ => .resetCount)))
        (push 0 (fun v => v.1) (goto (fun _ => .peek))))
  | .copyOffset => pop 1 (fun v b => (v.1,b))
      (branch (fun v => v.2.isSome)
        (push 2 (fun _ => true)
          (push 3 (fun _ => true) (goto (fun _ => .copyOffset))))
        (goto (fun _ => .restoreOffset)))
  | .restoreOffset => pop 2 (fun v b => (v.1,b))
      (branch (fun v => v.2.isSome)
        (push 1 (fun _ => true) (goto (fun _ => .restoreOffset)))
        (goto (fun _ => .writeFirst)))
  | .writeFirst => push 3 (fun v => v.1)
      (branch Prod.fst
        (goto (fun _ => .copyField))
        (goto (fun _ => .peek)))
  | .copyField => pop 0 (fun v b => (v.1,b))
      (branch (fun v => v.2.isSome)
        (push 3 (fun v => v.2.getD false)
          (branch (fun v => v.2.getD false)
            (goto (fun _ => .copyField))
            (goto (fun _ => .peek))))
        (goto (fun _ => .finish)))
  | .finish => pop 3 (fun v b => (v.1,b))
      (branch (fun v => v.2.isSome)
        (push 4 (fun v => v.2.getD false) (goto (fun _ => .finish)))
        halt)

def cfg (l : Option Phase) (s : Control)
    (stream offset offsetScratch revout output count used bits bitsScratch : List Bool) : Config :=
  ⟨l,s,![stream,offset,offsetScratch,revout,output,count,used,bits,bitsScratch]⟩

def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

private theorem run_succ {c d : Config} (h : TM2.step program c = some d) (t : ℕ) :
    run (t + 1) c = run t d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem replicate_true_rotate (q : ℕ) (tail : List Bool) :
    List.replicate q true ++ true :: tail =
      true :: List.replicate q true ++ tail := by
  induction q with
  | zero => rfl
  | succ q hq =>
      simpa only [List.replicate_succ, List.cons_append] using
        congrArg (List.cons true) hq

private theorem copy_offset_run (o a : ℕ) (s : Control)
    (stream revout output count used bits bitsScratch : List Bool) :
    run (o + 1) (cfg (some .copyOffset) s stream (List.replicate o true)
      (List.replicate a true)
      revout output count used bits bitsScratch) =
    cfg (some .restoreOffset) (s.1,none) stream []
      (List.replicate (a + o) true) ((List.replicate o true) ++ revout)
      output count used bits bitsScratch := by
  induction o generalizing a s revout with
  | zero =>
      apply congrArg (fun S => (⟨some Phase.restoreOffset,(s.1,none),S⟩ : Config))
      funext k
      fin_cases k <;> rfl
  | succ o ih =>
      have hs : TM2.step program
          (cfg (some .copyOffset) s stream (List.replicate (o + 1) true)
            (List.replicate a true) revout output count used bits bitsScratch) =
          some (cfg (some .copyOffset) (s.1,some true) stream
            (List.replicate o true) (List.replicate (a + 1) true)
            (true :: revout)
            output count used bits bitsScratch) := by
        apply congrArg (fun S => some (⟨some Phase.copyOffset,(s.1,some true),S⟩ : Config))
        funext k
        fin_cases k <;> rfl
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        List.replicate_succ, replicate_true_rotate] using
        (run_succ hs (o + 1)).trans
          (ih (a + 1) (s.1,some true) (true :: revout))

private theorem restore_offset_run (o a : ℕ) (s : Control)
    (stream revout output count used bits bitsScratch : List Bool) :
    run (o + 1) (cfg (some .restoreOffset) s stream
      (List.replicate a true) (List.replicate o true)
      revout output count used bits bitsScratch) =
    cfg (some .writeFirst) (s.1,none) stream
      (List.replicate (a + o) true) []
      revout output count used bits bitsScratch := by
  induction o generalizing a s with
  | zero =>
      apply congrArg (fun S => (⟨some Phase.writeFirst,(s.1,none),S⟩ : Config))
      funext k
      fin_cases k <;> rfl
  | succ o ih =>
      have hs : TM2.step program
          (cfg (some .restoreOffset) s stream (List.replicate a true)
            (List.replicate (o + 1) true) revout output count used bits bitsScratch) =
          some (cfg (some .restoreOffset) (s.1,some true) stream
            (List.replicate (a + 1) true) (List.replicate o true)
            revout output count used bits bitsScratch) := by
        apply congrArg (fun S => some (⟨some Phase.restoreOffset,(s.1,some true),S⟩ : Config))
        funext k
        fin_cases k <;> rfl
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (run_succ hs (o + 1)).trans (ih (a + 1) (s.1,some true))

private theorem copy_field_run (u : ℕ) (s : Control)
    (suffix offset revout output count used bits bitsScratch : List Bool) :
    run (u + 1) (cfg (some .copyField) s
      (EncodedGraph.unary u ++ suffix) offset [] revout output count used bits bitsScratch) =
    cfg (some .peek) (s.1,some false) suffix offset []
      (false :: List.replicate u true ++ revout)
      output count used bits bitsScratch := by
  induction u generalizing s revout with
  | zero =>
      apply congrArg (fun S => (⟨some Phase.peek,(s.1,some false),S⟩ : Config))
      funext k
      fin_cases k <;> rfl
  | succ u ih =>
      have hs : TM2.step program
          (cfg (some .copyField) s
            (EncodedGraph.unary (u + 1) ++ suffix)
            offset [] revout output count used bits bitsScratch) =
          some (cfg (some .copyField) (s.1,some true)
            (EncodedGraph.unary u ++ suffix) offset [] (true :: revout)
            output count used bits bitsScratch) := by
        apply congrArg (fun S => some (⟨some Phase.copyField,(s.1,some true),S⟩ : Config))
        funext k
        fin_cases k <;> rfl
      simpa only [List.replicate_succ, List.cons_append,
        replicate_true_rotate, Nat.add_assoc] using
        (run_succ hs (u + 1)).trans (ih (s.1,some true) (true :: revout))

private theorem offset_prefix_run (o : ℕ) (s : Control)
    (stream revout output count used bits bitsScratch : List Bool) :
    run (2 * o + 2) (cfg (some .copyOffset) s stream
      (List.replicate o true) [] revout output count used bits bitsScratch) =
    cfg (some .writeFirst) (s.1,none) stream
      (List.replicate o true) []
      (List.replicate o true ++ revout) output count used bits bitsScratch := by
  have hc := copy_offset_run o 0 s stream revout output count used bits bitsScratch
  have hr := restore_offset_run o 0 (s.1,none) stream
    (List.replicate o true ++ revout) output count used bits bitsScratch
  simp only [Nat.zero_add, List.replicate_zero] at hc hr
  have h := (run_add hc (o + 1)).trans hr
  simpa [two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

private theorem enter_zero (c a : ℕ) (s : Control)
    (suffix offset revout output bits bitsScratch : List Bool) :
    run 2 (cfg (some .peek) s (EncodedGraph.unary 0 ++ suffix)
      offset [] revout output (List.replicate (c + 1) true)
      (List.replicate a true) bits bitsScratch) =
    cfg (some .copyOffset) (false,some true) suffix offset [] revout output
      (List.replicate c true) (List.replicate (a + 1) true)
      bits bitsScratch := by
  apply congrArg (fun S => (⟨some Phase.copyOffset,(false,some true),S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem enter_succ (u c a : ℕ) (s : Control)
    (suffix offset revout output bits bitsScratch : List Bool) :
    run 2 (cfg (some .peek) s (EncodedGraph.unary (u + 1) ++ suffix)
      offset [] revout output (List.replicate (c + 1) true)
      (List.replicate a true) bits bitsScratch) =
    cfg (some .copyOffset) (true,some true)
      (EncodedGraph.unary u ++ suffix) offset [] revout output
      (List.replicate c true) (List.replicate (a + 1) true)
      bits bitsScratch := by
  apply congrArg (fun S => (⟨some Phase.copyOffset,(true,some true),S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem write_first_zero
    (stream offset revout output count used bits bitsScratch : List Bool) :
    run 1 (cfg (some .writeFirst) (false,none) stream offset []
      revout output count used bits bitsScratch) =
    cfg (some .peek) (false,none) stream offset []
      (false :: revout) output count used bits bitsScratch := by
  apply congrArg (fun S => (⟨some Phase.peek,(false,none),S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem write_first_succ
    (stream offset revout output count used bits bitsScratch : List Bool) :
    run 1 (cfg (some .writeFirst) (true,none) stream offset []
      revout output count used bits bitsScratch) =
    cfg (some .copyField) (true,none) stream offset []
      (true :: revout) output count used bits bitsScratch := by
  apply congrArg (fun S => (⟨some Phase.copyField,(true,none),S⟩ : Config))
  funext k
  fin_cases k <;> rfl

/-- One locally ranked unary endpoint consumes one copy-count token and
physically prepends the current unary offset to that field. -/
theorem one_field (u o c a : ℕ) (s : Control)
    (suffix revout output bits bitsScratch : List Bool) :
    ∃ s', run (2 * o + u + 5)
      (cfg (some .peek) s (EncodedGraph.unary u ++ suffix)
        (List.replicate o true) [] revout output
        (List.replicate (c + 1) true) (List.replicate a true)
        bits bitsScratch) =
      cfg (some .peek) s' suffix (List.replicate o true) []
        ((EncodedGraph.unary (u + o)).reverse ++ revout)
        output (List.replicate c true) (List.replicate (a + 1) true)
        bits bitsScratch := by
  cases u with
  | zero =>
      have he := enter_zero c a s suffix (List.replicate o true)
        revout output bits bitsScratch
      have hp := offset_prefix_run o (false,some true) suffix revout output
        (List.replicate c true) (List.replicate (a + 1) true) bits bitsScratch
      have hw := write_first_zero suffix (List.replicate o true)
        (List.replicate o true ++ revout) output
        (List.replicate c true) (List.replicate (a + 1) true) bits bitsScratch
      refine ⟨(false,none), ?_⟩
      have h := (run_add ((run_add he (2 * o + 2)).trans hp) 1).trans hw
      have ht : 2 + (2 * o + 2) + 1 = 2 * o + 5 := by omega
      rw [ht] at h
      simpa only [Nat.zero_add, EncodedGraph.unary,
        List.reverse_append, List.reverse_replicate,
        List.reverse_cons, List.reverse_nil, List.nil_append,
        List.singleton_append, List.append_assoc] using h
  | succ u =>
      have he := enter_succ u c a s suffix (List.replicate o true)
        revout output bits bitsScratch
      have hp := offset_prefix_run o (true,some true)
        (EncodedGraph.unary u ++ suffix) revout output
        (List.replicate c true) (List.replicate (a + 1) true) bits bitsScratch
      have hw := write_first_succ (EncodedGraph.unary u ++ suffix)
        (List.replicate o true) (List.replicate o true ++ revout)
        output (List.replicate c true) (List.replicate (a + 1) true)
        bits bitsScratch
      have hf := copy_field_run u (true,none) suffix
        (List.replicate o true) (true :: List.replicate o true ++ revout)
        output (List.replicate c true) (List.replicate (a + 1) true)
        bits bitsScratch
      refine ⟨(true,some false), ?_⟩
      have h := (run_add
        ((run_add ((run_add he (2 * o + 2)).trans hp) 1).trans hw)
          (u + 1)).trans hf
      have ht : 2 + (2 * o + 2) + 1 + (u + 1) =
          2 * o + (u + 1) + 5 := by omega
      rw [ht] at h
      have hrep : false :: List.replicate u true ++
          (true :: List.replicate o true ++ revout) =
          (EncodedGraph.unary (u + 1 + o)).reverse ++ revout := by
        simp [EncodedGraph.unary, List.replicate_add,
          List.append_assoc, Nat.add_assoc]
        have hleft : List.replicate u true ++ true ::
            (List.replicate o true ++ revout) =
            List.replicate (u + 1 + o) true ++ revout := by
          simp [List.replicate_add, List.append_assoc]
        have hright : List.replicate o true ++ true ::
            (List.replicate u true ++ revout) =
            List.replicate (o + 1 + u) true ++ revout := by
          simp [List.replicate_add, List.append_assoc]
        rw [hleft, hright]
        rw [show u + 1 + o = o + 1 + u by omega]
      simpa only [hrep] using h

def shifted (xs : List ℕ) (offset : ℕ) : List Bool :=
  SourceNormalizationMachineMark.endpointStream (xs.map (· + offset))

def copiedShifted (xs : List ℕ) (width copies : ℕ) : List Bool :=
  (List.range copies).flatMap fun k => shifted xs (k * width)

def blockCost (xs : List ℕ) (offset : ℕ) : ℕ :=
  xs.sum + (2 * offset + 5) * xs.length

/-- A literal pass over one copy's endpoint fields, leaving the next copy's
stream untouched and collecting the consumed field-count tokens. -/
theorem block_into (xs : List ℕ) (o a : ℕ) (s : Control)
    (suffix revout output bits bitsScratch : List Bool) :
    ∃ t ≤ blockCost xs o, ∃ s',
      run t (cfg (some .peek) s
        (SourceNormalizationMachineMark.endpointStream xs ++ suffix)
        (List.replicate o true) [] revout output
        (List.replicate xs.length true) (List.replicate a true)
        bits bitsScratch) =
      cfg (some .peek) s' suffix (List.replicate o true) []
        ((shifted xs o).reverse ++ revout)
        output [] (List.replicate (a + xs.length) true)
        bits bitsScratch := by
  induction xs generalizing a s revout with
  | nil =>
      exact ⟨0, by simp [blockCost], s, by simp [run, cfg, shifted,
        SourceNormalizationMachineMark.endpointStream]⟩
  | cons u us ih =>
      obtain ⟨s1,h1⟩ := one_field u o us.length a s
        (SourceNormalizationMachineMark.endpointStream us ++ suffix)
        revout output bits bitsScratch
      obtain ⟨t,ht,s2,h2⟩ := ih (a + 1) s1
        ((EncodedGraph.unary (u + o)).reverse ++ revout)
      refine ⟨2 * o + u + 5 + t, ?_, s2, ?_⟩
      · simp only [blockCost, List.sum_cons, List.length_cons,
          Nat.mul_succ] at ht ⊢
        omega
      · have h := (run_add h1 t).trans h2
        simpa only [SourceNormalizationMachineMark.endpointStream,
          List.append_assoc, shifted, List.map_cons, List.reverse_append,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
          List.length_cons, List.replicate_succ] using h

private theorem width_scan_run (bits scratch : List Bool) (o : ℕ)
    (s : Control) (stream revout output count used : List Bool) :
    run (bits.length + 1)
      (cfg (some .widthScan) s stream (List.replicate o true) []
        revout output count used bits scratch) =
      cfg (some .widthRestore) (s.1,none) stream
        (List.replicate (o + bits.count true) true) []
        revout output count used [] (bits.reverse ++ scratch) := by
  induction bits generalizing scratch o s with
  | nil =>
      apply congrArg (fun S => (⟨some Phase.widthRestore,(s.1,none),S⟩ : Config))
      funext k
      fin_cases k <;> rfl
  | cons b bs ih =>
      have hs : TM2.step program
          (cfg (some .widthScan) s stream (List.replicate o true) []
            revout output count used (b :: bs) scratch) =
          some (cfg (some .widthScan) (s.1,some b) stream
            (List.replicate (o + if b then 1 else 0) true) []
            revout output count used bs (b :: scratch)) := by
        cases b <;>
          apply congrArg (fun S => some
            (⟨some Phase.widthScan,(s.1,some _),S⟩ : Config))
        all_goals
          funext k
          fin_cases k <;> simp [List.replicate_succ]
      have h := (run_succ hs (bs.length + 1)).trans
        (ih (b :: scratch) (o + if b then 1 else 0) (s.1,some b))
      cases b <;> simpa [Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm, List.append_assoc] using h

private theorem width_restore_run (scratch vector : List Bool) (s : Control)
    (stream offset revout output count used : List Bool) :
    run (scratch.length + 1)
      (cfg (some .widthRestore) s stream offset []
        revout output count used vector scratch) =
      cfg (some .resetCount) (s.1,none) stream offset []
        revout output count used (scratch.reverse ++ vector) [] := by
  induction scratch generalizing vector s with
  | nil =>
      apply congrArg (fun S => (⟨some Phase.resetCount,(s.1,none),S⟩ : Config))
      funext k
      fin_cases k <;> rfl
  | cons b bs ih =>
      have hs : TM2.step program
          (cfg (some .widthRestore) s stream offset []
            revout output count used vector (b :: bs)) =
          some (cfg (some .widthRestore) (s.1,some b) stream offset []
            revout output count used (b :: vector) bs) := by
        apply congrArg (fun S => some
          (⟨some Phase.widthRestore,(s.1,some b),S⟩ : Config))
        funext k
        fin_cases k <;> rfl
      simpa only [List.length_cons, List.reverse_cons,
        List.singleton_append, List.append_assoc] using
        (run_succ hs (bs.length + 1)).trans
          (ih (b :: vector) (s.1,some b))

private theorem reset_count_run (r : ℕ) (s : Control)
    (stream offset revout output count bits bitsScratch : List Bool) :
    run (r + 1)
      (cfg (some .resetCount) s stream offset []
        revout output count (List.replicate r true) bits bitsScratch) =
      cfg (some .peek) (s.1,none) (s.1 :: stream) offset []
        revout output (List.replicate r true ++ count) [] bits bitsScratch := by
  induction r generalizing count s with
  | zero =>
      apply congrArg (fun S => (⟨some Phase.peek,(s.1,none),S⟩ : Config))
      funext k
      fin_cases k <;> rfl
  | succ r ih =>
      have hs : TM2.step program
          (cfg (some .resetCount) s stream offset []
            revout output count (List.replicate (r + 1) true) bits bitsScratch) =
          some (cfg (some .resetCount) (s.1,some true) stream offset []
            revout output (true :: count) (List.replicate r true) bits bitsScratch) := by
        apply congrArg (fun S => some
          (⟨some Phase.resetCount,(s.1,some true),S⟩ : Config))
        funext k
        fin_cases k <;> rfl
      simpa only [List.replicate_succ, List.cons_append,
        List.append_assoc, replicate_true_rotate] using
        (run_succ hs (r + 1)).trans
          (ih (s.1,some true) (true :: count))

private theorem width_add_run (bits : List Bool) (o : ℕ) (s : Control)
    (stream revout output count used : List Bool) :
    run (2 * bits.length + 2)
      (cfg (some .widthScan) s stream (List.replicate o true) []
        revout output count used bits []) =
      cfg (some .resetCount) (s.1,none) stream
        (List.replicate (o + bits.count true) true) []
        revout output count used bits [] := by
  have hs := width_scan_run bits [] o s stream revout output count used
  have hr := width_restore_run bits.reverse [] (s.1,none) stream
    (List.replicate (o + bits.count true) true) revout output count used
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at hs hr
  have h := (run_add hs (bits.length + 1)).trans hr
  simpa [two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- The inter-copy transition restores the field counter and adds exactly
the number of supported padded vertices to the retained offset. -/
theorem boundary_run (bits : List Bool) (fields o : ℕ) (b : Bool)
    (s : Control) (stream revout output : List Bool) :
    run (2 * bits.length + fields + 5)
      (cfg (some .peek) s (b :: stream)
        (List.replicate o true) [] revout output []
        (List.replicate fields true) bits []) =
      cfg (some .peek) (b,none) (b :: stream)
        (List.replicate (o + bits.count true) true) [] revout output
        (List.replicate fields true) [] bits [] := by
  have he : run 2
      (cfg (some .peek) s (b :: stream) (List.replicate o true) []
        revout output [] (List.replicate fields true) bits []) =
      cfg (some .widthScan) (b,none) stream (List.replicate o true) []
        revout output [] (List.replicate fields true) bits [] := by
    apply congrArg (fun S => (⟨some Phase.widthScan,(b,none),S⟩ : Config))
    funext k
    fin_cases k <;> rfl
  have hw := width_add_run bits o (b,none) stream revout output []
    (List.replicate fields true)
  have hr := reset_count_run fields (b,none) stream
    (List.replicate (o + bits.count true) true) revout output [] bits []
  have h := (run_add ((run_add he (2 * bits.length + 2)).trans hw)
    (fields + 1)).trans hr
  have ht : 2 + (2 * bits.length + 2) + (fields + 1) =
      2 * bits.length + fields + 5 := by omega
  rw [ht] at h
  simpa only [List.append_nil] using h

def copyInput (xs : List ℕ) : ℕ → List Bool
  | 0 => []
  | r + 1 => SourceNormalizationMachineMark.endpointStream xs ++ copyInput xs r

def shiftedFrom (xs : List ℕ) (width offset : ℕ) : ℕ → List Bool
  | 0 => []
  | r + 1 => shifted xs offset ++ shiftedFrom xs width (offset + width) r

def copiesCost (xs : List ℕ) (bits : List Bool) (offset : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => blockCost xs offset
  | r + 2 => blockCost xs offset +
      (2 * bits.length + xs.length + 5) +
      copiesCost xs bits (offset + bits.count true) (r + 1)

private theorem copyInput_nonempty (xs : List ℕ) (hx : xs ≠ []) (r : ℕ) :
    copyInput xs (r + 1) ≠ [] := by
  cases xs with
  | nil => exact False.elim (hx rfl)
  | cons u us =>
      simp [copyInput, SourceNormalizationMachineMark.endpointStream,
        EncodedGraph.unary]

/-- All copy-major unary fields are physically shifted, with one width scan
between consecutive copies and no uncharged final offset update. -/
theorem copies_into (xs : List ℕ) (hx : xs ≠ [])
    (bits : List Bool) (r o : ℕ) (hr : 0 < r) (s : Control)
    (revout output : List Bool) :
    ∃ t ≤ copiesCost xs bits o r, ∃ s',
      run t (cfg (some .peek) s (copyInput xs r)
        (List.replicate o true) [] revout output
        (List.replicate xs.length true) [] bits []) =
      cfg (some .peek) s' []
        (List.replicate (o + (r - 1) * bits.count true) true) []
        ((shiftedFrom xs (bits.count true) o r).reverse ++ revout)
        output [] (List.replicate xs.length true) bits [] := by
  induction r generalizing o s revout with
  | zero => omega
  | succ r ih =>
      obtain ⟨t,ht,s1,hblock⟩ := block_into xs o 0 s
        (copyInput xs r) revout output bits []
      simp only [Nat.zero_add, List.replicate_zero] at hblock
      cases r with
      | zero =>
          refine ⟨t, ?_, s1, ?_⟩
          · simpa [copiesCost] using ht
          · simpa [copyInput, shiftedFrom, shifted,
              Nat.add_zero] using hblock
      | succ r =>
          have hne := copyInput_nonempty xs hx r
          obtain ⟨b,tail,hstream⟩ : ∃ b tail,
              copyInput xs (r + 1) = b :: tail := by
            cases h : copyInput xs (r + 1) with
            | nil => exact False.elim (hne h)
            | cons b tail => exact ⟨b,tail,rfl⟩
          have hboundary := boundary_run bits xs.length o b s1 tail
            ((shifted xs o).reverse ++ revout) output
          rw [← hstream] at hboundary
          obtain ⟨v,hv,s2,hrest⟩ := ih
            (o + bits.count true) (by omega) (b,none)
            ((shifted xs o).reverse ++ revout)
          have h := (run_add ((run_add hblock
            (2 * bits.length + xs.length + 5)).trans hboundary) v).trans hrest
          refine ⟨t + (2 * bits.length + xs.length + 5) + v, ?_, s2, ?_⟩
          · simpa only [copiesCost] using
              (show t + (2 * bits.length + xs.length + 5) + v ≤
                blockCost xs o + (2 * bits.length + xs.length + 5) +
                  copiesCost xs bits (o + bits.count true) (r + 1) by omega)
          · have hoff : o + (r + 2 - 1) * bits.count true =
                (o + bits.count true) + (r + 1 - 1) * bits.count true := by
              have h1 : r + 2 - 1 = r + 1 := by omega
              have h2 : r + 1 - 1 = r := by omega
              rw [h1, h2, Nat.succ_mul]
              omega
            simpa only [copyInput, shiftedFrom, List.reverse_append,
              List.append_assoc, hoff]
              using h

private theorem finish_run (revout : List Bool) (s : Control)
    (offset output used bits : List Bool) :
    run (revout.length + 1)
      (cfg (some .finish) s [] offset [] revout output [] used bits []) =
      cfg none (s.1,none) [] offset [] []
        (revout.reverse ++ output) [] used bits [] := by
  induction revout generalizing s output with
  | nil =>
      apply congrArg (fun S => (⟨none,(s.1,none),S⟩ : Config))
      funext k
      fin_cases k <;> rfl
  | cons b bs ih =>
      have hs : TM2.step program
          (cfg (some .finish) s [] offset [] (b :: bs)
            output [] used bits []) =
          some (cfg (some .finish) (s.1,some b) [] offset [] bs
            (b :: output) [] used bits []) := by
        apply congrArg (fun S => some
          (⟨some Phase.finish,(s.1,some b),S⟩ : Config))
        funext k
        fin_cases k <;> rfl
      simpa only [List.length_cons, List.reverse_cons,
        List.singleton_append, List.append_assoc] using
        (run_succ hs (bs.length + 1)).trans
          (ih (s.1,some b) (b :: output))

/-- Complete physical copy-major shift, including the charged final
reversal. The source support vector and field-count tokens remain available. -/
theorem copies_run (xs : List ℕ) (hx : xs ≠ [])
    (bits : List Bool) (r o : ℕ) (hr : 0 < r)
    (output : List Bool) :
    ∃ t ≤ copiesCost xs bits o r +
        (shiftedFrom xs (bits.count true) o r).length + 2,
      run t (cfg (some .peek) (false,none) (copyInput xs r)
        (List.replicate o true) [] [] output
        (List.replicate xs.length true) [] bits []) =
      cfg none (false,none) []
        (List.replicate (o + (r - 1) * bits.count true) true) [] []
        (shiftedFrom xs (bits.count true) o r ++ output)
        [] (List.replicate xs.length true) bits [] := by
  obtain ⟨t,ht,s,he⟩ := copies_into xs hx bits r o hr
    (false,none) [] output
  simp only [List.append_nil] at he
  have hp : run 1
      (cfg (some .peek) s []
        (List.replicate (o + (r - 1) * bits.count true) true) []
        (shiftedFrom xs (bits.count true) o r).reverse
        output [] (List.replicate xs.length true) bits []) =
      cfg (some .finish) (false,none) []
        (List.replicate (o + (r - 1) * bits.count true) true) []
        (shiftedFrom xs (bits.count true) o r).reverse
        output [] (List.replicate xs.length true) bits [] := by
    apply congrArg (fun S =>
      (⟨some Phase.finish,(false,none),S⟩ : Config))
    funext k
    fin_cases k <;> rfl
  have hf := finish_run (shiftedFrom xs (bits.count true) o r).reverse
    (false,none)
    (List.replicate (o + (r - 1) * bits.count true) true)
    output (List.replicate xs.length true) bits
  simp only [List.length_reverse, List.reverse_reverse] at hf
  refine ⟨t + 1 + ((shiftedFrom xs (bits.count true) o r).length + 1),
    by omega, ?_⟩
  exact (run_add ((run_add he 1).trans hp) _).trans hf

theorem copyInput_eq_copy_major (xs : List ℕ) (r : ℕ) :
    copyInput xs r =
      (List.range r).flatMap
        (fun _ => SourceNormalizationMachineMark.endpointStream xs) := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [copyInput, List.range_succ_eq_map]
      simp only [List.flatMap_cons, List.flatMap_map]
      simpa only [ih]

theorem shiftedFrom_eq_copy_major (xs : List ℕ)
    (width offset r : ℕ) :
    shiftedFrom xs width offset r =
      (List.range r).flatMap (fun k => shifted xs (offset + k * width)) := by
  induction r generalizing offset with
  | zero => rfl
  | succ r ih =>
      rw [shiftedFrom, List.range_succ_eq_map]
      simp only [List.flatMap_cons, List.flatMap_map]
      rw [ih]
      congr 1
      · simp
      · apply List.flatMap_congr
        intro k hk
        congr 1
        rw [Nat.succ_mul]
        omega

theorem copiedShifted_eq_shiftedFrom (xs : List ℕ) (width r : ℕ) :
    copiedShifted xs width r = shiftedFrom xs width 0 r := by
  rw [shiftedFrom_eq_copy_major]
  simp only [copiedShifted, Nat.zero_add]

end EthInapproximability.CurrentPaper.SourceNormalizationMachineShiftCopies
