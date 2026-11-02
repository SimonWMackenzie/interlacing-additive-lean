import EthInapproximability.CurrentPaper.SourceListMachineFieldsCore
import EthInapproximability.CurrentPaper.ProtocolBinaryHeader
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding
import EthInapproximability.CurrentPaper.SourceListEncoding

/-! # Canonical length-prefixed raw payloads on Boolean stacks

Source: frozen v8 `B-effectivity-details.tex`, explicit source lists. Successful
execution time depends only on the current field, independently of the suffix.
Malformed headers and truncated payloads are rejected by actual stack steps.
-/

namespace EthInapproximability.CurrentPaper.SourceListMachineFields

open Turing TM2.Stmt BitMachineEncoding EncodedCommunication

/-- A successful canonical header scans only the header, not its suffix. -/
theorem header_success {input bs rest : List Bool} {seen popped : Option Bool}
    (saved target : List Bool) (h : ProtocolBinaryHeader.readChecked seen input = some (bs, rest)) :
    ∃ v : ProtocolBinaryHeader.Control,
      ProtocolBinaryHeader.run (3 * bs.length + saved.length + 2)
        (ProtocolBinaryHeader.cfg (some .scan) (seen, popped) input saved target) =
      ProtocolBinaryHeader.cfg none v rest [] (true :: (saved.reverse ++ bs ++ target)) := by
  induction input using readField.induct generalizing seen popped saved bs rest with
  | case1 => simp [ProtocolBinaryHeader.readChecked] at h
  | case2 tail =>
      by_cases hs : seen = some false
      · simp [ProtocolBinaryHeader.readChecked, hs] at h
      · simp only [ProtocolBinaryHeader.readChecked, hs, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨(seen, none), ?_⟩
        rw [show 3 * ([] : List Bool).length + saved.length + 2 =
          (saved.length + 1) + 1 by simp,
          ProtocolBinaryHeader.run_succ_first, ProtocolBinaryHeader.scan_false, if_neg hs, ProtocolBinaryHeader.restore_correct]
        simp
  | case3 => simp [ProtocolBinaryHeader.readChecked] at h
  | case4 b tail ih =>
      obtain ⟨⟨xs, suffix⟩, hx, he⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨v, hv⟩ := ih (b :: saved) hx (popped := some b)
      refine ⟨v, ?_⟩
      rw [show 3 * (b :: xs).length + saved.length + 2 =
        ((3 * xs.length + (b :: saved).length + 2) + 1) + 1 by simp; omega,
        ProtocolBinaryHeader.run_succ_first, ProtocolBinaryHeader.scan_true, ProtocolBinaryHeader.run_succ_first, ProtocolBinaryHeader.payload_cons, hv]
      simp [List.reverse_cons, List.append_assoc]

theorem header_natField (n : Nat) (suffix : List Bool) :
    ∃ v : ProtocolBinaryHeader.Control,
      ProtocolBinaryHeader.run (3 * n.bits.length + 2)
        (ProtocolBinaryHeader.cfg (some .scan) (none, none) (natField n ++ suffix) [] []) =
      ProtocolBinaryHeader.cfg none v suffix [] (true :: n.bits) := by
  have hr : ProtocolBinaryHeader.readChecked none (natField n ++ suffix) = some (n.bits, suffix) := by
    rw [ProtocolBinaryHeader.readChecked_spec]
    simp [natField, readField_append, ProtocolBinaryHeader.canonicalFrom_none, ProtocolBinaryHeader.canonical_of_bits]
  simpa using header_success [] [] hr (popped := none)

inductive OuterLabel where
  | afterHeader | afterPayload | clearCounter | restorePayload
  deriving DecidableEq, Fintype

abbrev Stack := Fin 7
abbrev Label := ProtocolBinaryHeader.Label ⊕ (SourceListMachineFieldsCore.Label ⊕ OuterLabel)
abbrev Control := ProtocolBinaryHeader.Control × SourceListMachineFieldsCore.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control
abbrev Statement := TM2.Stmt (fun _ : Stack => Bool) Label Control

def outer (l : OuterLabel) : Label := .inr (.inr l)
def headerControl (v : ProtocolBinaryHeader.Control) : Control := (v, (none, false))
def coreControl (v : SourceListMachineFieldsCore.Control) : Control := ((none, none), v)
def initialControl : Control := headerControl (none, none)
def setPop (v : Control) (b : Option Bool) : Control := (v.1, b, v.2.2)
def go (l : OuterLabel) : Statement := goto (fun _ => outer l)
def failed : Statement := load (fun _ => coreControl (some false, false)) halt

def headerStack : Fin 3 ↪ Stack where
  toFun k := ⟨k.val, by omega⟩
  inj' := by
    intro a b h
    apply Fin.ext
    exact congrArg (fun k : Stack => k.val) h

def coreStack : SourceListMachineFieldsCore.Stack ↪ Stack where
  toFun k := ![2, 0, 3, 4, 5] k
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all

def program : Label → Statement
  | .inl l => BitMachineStackEmbedding.stmt headerStack Sum.inl headerControl Prod.fst
      (some (outer .afterHeader)) (ProtocolBinaryHeader.program l)
  | .inr (.inl l) => BitMachineStackEmbedding.stmt coreStack (fun l => .inr (.inl l))
      coreControl Prod.snd (some (outer .afterPayload)) (SourceListMachineFieldsCore.program l)
  | .inr (.inr .afterHeader) => pop 2 setPop
      (branch (fun v => v.2.1.getD false)
        (load (fun _ => coreControl (none, false)) (goto (fun _ => .inr (.inl .zeroScan)))) failed)
  | .inr (.inr .afterPayload) => branch (fun v => v.2.1.getD false) (go .clearCounter) failed
  | .inr (.inr .clearCounter) => pop 2 setPop
      (branch (fun v => v.2.1.isSome) (go .clearCounter) (go .restorePayload))
  | .inr (.inr .restorePayload) => pop 4 setPop
      (branch (fun v => v.2.1.isSome)
        (push 6 (fun v => v.2.1.getD false) (go .restorePayload))
        (load (fun _ => coreControl (some true, false)) halt))

structure Data where
  input : List Bool := []
  saved : List Bool := []
  counter : List Bool := []
  work : List Bool := []
  reversed : List Bool := []
  count : List Bool := []
  payload : List Bool := []

def Data.stacks (d : Data) : Stack → List Bool :=
  ![d.input, d.saved, d.counter, d.work, d.reversed, d.count, d.payload]
def cfg (l : Option Label) (v : Control) (d : Data) : Config := ⟨l, v, d.stacks⟩
def run (n : Nat) (c : Config) : Config := ((advance program)^[n]) c

theorem run_succ {c c' : Config} (h : advance program c = c') (n : Nat) :
    run (n + 1) c = run n c' := by
  exact (Function.iterate_succ_apply _ _ _).trans (congrArg (run n) h)
theorem run_add {c c' : Config} {n : Nat} (h : run n c = c') (m : Nat) :
    run (n + m) c = run m c' := by
  rw [Nat.add_comm, run, Function.iterate_add_apply]
  exact congrArg (run m) h

abbrev HeaderConfig := TM2.Cfg (fun _ : Fin 3 => Bool) ProtocolBinaryHeader.Label ProtocolBinaryHeader.Control

def headerData (d : Data) (c : HeaderConfig) : Data :=
  {d with input := c.stk 0, saved := c.stk 1, counter := c.stk 2}
def coreData (d : Data) (c : SourceListMachineFieldsCore.Config) : Data :=
  {d with counter := c.stk 0, input := c.stk 1, work := c.stk 2,
          reversed := c.stk 3, count := c.stk 4}

theorem headerBank (d : Data) (c : HeaderConfig) :
    BitMachineStackEmbedding.bank headerStack d.stacks c.stk = (headerData d c).stacks := by
  funext j
  fin_cases j
  · exact BitMachineStackEmbedding.bank_at headerStack d.stacks c.stk 0
  · exact BitMachineStackEmbedding.bank_at headerStack d.stacks c.stk 1
  · exact BitMachineStackEmbedding.bank_at headerStack d.stacks c.stk 2
  all_goals
    apply BitMachineStackEmbedding.bank_outside
    rintro ⟨k, h⟩
    fin_cases k <;> cases h

theorem coreBank (d : Data) (c : SourceListMachineFieldsCore.Config) :
    BitMachineStackEmbedding.bank coreStack d.stacks c.stk = (coreData d c).stacks := by
  funext j
  fin_cases j
  · exact BitMachineStackEmbedding.bank_at coreStack d.stacks c.stk 1
  · apply BitMachineStackEmbedding.bank_outside; rintro ⟨k, h⟩; fin_cases k <;> cases h
  · exact BitMachineStackEmbedding.bank_at coreStack d.stacks c.stk 0
  · exact BitMachineStackEmbedding.bank_at coreStack d.stacks c.stk 2
  · exact BitMachineStackEmbedding.bank_at coreStack d.stacks c.stk 3
  · exact BitMachineStackEmbedding.bank_at coreStack d.stacks c.stk 4
  · apply BitMachineStackEmbedding.bank_outside; rintro ⟨k, h⟩; fin_cases k <;> cases h

noncomputable def headerFrame (d : Data) (c : HeaderConfig) : Config :=
  BitMachineStackEmbedding.cfg headerStack d.stacks Sum.inl headerControl (some (outer .afterHeader)) c
noncomputable def coreFrame (d : Data) (c : SourceListMachineFieldsCore.Config) : Config :=
  BitMachineStackEmbedding.cfg coreStack d.stacks (fun l => .inr (.inl l)) coreControl
    (some (outer .afterPayload)) c

theorem headerFrame_initial (d : Data) :
    headerFrame d (ProtocolBinaryHeader.cfg (some .scan) (none, none) d.input [] []) =
      cfg (some (.inl .scan)) initialControl {d with saved := [], counter := []} := by
  unfold headerFrame BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg
  rw [headerBank]
  rfl

theorem headerFrame_halted (d : Data) (c : HeaderConfig) (hc : c.l = none) :
    headerFrame d c = cfg (some (outer .afterHeader)) (headerControl c.var) (headerData d c) := by
  unfold headerFrame BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg
  rw [hc, headerBank]
  rfl

theorem coreFrame_initial (d : Data) :
    coreFrame d (SourceListMachineFieldsCore.cfg (some .zeroScan) (none, false) d.counter d.input [] d.reversed d.count) =
      cfg (some (.inr (.inl .zeroScan))) (coreControl (none, false)) {d with work := []} := by
  unfold coreFrame BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg
  rw [coreBank]
  rfl

theorem coreFrame_halted (d : Data) (c : SourceListMachineFieldsCore.Config) (hc : c.l = none) :
    coreFrame d c = cfg (some (outer .afterPayload)) (coreControl c.var) (coreData d c) := by
  unfold coreFrame BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg
  rw [hc, coreBank]
  rfl

theorem header_run (d : Data) :
    ∃ t ≤ 2 * d.input.length + 2, ∃ c : HeaderConfig,
      run t (cfg (some (.inl .scan)) initialControl {d with saved := [], counter := []}) =
        cfg (some (outer .afterHeader)) (headerControl c.var) (headerData d c) ∧
      ProtocolBinaryHeader.Post none d.input [] [] c := by
  obtain ⟨t, ht, hp⟩ := ProtocolBinaryHeader.scan_correct d.input none none [] []
  obtain ⟨n, hn, he⟩ := BitMachineStackEmbedding.outputs headerStack d.stacks Sum.inl
    headerControl Prod.fst (fun _ => rfl) (some (outer .afterHeader))
    ProtocolBinaryHeader.program program (fun _ => rfl)
    (ProtocolBinaryHeader.cfg (some .scan) (none, none) d.input [] []) t hp.1
  change run n (headerFrame d _) = headerFrame d (ProtocolBinaryHeader.run t _) at he
  rw [headerFrame_initial, headerFrame_halted d _ hp.1] at he
  exact ⟨n, hn.trans (by simpa using ht), _, he, hp⟩

theorem header_run_success (d : Data) (bs rest : List Bool)
    (hr : ProtocolBinaryHeader.readChecked none d.input = some (bs, rest)) :
    ∃ t ≤ 3 * bs.length + 2, ∃ v : ProtocolBinaryHeader.Control,
      run t (cfg (some (.inl .scan)) initialControl {d with saved := [], counter := []}) =
        cfg (some (outer .afterHeader)) (headerControl v)
          {d with input := rest, saved := [], counter := true :: bs} := by
  obtain ⟨v, hv⟩ := header_success [] [] hr (popped := none)
  simp only [List.length_nil, Nat.add_zero, List.reverse_nil, List.nil_append, List.append_nil] at hv
  obtain ⟨n, hn, he⟩ := BitMachineStackEmbedding.outputs headerStack d.stacks Sum.inl
    headerControl Prod.fst (fun _ => rfl) (some (outer .afterHeader))
    ProtocolBinaryHeader.program program (fun _ => rfl)
    (ProtocolBinaryHeader.cfg (some .scan) (none, none) d.input [] []) (3 * bs.length + 2)
    (by change (ProtocolBinaryHeader.run _ _).l = none; rw [hv]; rfl)
  change run n (headerFrame d _) = headerFrame d (ProtocolBinaryHeader.run _ _) at he
  rw [headerFrame_initial, hv, headerFrame_halted d _ rfl] at he
  exact ⟨n, hn, v, he⟩

theorem payload_run (d : Data) :
    ∃ t ≤ (min (bitsValue d.counter) d.input.length + 1) * (4 * d.counter.length + 5), ∃ q',
      q'.length = d.counter.length ∧
      run t (cfg (some (.inr (.inl .zeroScan))) (coreControl (none, false)) {d with work := []}) =
        cfg (some (outer .afterPayload))
          (coreControl (some (decide (bitsValue d.counter ≤ d.input.length)), false))
          {d with counter := q', input := d.input.drop (bitsValue d.counter), work := [],
                  reversed := (d.input.take (bitsValue d.counter)).reverse ++ d.reversed,
                  count := List.replicate (min (bitsValue d.counter) d.input.length) true ++ d.count} := by
  obtain ⟨t, ht, q', hq, hr⟩ := SourceListMachineFieldsCore.payload_run d.counter d.input d.reversed d.count
  obtain ⟨n, hn, he⟩ := BitMachineStackEmbedding.outputs coreStack d.stacks
    (fun l => .inr (.inl l)) coreControl Prod.snd (fun _ => rfl) (some (outer .afterPayload))
    SourceListMachineFieldsCore.program program (fun _ => rfl)
    (SourceListMachineFieldsCore.cfg (some .zeroScan) (none, false) d.counter d.input [] d.reversed d.count) t
    (by change (SourceListMachineFieldsCore.run _ _).l = none; rw [hr]; rfl)
  change run n (coreFrame d _) = coreFrame d (SourceListMachineFieldsCore.run _ _) at he
  rw [coreFrame_initial, hr, coreFrame_halted d _ rfl] at he
  exact ⟨n, hn.trans ht, q', hq, he⟩

theorem afterHeader_good (v : Control) (bs : List Bool) (d : Data) :
    advance program (cfg (some (outer .afterHeader)) v {d with counter := true :: bs}) =
      cfg (some (.inr (.inl .zeroScan))) (coreControl (none, false)) {d with counter := bs} := by
  simp [advance, TM2.step, program, outer, TM2.stepAux, cfg, Data.stacks, setPop]
  funext k; fin_cases k <;> rfl

theorem afterHeader_bad (v : Control) (bs : List Bool) (d : Data) :
    advance program (cfg (some (outer .afterHeader)) v {d with counter := false :: bs}) =
      cfg none (coreControl (some false, false)) {d with counter := bs} := by
  simp [advance, TM2.step, program, outer, TM2.stepAux, cfg, Data.stacks, setPop, failed]
  funext k; fin_cases k <;> rfl

theorem afterPayload_step (v : Control) (d : Data) (flag : Bool) (hv : v.2.1 = some flag) :
    advance program (cfg (some (outer .afterPayload)) v d) =
      if flag then cfg (some (outer .clearCounter)) v d
      else cfg none (coreControl (some false, false)) d := by
  cases flag <;> simp [advance, TM2.step, program, outer, TM2.stepAux, cfg, hv, failed, go]

theorem clear_cons (b : Bool) (q : List Bool) (v : Control) (d : Data) :
    advance program (cfg (some (outer .clearCounter)) v {d with counter := b :: q}) =
      cfg (some (outer .clearCounter)) (setPop v (some b)) {d with counter := q} := by
  simp [advance, TM2.step, program, outer, TM2.stepAux, cfg, Data.stacks, setPop, go]
  funext k; fin_cases k <;> rfl

theorem clear_nil (v : Control) (d : Data) :
    advance program (cfg (some (outer .clearCounter)) v {d with counter := []}) =
      cfg (some (outer .restorePayload)) (setPop v none) {d with counter := []} := by
  simp [advance, TM2.step, program, outer, TM2.stepAux, cfg, Data.stacks, setPop, go]

theorem clear_run (q : List Bool) (v : Control) (d : Data) :
    run (q.length + 1) (cfg (some (outer .clearCounter)) v {d with counter := q}) =
      cfg (some (outer .restorePayload)) (setPop v none) {d with counter := []} := by
  induction q generalizing v with
  | nil => simpa using run_succ (clear_nil v d) 0
  | cons b q ih =>
      rw [List.length_cons, run_succ (clear_cons b q v d), ih]
      rfl

theorem restore_cons (b : Bool) (xs : List Bool) (v : Control) (d : Data) :
    advance program (cfg (some (outer .restorePayload)) v {d with reversed := b :: xs}) =
      cfg (some (outer .restorePayload)) (setPop v (some b))
        {d with reversed := xs, payload := b :: d.payload} := by
  simp [advance, TM2.step, program, outer, TM2.stepAux, cfg, Data.stacks, setPop, go]
  funext k; fin_cases k <;> rfl

theorem restore_nil (v : Control) (d : Data) :
    advance program (cfg (some (outer .restorePayload)) v {d with reversed := []}) =
      cfg none (coreControl (some true, false)) {d with reversed := []} := by
  simp [advance, TM2.step, program, outer, TM2.stepAux, cfg, Data.stacks, setPop]

theorem restore_run (xs : List Bool) (v : Control) (d : Data) :
    run (xs.length + 1) (cfg (some (outer .restorePayload)) v {d with reversed := xs}) =
      cfg none (coreControl (some true, false)) {d with reversed := [], payload := xs.reverse ++ d.payload} := by
  induction xs generalizing v d with
  | nil => simpa using run_succ (restore_nil v d) 0
  | cons b xs ih =>
      rw [List.length_cons, run_succ (restore_cons b xs v d), ih (setPop v (some b))
        {d with payload := b :: d.payload}]
      simp [List.reverse_cons, List.append_assoc]

theorem finish_run (v : Control) (d : Data) (hv : v.2.1 = some true) :
    run (d.counter.length + d.reversed.length + 3) (cfg (some (outer .afterPayload)) v d) =
      cfg none (coreControl (some true, false))
        {d with counter := [], reversed := [], payload := d.reversed.reverse ++ d.payload} := by
  have hs := afterPayload_step v d true hv
  simp only [↓reduceIte] at hs
  have hc := clear_run d.counter v d
  have hr := restore_run d.reversed (setPop v none) {d with counter := []}
  rw [show d.counter.length + d.reversed.length + 3 =
    ((d.counter.length + 1) + (d.reversed.length + 1)) + 1 by omega, run_succ hs]
  exact (run_add hc _).trans hr

def success (payload suffix : List Bool) : Config :=
  cfg none (coreControl (some true, false))
    {input := suffix, count := List.replicate payload.length true, payload := payload}

def Bad (c : Config) : Prop := c.l = none ∧ c.var.2.1 = some false

theorem readChecked_natField (n : Nat) (suffix : List Bool) :
    ProtocolBinaryHeader.readChecked none (natField n ++ suffix) = some (n.bits, suffix) := by
  rw [ProtocolBinaryHeader.readChecked_spec]
  simp [natField, readField_append, ProtocolBinaryHeader.canonicalFrom_none,
    ProtocolBinaryHeader.canonical_of_bits]

/-- Total execution after any successfully read natural-number header. The
bound charges only the header and the consumed payload prefix. -/
theorem field_readNat (input rest : List Bool) (n : Nat)
    (hr : readNat input = some (n, rest)) :
    ∃ t ≤ 20 * (min n rest.length + 1) * (n.bits.length + 1), ∃ c,
      run t (cfg (some (.inl .scan)) initialControl {input := input}) = c ∧
      if n ≤ rest.length then c = success (rest.take n) (rest.drop n) else Bad c := by
  have hh : ProtocolBinaryHeader.readChecked none input = some (n.bits, rest) := by
    rw [← readNat_sound hr]
    exact readChecked_natField n rest
  obtain ⟨a, ha, v, he⟩ := header_run_success {input := input} n.bits rest hh
  have hs := afterHeader_good (headerControl v) n.bits {input := rest}
  have hp := (run_add he 1).trans (run_succ hs 0)
  obtain ⟨b, hb, q', hq, hbRun⟩ := payload_run {input := rest, counter := n.bits}
  simp only [bitsValue_bits, List.append_nil] at hb hbRun
  have hpre := (run_add hp b).trans hbRun
  let d : Data :=
    {input := rest.drop n, counter := q', reversed := (rest.take n).reverse,
      count := List.replicate (min n rest.length) true}
  by_cases hn : n ≤ rest.length
  · have hd : cfg (some (outer .afterPayload))
        (coreControl (some (decide (n ≤ rest.length)), false))
        {input := rest.drop n, counter := q', reversed := (rest.take n).reverse,
          count := List.replicate (min n rest.length) true} =
        cfg (some (outer .afterPayload)) (coreControl (some true, false)) d := by
      simp [hn, d]
    rw [hd] at hpre
    have hfinish := finish_run (coreControl (some true, false)) d rfl
    have hlen : (rest.take n).length = n := by simp [List.length_take, Nat.min_eq_left hn]
    have heq : cfg none (coreControl (some true, false))
        {d with counter := [], reversed := [], payload := d.reversed.reverse ++ d.payload} =
        success (rest.take n) (rest.drop n) := by
      simp [success, d, hlen, Nat.min_eq_left hn]
    rw [heq] at hfinish
    refine ⟨a + 1 + b + (d.counter.length + d.reversed.length + 3), ?_, _,
      (run_add hpre _).trans hfinish, by simp [hn]⟩
    simp only [d, List.length_reverse, hlen, Nat.min_eq_left hn] at hb ⊢
    change q'.length = n.bits.length at hq
    rw [hq]
    nlinarith
  · have hd : cfg (some (outer .afterPayload))
        (coreControl (some (decide (n ≤ rest.length)), false))
        {input := rest.drop n, counter := q', reversed := (rest.take n).reverse,
          count := List.replicate (min n rest.length) true} =
        cfg (some (outer .afterPayload)) (coreControl (some false, false)) d := by
      simp [hn, d]
    rw [hd] at hpre
    have hs' := afterPayload_step (coreControl (some false, false)) d false rfl
    simp only [Bool.false_eq_true, ↓reduceIte] at hs'
    refine ⟨a + 1 + b + 1, ?_, _, (run_add hpre 1).trans (run_succ hs' 0), ?_⟩
    · generalize min n rest.length = k at hb ⊢
      nlinarith
    · simp [hn, Bad, cfg, coreControl, run]

/-- A valid field is read without touching the suffix; empty payloads work.
All seven local scratch banks have their exact reusable final contents. -/
theorem field_encoded (payload suffix : List Bool) :
    ∃ t ≤ 20 * (payload.length + 1) * (payload.length.bits.length + 1),
      run t (cfg (some (.inl .scan)) initialControl
        {input := natField payload.length ++ (payload ++ suffix)}) = success payload suffix := by
  have hn : payload.length ≤ (payload ++ suffix).length := by simp
  obtain ⟨t, ht, c, he, hc⟩ := field_readNat
    (natField payload.length ++ (payload ++ suffix)) (payload ++ suffix) payload.length
    (readNat_append _ _)
  simp only [hn, ↓reduceIte] at hc
  simp only [List.take_left, List.drop_left] at hc
  rw [hc] at he
  exact ⟨t, by simpa [Nat.min_eq_left hn] using ht, he⟩

theorem readNat_lengths {input rest : List Bool} {n : Nat}
    (hr : readNat input = some (n, rest)) : n.bits.length ≤ input.length ∧ rest.length ≤ input.length := by
  have hh := congrArg List.length (readNat_sound hr)
  simp only [List.length_append, natField, field_length] at hh
  omega

/-- All raw inputs terminate. This fallback quadratic bound includes malformed
headers, noncanonical encodings, oversized lengths and truncated payloads. -/
theorem field_total (input : List Bool) :
    ∃ t ≤ 20 * (input.length + 1)^2, ∃ c,
      run t (cfg (some (.inl .scan)) initialControl {input := input}) = c ∧
      match readNat input with
      | none => Bad c
      | some (n, rest) => if n ≤ rest.length then c = success (rest.take n) (rest.drop n) else Bad c := by
  cases hr : readNat input with
  | some p =>
      obtain ⟨n, rest⟩ := p
      obtain ⟨t, ht, c, he, hc⟩ := field_readNat input rest n hr
      have hl := readNat_lengths hr
      have hm : min n rest.length ≤ input.length := (Nat.min_le_right _ _).trans hl.2
      have hb := Nat.mul_le_mul (Nat.mul_le_mul_left 20 (Nat.add_le_add_right hm 1))
        (Nat.add_le_add_right hl.1 1)
      refine ⟨t, ht.trans ?_, c, he, ?_⟩
      · simpa only [pow_two, Nat.mul_assoc] using hb
      · simpa [hr] using hc
  | none =>
      have hh : ProtocolBinaryHeader.readChecked none input = none := by
        have hmap := ProtocolBinaryHeader.readChecked_readNat input
        rw [hr] at hmap
        exact Option.map_eq_none_iff.mp hmap
      obtain ⟨t, ht, c, he, hp⟩ := header_run {input := input}
      have hv : c.stk 2 = [false] := by
        simpa [ProtocolBinaryHeader.Post, hh] using hp.2
      let d := headerData {input := input} c
      have hd : d = {d with counter := false :: []} := by
        change d = {d with counter := [false]}
        have hc : d.counter = [false] := hv
        rw [← hc]
      have hs := afterHeader_bad (headerControl c.var) [] d
      rw [← hd] at hs
      refine ⟨t + 1, ?_, _, (run_add he 1).trans (run_succ hs 0), ?_⟩
      · change t ≤ 2 * input.length + 2 at ht
        nlinarith [Nat.zero_le (input.length^2)]
      · simp [Bad, cfg, coreControl, run]

end EthInapproximability.CurrentPaper.SourceListMachineFields
