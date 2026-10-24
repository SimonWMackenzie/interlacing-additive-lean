import EthInapproximability.CurrentPaper.SourceListMachineFields

/-! # Initializing a streaming source-list transformation

Source: frozen v8 `B-effectivity-details.tex`, explicit source lists. Read only
the outer canonical count header, retain its binary word for the loop counter,
and write the same header into a reversed output accumulator by physical steps.
No unary expansion of the number of list entries occurs.
-/

namespace EthInapproximability.CurrentPaper.SourceListMachineInitialize

open Turing TM2.Stmt BitMachineEncoding EncodedCommunication

inductive OuterLabel where
  | afterHeader | copyCount | restoreCount
  deriving DecidableEq, Fintype

abbrev Stack := Fin 5
abbrev Label := ProtocolBinaryHeader.Label ⊕ OuterLabel
abbrev Control := ProtocolBinaryHeader.Control × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control
abbrev Statement := TM2.Stmt (fun _ : Stack => Bool) Label Control

def headerControl (v : ProtocolBinaryHeader.Control) : Control := (v, none)
def initialControl : Control := headerControl (none, none)
def doneControl (flag : Bool) : Control := ((none, none), some flag)
def setPop (v : Control) (b : Option Bool) : Control := (v.1, b)
def go (l : OuterLabel) : Statement := goto (fun _ => .inr l)

def headerStack : Fin 3 ↪ Stack where
  toFun k := ⟨k.val, by omega⟩
  inj' := by
    intro a b h
    apply Fin.ext
    exact congrArg (fun k : Stack => k.val) h

def program : Label → Statement
  | .inl l => BitMachineStackEmbedding.stmt headerStack Sum.inl headerControl Prod.fst
      (some (.inr .afterHeader)) (ProtocolBinaryHeader.program l)
  | .inr .afterHeader => pop 2 setPop
      (branch (fun v => v.2.getD false) (go .copyCount)
        (load (fun _ => doneControl false) halt))
  | .inr .copyCount => pop 2 setPop
      (branch (fun v => v.2.isSome)
        (push 3 (fun v => v.2.getD false)
          (push 4 (fun _ => true) (push 4 (fun v => v.2.getD false) (go .copyCount))))
        (push 4 (fun _ => false) (go .restoreCount)))
  | .inr .restoreCount => pop 3 setPop
      (branch (fun v => v.2.isSome)
        (push 2 (fun v => v.2.getD false) (go .restoreCount))
        (load (fun _ => doneControl true) halt))

structure Data where
  input : List Bool := []
  saved : List Bool := []
  count : List Bool := []
  temp : List Bool := []
  output : List Bool := []

def Data.stacks (d : Data) : Stack → List Bool := ![d.input, d.saved, d.count, d.temp, d.output]
def cfg (l : Option Label) (v : Control) (d : Data) : Config := ⟨l, v, d.stacks⟩
def run (n : Nat) (c : Config) : Config := ((advance program)^[n]) c

theorem run_succ {c c' : Config} (h : advance program c = c') (n : Nat) :
    run (n + 1) c = run n c' := by
  exact (Function.iterate_succ_apply _ _ _).trans (congrArg (run n) h)
theorem run_add {c c' : Config} {n : Nat} (h : run n c = c') (m : Nat) :
    run (n + m) c = run m c' := by
  rw [Nat.add_comm, run, Function.iterate_add_apply]
  exact congrArg (run m) h

abbrev HeaderConfig := TM2.Cfg (fun _ : Fin 3 => Bool)
  ProtocolBinaryHeader.Label ProtocolBinaryHeader.Control
def headerData (d : Data) (c : HeaderConfig) : Data :=
  {d with input := c.stk 0, saved := c.stk 1, count := c.stk 2}

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

noncomputable def headerFrame (d : Data) (c : HeaderConfig) : Config :=
  BitMachineStackEmbedding.cfg headerStack d.stacks Sum.inl headerControl (some (.inr .afterHeader)) c

theorem headerFrame_initial (d : Data) :
    headerFrame d (ProtocolBinaryHeader.cfg (some .scan) (none, none) d.input [] []) =
      cfg (some (.inl .scan)) initialControl {d with saved := [], count := []} := by
  unfold headerFrame BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg BitMachineInline.cfg
  rw [headerBank]
  rfl

theorem headerFrame_halted (d : Data) (c : HeaderConfig) (hc : c.l = none) :
    headerFrame d c = cfg (some (.inr .afterHeader)) (headerControl c.var) (headerData d c) := by
  unfold headerFrame BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg BitMachineInline.cfg
  rw [hc, headerBank]
  rfl

theorem header_run (d : Data) :
    ∃ t ≤ 2 * d.input.length + 2, ∃ c : HeaderConfig,
      run t (cfg (some (.inl .scan)) initialControl {d with saved := [], count := []}) =
        cfg (some (.inr .afterHeader)) (headerControl c.var) (headerData d c) ∧
      ProtocolBinaryHeader.Post none d.input [] [] c := by
  obtain ⟨t, ht, hp⟩ := ProtocolBinaryHeader.scan_correct d.input none none [] []
  obtain ⟨n, hn, he⟩ := BitMachineStackEmbedding.outputs headerStack d.stacks Sum.inl
    headerControl Prod.fst (fun _ => rfl) (some (.inr .afterHeader))
    ProtocolBinaryHeader.program program (fun _ => rfl)
    (ProtocolBinaryHeader.cfg (some .scan) (none, none) d.input [] []) t hp.1
  change run n (headerFrame d _) = headerFrame d (ProtocolBinaryHeader.run t _) at he
  rw [headerFrame_initial, headerFrame_halted d _ hp.1] at he
  exact ⟨n, hn.trans (by simpa using ht), _, he, hp⟩

theorem header_run_success (d : Data) (bs rest : List Bool)
    (hr : ProtocolBinaryHeader.readChecked none d.input = some (bs, rest)) :
    ∃ t ≤ 3 * bs.length + 2, ∃ v : ProtocolBinaryHeader.Control,
      run t (cfg (some (.inl .scan)) initialControl {d with saved := [], count := []}) =
        cfg (some (.inr .afterHeader)) (headerControl v)
          {d with input := rest, saved := [], count := true :: bs} := by
  obtain ⟨v, hv⟩ := SourceListMachineFields.header_success [] [] hr (popped := none)
  simp only [List.length_nil, Nat.add_zero, List.reverse_nil, List.nil_append, List.append_nil] at hv
  obtain ⟨n, hn, he⟩ := BitMachineStackEmbedding.outputs headerStack d.stacks Sum.inl
    headerControl Prod.fst (fun _ => rfl) (some (.inr .afterHeader))
    ProtocolBinaryHeader.program program (fun _ => rfl)
    (ProtocolBinaryHeader.cfg (some .scan) (none, none) d.input [] []) (3 * bs.length + 2)
    (by change (ProtocolBinaryHeader.run _ _).l = none; rw [hv]; rfl)
  change run n (headerFrame d _) = headerFrame d (ProtocolBinaryHeader.run _ _) at he
  rw [headerFrame_initial, hv, headerFrame_halted d _ rfl] at he
  exact ⟨n, hn, v, he⟩

theorem afterHeader_good (v : Control) (bs : List Bool) (d : Data) :
    advance program (cfg (some (.inr .afterHeader)) v {d with count := true :: bs}) =
      cfg (some (.inr .copyCount)) (setPop v (some true)) {d with count := bs} := by
  simp [advance, TM2.step, program, TM2.stepAux, cfg, Data.stacks, setPop, go]
  funext k; fin_cases k <;> rfl

theorem afterHeader_bad (v : Control) (bs : List Bool) (d : Data) :
    advance program (cfg (some (.inr .afterHeader)) v {d with count := false :: bs}) =
      cfg none (doneControl false) {d with count := bs} := by
  simp [advance, TM2.step, program, TM2.stepAux, cfg, Data.stacks, setPop]
  funext k; fin_cases k <;> rfl

theorem copy_cons (b : Bool) (bs : List Bool) (v : Control) (d : Data) :
    advance program (cfg (some (.inr .copyCount)) v {d with count := b :: bs}) =
      cfg (some (.inr .copyCount)) (setPop v (some b))
        {d with count := bs, temp := b :: d.temp, output := b :: true :: d.output} := by
  simp [advance, TM2.step, program, TM2.stepAux, cfg, Data.stacks, setPop, go]
  funext k; fin_cases k <;> rfl

theorem copy_nil (v : Control) (d : Data) :
    advance program (cfg (some (.inr .copyCount)) v {d with count := []}) =
      cfg (some (.inr .restoreCount)) (setPop v none) {d with count := [], output := false :: d.output} := by
  simp [advance, TM2.step, program, TM2.stepAux, cfg, Data.stacks, setPop, go]
  funext k; fin_cases k <;> rfl

theorem copy_run (bs : List Bool) (v : Control) (d : Data) :
    run (bs.length + 1) (cfg (some (.inr .copyCount)) v {d with count := bs}) =
      cfg (some (.inr .restoreCount)) (setPop v none)
        {d with count := [], temp := bs.reverse ++ d.temp, output := (field bs).reverse ++ d.output} := by
  induction bs generalizing v d with
  | nil => simpa [field] using run_succ (copy_nil v d) 0
  | cons b bs ih =>
      rw [List.length_cons, run_succ (copy_cons b bs v d),
        ih (setPop v (some b)) {d with temp := b :: d.temp, output := b :: true :: d.output}]
      simp [field, List.reverse_cons, List.append_assoc, cfg, setPop]

theorem restore_cons (b : Bool) (bs : List Bool) (v : Control) (d : Data) :
    advance program (cfg (some (.inr .restoreCount)) v {d with temp := b :: bs}) =
      cfg (some (.inr .restoreCount)) (setPop v (some b)) {d with temp := bs, count := b :: d.count} := by
  simp [advance, TM2.step, program, TM2.stepAux, cfg, Data.stacks, setPop, go]
  funext k; fin_cases k <;> rfl

theorem restore_nil (v : Control) (d : Data) :
    advance program (cfg (some (.inr .restoreCount)) v {d with temp := []}) =
      cfg none (doneControl true) {d with temp := []} := by
  simp [advance, TM2.step, program, TM2.stepAux, cfg, Data.stacks, setPop]

theorem restore_run (bs : List Bool) (v : Control) (d : Data) :
    run (bs.length + 1) (cfg (some (.inr .restoreCount)) v {d with temp := bs}) =
      cfg none (doneControl true) {d with temp := [], count := bs.reverse ++ d.count} := by
  induction bs generalizing v d with
  | nil => simpa using run_succ (restore_nil v d) 0
  | cons b bs ih =>
      rw [List.length_cons, run_succ (restore_cons b bs v d),
        ih (setPop v (some b)) {d with count := b :: d.count}]
      simp [List.reverse_cons, List.append_assoc]

theorem copy_restore (bs : List Bool) (v : Control) (d : Data) :
    run (2 * bs.length + 2) (cfg (some (.inr .copyCount)) v {d with count := bs, temp := []}) =
      cfg none (doneControl true)
        {d with count := bs, temp := [], output := (field bs).reverse ++ d.output} := by
  have hs := copy_run bs v {d with temp := []}
  simp only [List.append_nil] at hs
  have hr := restore_run bs.reverse (setPop v none)
    {d with count := [], output := (field bs).reverse ++ d.output}
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hr
  rw [show 2 * bs.length + 2 = (bs.length + 1) + (bs.length + 1) by omega]
  exact (run_add hs _).trans hr

/-- The valid outer header is processed in time independent of the suffix and
of the numerical value of the branch count. Existing output is preserved. -/
theorem init_encoded (n : Nat) (suffix output : List Bool) :
    ∃ t ≤ 5 * n.bits.length + 5,
      run t (cfg (some (.inl .scan)) initialControl
        {input := natField n ++ suffix, output := output}) =
      cfg none (doneControl true)
        {input := suffix, count := n.bits, output := (natField n).reverse ++ output} := by
  obtain ⟨a, ha, v, he⟩ := header_run_success {input := natField n ++ suffix, output := output}
    n.bits suffix (SourceListMachineFields.readChecked_natField n suffix)
  have hs := afterHeader_good (headerControl v) n.bits {input := suffix, output := output}
  have hp := (run_add he 1).trans (run_succ hs 0)
  have hf := copy_restore n.bits (setPop (headerControl v) (some true)) {input := suffix, output := output}
  exact ⟨a + 1 + (2 * n.bits.length + 2), by omega, (run_add hp _).trans hf⟩

def Bad (output : List Bool) (c : Config) : Prop :=
  c.l = none ∧ c.var.2 = some false ∧ c.stk 4 = output

/-- Every raw input either initializes its exact canonical header or rejects;
the rejection case leaves the pre-existing output accumulator intact. -/
theorem init_total (input output : List Bool) :
    ∃ t ≤ 5 * input.length + 5, ∃ c,
      run t (cfg (some (.inl .scan)) initialControl {input := input, output := output}) = c ∧
      match readNat input with
      | none => Bad output c
      | some (n, suffix) => c = cfg none (doneControl true)
          {input := suffix, count := n.bits, output := (natField n).reverse ++ output} := by
  cases hr : readNat input with
  | some p =>
      obtain ⟨n, suffix⟩ := p
      obtain ⟨t, ht, he⟩ := init_encoded n suffix output
      rw [readNat_sound hr] at he
      have hl := (SourceListMachineFields.readNat_lengths hr).1
      exact ⟨t, by omega, _, he, by simp⟩
  | none =>
      have hh : ProtocolBinaryHeader.readChecked none input = none := by
        have hmap := ProtocolBinaryHeader.readChecked_readNat input
        rw [hr] at hmap
        exact Option.map_eq_none_iff.mp hmap
      obtain ⟨t, ht, c, he, hp⟩ := header_run {input := input, output := output}
      have hv : c.stk 2 = [false] := by
        simpa [ProtocolBinaryHeader.Post, hh] using hp.2
      let d := headerData {input := input, output := output} c
      have hd : d = {d with count := false :: []} := by
        have hc : d.count = [false] := hv
        rw [← hc]
      have hs := afterHeader_bad (headerControl c.var) [] d
      rw [← hd] at hs
      refine ⟨t + 1, ?_, _, (run_add he 1).trans (run_succ hs 0), ?_⟩
      · change t ≤ 2 * input.length + 2 at ht
        omega
      · simp [Bad, cfg, doneControl, run, Data.stacks, d, headerData]

end EthInapproximability.CurrentPaper.SourceListMachineInitialize
