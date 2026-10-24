import EthInapproximability.CurrentPaper.SourceListMachineFields
import EthInapproximability.CurrentPaper.BitMachineBroadcast

/-! # A bounded natural field for graph normalization

Source: frozen v8 `06-eth.tex`, `thm:paper-sparse-gap-source`, and the explicit
graph encoding in `03-exact-hardness.tex`. A preserved physical cap is copied
before each canonical binary field is expanded to unary. The theorem below
is the valid-field execution theorem used after graph validation.
-/

namespace EthInapproximability.CurrentPaper.SourceNormalizationMachineField

open Turing TM2.Stmt BitMachineEncoding EncodedCommunication

inductive OuterLabel where
  | afterHeader | copyCap | restoreCap | beforeBound | afterBound | clearValue | clearBudget
  deriving DecidableEq, Fintype

abbrev Stack := Fin 8
abbrev Label := ProtocolBinaryHeader.Label ⊕ (ProtocolBoundedUnary.Label ⊕ OuterLabel)
abbrev Control := (ProtocolBinaryHeader.Control × ProtocolBoundedUnary.Control) × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control
abbrev Statement := TM2.Stmt (fun _ : Stack => Bool) Label Control

def outer (l : OuterLabel) : Label := .inr (.inr l)
def headerControl (v : ProtocolBinaryHeader.Control) : Control := ((v, (none, false)), none)
def boundControl (v : ProtocolBoundedUnary.Control) : Control := (((none, none), v), none)
def initialControl : Control := headerControl (none, none)
def doneControl (b : Bool) : Control := (((none, none), (none, false)), some b)
def setPop (v : Control) (b : Option Bool) : Control := (v.1, b)
def go (l : OuterLabel) : Statement := goto (fun _ => outer l)
def failed : Statement := load (fun _ => doneControl false) halt

def headerStack : Fin 3 ↪ Stack where
  toFun k := ⟨k.val, by omega⟩
  inj' := by intro a b h; apply Fin.ext; exact congrArg (fun k : Stack => k.val) h
def boundStack : Fin 4 ↪ Stack where
  toFun k := ⟨k.val + 2, by omega⟩
  inj' := by
    intro a b h
    apply Fin.ext
    have hh := congrArg (fun k : Stack => k.val) h
    simp only at hh
    omega

def program : Label → Statement
  | .inl l => BitMachineStackEmbedding.stmt headerStack Sum.inl headerControl (fun v => v.1.1)
      (some (outer .afterHeader)) (ProtocolBinaryHeader.program l)
  | .inr (.inl l) => BitMachineStackEmbedding.stmt boundStack (fun l => .inr (.inl l))
      boundControl (fun v => v.1.2) (some (outer .afterBound)) (ProtocolBoundedUnary.program l)
  | .inr (.inr .afterHeader) => pop 2 setPop
      (branch (fun v => v.2.getD false) (go .copyCap) failed)
  | .inr (.inr .copyCap) => BitMachineBroadcast.scanStep 6 7 (outer .copyCap) (outer .restoreCap)
  | .inr (.inr .restoreCap) =>
      BitMachineBroadcast.restoreStep 7 [6, 3] (outer .restoreCap) (outer .beforeBound)
  | .inr (.inr .beforeBound) => load (fun _ => boundControl (none, false))
      (goto (fun _ => .inr (.inl .zeroScan)))
  | .inr (.inr .afterBound) => pop 5 setPop
      (branch (fun v => v.2.getD false) (go .clearValue) failed)
  | .inr (.inr .clearValue) => pop 2 setPop
      (branch (fun v => v.2.isSome) (go .clearValue) (go .clearBudget))
  | .inr (.inr .clearBudget) => pop 3 setPop
      (branch (fun v => v.2.isSome) (go .clearBudget)
        (load (fun _ => doneControl true) halt))

structure Data where
  input : List Bool := []
  saved : List Bool := []
  value : List Bool := []
  budget : List Bool := []
  work : List Bool := []
  unary : List Bool := []
  cap : List Bool := []
  temp : List Bool := []

def Data.stacks (d : Data) : Stack → List Bool :=
  ![d.input, d.saved, d.value, d.budget, d.work, d.unary, d.cap, d.temp]
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
abbrev BoundConfig := TM2.Cfg (fun _ : Fin 4 => Bool)
  ProtocolBoundedUnary.Label ProtocolBoundedUnary.Control

def headerData (d : Data) (c : HeaderConfig) : Data :=
  {d with input := c.stk 0, saved := c.stk 1, value := c.stk 2}
def boundData (d : Data) (c : BoundConfig) : Data :=
  {d with value := c.stk 0, budget := c.stk 1, work := c.stk 2, unary := c.stk 3}

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

theorem boundBank (d : Data) (c : BoundConfig) :
    BitMachineStackEmbedding.bank boundStack d.stacks c.stk = (boundData d c).stacks := by
  funext j
  fin_cases j
  · apply BitMachineStackEmbedding.bank_outside; rintro ⟨k, h⟩; fin_cases k <;> cases h
  · apply BitMachineStackEmbedding.bank_outside; rintro ⟨k, h⟩; fin_cases k <;> cases h
  · exact BitMachineStackEmbedding.bank_at boundStack d.stacks c.stk 0
  · exact BitMachineStackEmbedding.bank_at boundStack d.stacks c.stk 1
  · exact BitMachineStackEmbedding.bank_at boundStack d.stacks c.stk 2
  · exact BitMachineStackEmbedding.bank_at boundStack d.stacks c.stk 3
  all_goals
    apply BitMachineStackEmbedding.bank_outside
    rintro ⟨k, h⟩
    fin_cases k <;> cases h

noncomputable def headerFrame (d : Data) (c : HeaderConfig) : Config :=
  BitMachineStackEmbedding.cfg headerStack d.stacks Sum.inl headerControl (some (outer .afterHeader)) c
noncomputable def boundFrame (d : Data) (c : BoundConfig) : Config :=
  BitMachineStackEmbedding.cfg boundStack d.stacks (fun l => .inr (.inl l)) boundControl
    (some (outer .afterBound)) c

theorem headerFrame_initial (d : Data) :
    headerFrame d (ProtocolBinaryHeader.cfg (some .scan) (none, none) d.input [] []) =
      cfg (some (.inl .scan)) initialControl {d with saved := [], value := []} := by
  unfold headerFrame BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg BitMachineInline.cfg
  rw [headerBank]
  rfl
theorem headerFrame_halted (d : Data) (c : HeaderConfig) (hc : c.l = none) :
    headerFrame d c = cfg (some (outer .afterHeader)) (headerControl c.var) (headerData d c) := by
  unfold headerFrame BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg BitMachineInline.cfg
  rw [hc, headerBank]
  rfl
theorem boundFrame_initial (d : Data) :
    boundFrame d (ProtocolBoundedUnary.cfg (some .zeroScan) (none, false) d.value d.budget [] []) =
      cfg (some (.inr (.inl .zeroScan))) (boundControl (none, false)) {d with work := [], unary := []} := by
  unfold boundFrame BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg BitMachineInline.cfg
  rw [boundBank]
  rfl
theorem boundFrame_halted (d : Data) (c : BoundConfig) (hc : c.l = none) :
    boundFrame d c = cfg (some (outer .afterBound)) (boundControl c.var) (boundData d c) := by
  unfold boundFrame BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg BitMachineInline.cfg
  rw [hc, boundBank]
  rfl

theorem header_run (d : Data) (bs rest : List Bool)
    (hr : ProtocolBinaryHeader.readChecked none d.input = some (bs, rest)) :
    ∃ t ≤ 3 * bs.length + 2, ∃ v : ProtocolBinaryHeader.Control,
      run t (cfg (some (.inl .scan)) initialControl {d with saved := [], value := []}) =
        cfg (some (outer .afterHeader)) (headerControl v)
          {d with input := rest, saved := [], value := true :: bs} := by
  obtain ⟨v, hv⟩ := SourceListMachineFields.header_success [] [] hr (popped := none)
  simp only [List.length_nil, Nat.add_zero, List.reverse_nil, List.nil_append, List.append_nil] at hv
  obtain ⟨n, hn, he⟩ := BitMachineStackEmbedding.outputs headerStack d.stacks Sum.inl
    headerControl (fun v => v.1.1) (fun _ => rfl) (some (outer .afterHeader))
    ProtocolBinaryHeader.program program (fun _ => rfl)
    (ProtocolBinaryHeader.cfg (some .scan) (none, none) d.input [] []) (3 * bs.length + 2)
    (by change (ProtocolBinaryHeader.run _ _).l = none; rw [hv]; rfl)
  change run n (headerFrame d _) = headerFrame d (ProtocolBinaryHeader.run _ _) at he
  rw [headerFrame_initial, hv, headerFrame_halted d _ rfl] at he
  exact ⟨n, hn, v, he⟩

theorem bounded_run (d : Data) :
    ∃ t ≤ (d.budget.length + 1) * (4 * d.value.length + 5), ∃ c : BoundConfig,
      run t (cfg (some (.inr (.inl .zeroScan))) (boundControl (none, false))
        {d with work := [], unary := []}) =
        cfg (some (outer .afterBound)) (boundControl c.var) (boundData d c) ∧
      c.stk 3 = ProtocolBoundedUnary.result d.value d.budget [] ∧
      (c.stk 0).length = d.value.length ∧ c.stk 2 = [] ∧ (c.stk 1).length ≤ d.budget.length := by
  obtain ⟨t, c, ht, he, hc, ho, hv, hw, hb⟩ :=
    ProtocolBoundedUnary.bounded_run_framed d.value d.budget []
  obtain ⟨n, hn, hr⟩ := BitMachineStackEmbedding.outputs boundStack d.stacks
    (fun l => .inr (.inl l)) boundControl (fun v => v.1.2) (fun _ => rfl)
    (some (outer .afterBound)) ProtocolBoundedUnary.program program (fun _ => rfl)
    (ProtocolBoundedUnary.cfg (some .zeroScan) (none, false) d.value d.budget [] []) t
    (by rw [← he] at hc; exact hc)
  change run n (boundFrame d _) = boundFrame d (ProtocolBoundedUnary.run _ _) at hr
  rw [boundFrame_initial, he, boundFrame_halted d c hc] at hr
  exact ⟨n, hn.trans ht, c, hr, ho, hv, hw, hb⟩

theorem copy_cap (cap : List Bool) (v : Control) (d : Data) :
    run (2 * cap.length + 2)
      (cfg (some (outer .copyCap)) v {d with budget := [], cap := cap, temp := []}) =
      cfg (some (outer .beforeBound)) (v.1, none) {d with budget := cap, cap := cap, temp := []} := by
  let bank := ({d with budget := [], cap := cap, temp := []} : Data).stacks
  have hs := BitMachineBroadcast.scan_run program (6 : Stack) 7 (by decide)
    (outer .copyCap) (outer .restoreCap) rfl v.1 v.2 cap [] bank
  have hi : BitMachineBroadcast.contents 6 7 bank cap [] = bank := by
    funext k; fin_cases k <;> rfl
  rw [hi] at hs
  simp only [List.append_nil] at hs
  have hr := BitMachineBroadcast.restore_run program (7 : Stack) [6, 3]
    (by decide) (by decide) (outer .restoreCap) (outer .beforeBound) rfl v.1 none
    cap.reverse (Function.update bank 6 [])
  simp only [List.length_reverse, List.reverse_reverse] at hr
  have he := (BitMachineBroadcast.run_add program hs (cap.length + 1)).trans hr
  have hf : Function.update
      (BitMachineBroadcast.prepend [6, 3] cap (Function.update bank 6 [])) 7 [] =
      ({d with budget := cap, cap := cap, temp := []} : Data).stacks := by
    funext k
    fin_cases k <;> simp [BitMachineBroadcast.prepend, bank, Data.stacks]
  rw [hf] at he
  simpa only [BitMachineBroadcast.run, run, cfg, Nat.two_mul, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using he

theorem afterHeader_good (v : Control) (bs : List Bool) (d : Data) :
    advance program (cfg (some (outer .afterHeader)) v {d with value := true :: bs}) =
      cfg (some (outer .copyCap)) (setPop v (some true)) {d with value := bs} := by
  simp [advance, TM2.step, program, outer, TM2.stepAux, cfg, Data.stacks, setPop, go]
  funext k; fin_cases k <;> rfl
theorem beforeBound_step (v : Control) (d : Data) :
    advance program (cfg (some (outer .beforeBound)) v d) =
      cfg (some (.inr (.inl .zeroScan))) (boundControl (none, false)) d := by
  simp [advance, TM2.step, program, outer, TM2.stepAux, cfg]
theorem afterBound_good (v : Control) (bs : List Bool) (d : Data) :
    advance program (cfg (some (outer .afterBound)) v {d with unary := true :: bs}) =
      cfg (some (outer .clearValue)) (setPop v (some true)) {d with unary := bs} := by
  simp [advance, TM2.step, program, outer, TM2.stepAux, cfg, Data.stacks, setPop, go]
  funext k; fin_cases k <;> rfl

theorem clearValue_cons (b : Bool) (bs : List Bool) (v : Control) (d : Data) :
    advance program (cfg (some (outer .clearValue)) v {d with value := b :: bs}) =
      cfg (some (outer .clearValue)) (setPop v (some b)) {d with value := bs} := by
  simp [advance, TM2.step, program, outer, TM2.stepAux, cfg, Data.stacks, setPop, go]
  funext k; fin_cases k <;> rfl
theorem clearValue_nil (v : Control) (d : Data) :
    advance program (cfg (some (outer .clearValue)) v {d with value := []}) =
      cfg (some (outer .clearBudget)) (setPop v none) {d with value := []} := by
  simp [advance, TM2.step, program, outer, TM2.stepAux, cfg, Data.stacks, setPop, go]
theorem clearValue_run (bs : List Bool) (v : Control) (d : Data) :
    run (bs.length + 1) (cfg (some (outer .clearValue)) v {d with value := bs}) =
      cfg (some (outer .clearBudget)) (setPop v none) {d with value := []} := by
  induction bs generalizing v with
  | nil => simpa using run_succ (clearValue_nil v d) 0
  | cons b bs ih => rw [List.length_cons, run_succ (clearValue_cons b bs v d), ih]; rfl

theorem clearBudget_cons (b : Bool) (bs : List Bool) (v : Control) (d : Data) :
    advance program (cfg (some (outer .clearBudget)) v {d with budget := b :: bs}) =
      cfg (some (outer .clearBudget)) (setPop v (some b)) {d with budget := bs} := by
  simp [advance, TM2.step, program, outer, TM2.stepAux, cfg, Data.stacks, setPop, go]
  funext k; fin_cases k <;> rfl
theorem clearBudget_nil (v : Control) (d : Data) :
    advance program (cfg (some (outer .clearBudget)) v {d with budget := []}) =
      cfg none (doneControl true) {d with budget := []} := by
  simp [advance, TM2.step, program, outer, TM2.stepAux, cfg, Data.stacks, setPop]
theorem clearBudget_run (bs : List Bool) (v : Control) (d : Data) :
    run (bs.length + 1) (cfg (some (outer .clearBudget)) v {d with budget := bs}) =
      cfg none (doneControl true) {d with budget := []} := by
  induction bs generalizing v with
  | nil => simpa using run_succ (clearBudget_nil v d) 0
  | cons b bs ih => rw [List.length_cons, run_succ (clearBudget_cons b bs v d), ih]

theorem cleanup_run (v : Control) (d : Data) :
    run (d.value.length + d.budget.length + 2) (cfg (some (outer .clearValue)) v d) =
      cfg none (doneControl true) {d with value := [], budget := []} := by
  have hv := clearValue_run d.value v d
  have hb := clearBudget_run d.budget (setPop v none) {d with value := []}
  rw [show d.value.length + d.budget.length + 2 = (d.value.length + 1) + (d.budget.length + 1) by omega]
  exact (run_add hv _).trans hb

/-- A canonical natural field bounded by the preserved cap is read to unary,
with all local scratch cleared and the suffix unchanged. -/
theorem field_encoded_cap (n : Nat) (cap : List Bool)
    (hn : n ≤ cap.length) (suffix : List Bool) :
    ∃ t ≤ 20 * (cap.length + 1) * (n.bits.length + 1),
      run t (cfg (some (.inl .scan)) initialControl
        {input := natField n ++ suffix, cap := cap}) =
      cfg none (doneControl true)
        {input := suffix, unary := List.replicate n true, cap := cap} := by
  obtain ⟨a, ha, v, he⟩ := header_run
    {input := natField n ++ suffix, cap := cap} n.bits suffix
    (SourceListMachineFields.readChecked_natField n suffix)
  have hs := afterHeader_good (headerControl v) n.bits {input := suffix, cap := cap}
  have hp := (run_add he 1).trans (run_succ hs 0)
  let d : Data := {input := suffix, value := n.bits, cap := cap}
  have hcopy := copy_cap cap (setPop (headerControl v) (some true)) d
  have hp₂ := (run_add hp (2 * cap.length + 2)).trans hcopy
  have hs₂ := beforeBound_step ((setPop (headerControl v) (some true)).1, none)
    {d with budget := cap, cap := cap, temp := []}
  have hp₃ := (run_add hp₂ 1).trans (run_succ hs₂ 0)
  let db : Data := {d with budget := cap}
  obtain ⟨b, hb, c, hc, ho, hv, hw, hbudget⟩ := bounded_run db
  have hp₄ := (run_add hp₃ b).trans hc
  have hunary : c.stk 3 = true :: List.replicate n true := by
    simpa [ProtocolBoundedUnary.result, db, d, bitsValue_bits, hn, Nat.min_eq_left hn] using ho
  let dc := boundData db c
  have hdc : dc = {dc with unary := true :: List.replicate n true} := by
    have hh : dc.unary = true :: List.replicate n true := hunary
    rw [← hh]
  have hs₃ := afterBound_good (boundControl c.var) (List.replicate n true) dc
  rw [← hdc] at hs₃
  have hp₅ := (run_add hp₄ 1).trans (run_succ hs₃ 0)
  have hfinish := cleanup_run (setPop (boundControl c.var) (some true))
    {dc with unary := List.replicate n true}
  have hout : {dc with unary := List.replicate n true, value := [], budget := []} =
      ({input := suffix, unary := List.replicate n true, cap := cap} : Data) := by
    simp [dc, boundData, db, d, hw]
  rw [hout] at hfinish
  refine ⟨a + 1 + (2 * cap.length + 2) + 1 + b + 1 +
      (dc.value.length + dc.budget.length + 2), ?_,
    (run_add hp₅ _).trans hfinish⟩
  change (c.stk 0).length = n.bits.length at hv
  simp only [db, d] at hbudget hb
  change a + 1 + (2 * cap.length + 2) + 1 + b + 1 +
    ((c.stk 0).length + (c.stk 1).length + 2) ≤ _
  rw [hv]
  nlinarith

theorem field_encoded (n N : Nat) (hn : n ≤ N) (suffix : List Bool) :
    ∃ t ≤ 20 * (N + 1) * (n.bits.length + 1),
      run t (cfg (some (.inl .scan)) initialControl
        {input := natField n ++ suffix, cap := List.replicate N true}) =
      cfg none (doneControl true)
        {input := suffix, unary := List.replicate n true, cap := List.replicate N true} := by
  simpa only [List.length_replicate] using
    field_encoded_cap n (List.replicate N true) (by simpa using hn) suffix

end EthInapproximability.CurrentPaper.SourceNormalizationMachineField
