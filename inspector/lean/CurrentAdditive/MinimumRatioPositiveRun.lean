import CurrentAdditive.MinimumRatioPositiveMachine

namespace CurrentAdditive.MinimumRatioPositiveRun

open Turing
open EthInapproximability.CurrentPaper
open BitMachineEncoding
open MinimumRatioPositiveMachine

def run (t : Nat) (c : TM2.Cfg (fun _ : Stack => Bool) Label Control) :=
  ((advance program)^[t]) c

theorem run_add (n m : Nat)
    (c : TM2.Cfg (fun _ : Stack => Bool) Label Control) :
    run (n + m) c = run m (run n c) := by
  simp only [run, Nat.add_comm n m, Function.iterate_add_apply]

theorem run_one (c : TM2.Cfg (fun _ : Stack => Bool) Label Control) :
    run 1 c = advance program c := by simp [run]

def cfg (l : Option Label) (v : Control) (S : Stack → List Bool) :=
  (⟨l,v,S⟩ : TM2.Cfg (fun _ : Stack => Bool) Label Control)

def inputBank (input : List Bool) : Stack → List Bool :=
  fun j => if j = 2 then input else []

def outerBank (B : BitMachineBankCodec.Bank 2) : Stack → List Bool :=
  fun j => if j = 0 then B 0 else if j = 1 then B 1 else []

private theorem outer_contents (F : Stack → List Bool)
    (hF : ∀ j : Stack, 5 ≤ j.val → F j = [])
    (B : BitMachineBankCodec.Bank 2)
    (source saved output : List Bool) :
    BitMachineStackEmbedding.bank outerSlot F
      (BitMachineBankCodec.contents B source saved output) =
    (fun j : Stack => if j = 0 then B 0 else if j = 1 then B 1 else
      if j = 2 then source else if j = 3 then saved else if j = 4 then output
      else []) := by
  funext j
  fin_cases j
  · change BitMachineStackEmbedding.bank outerSlot F
      (BitMachineBankCodec.contents B source saved output) (outerSlot (.inl 0)) = _
    rw [BitMachineStackEmbedding.bank_at]
    simp [outerSlot, BitMachineBankCodec.contents]
  · change BitMachineStackEmbedding.bank outerSlot F
      (BitMachineBankCodec.contents B source saved output) (outerSlot (.inl 1)) = _
    rw [BitMachineStackEmbedding.bank_at]
    simp [outerSlot, BitMachineBankCodec.contents]
  · change BitMachineStackEmbedding.bank outerSlot F
      (BitMachineBankCodec.contents B source saved output) (outerSlot (.inr 0)) = _
    rw [BitMachineStackEmbedding.bank_at]
    simp [outerSlot, BitMachineBankCodec.contents]
  · change BitMachineStackEmbedding.bank outerSlot F
      (BitMachineBankCodec.contents B source saved output) (outerSlot (.inr 1)) = _
    rw [BitMachineStackEmbedding.bank_at]
    simp [outerSlot, BitMachineBankCodec.contents]
  · change BitMachineStackEmbedding.bank outerSlot F
      (BitMachineBankCodec.contents B source saved output) (outerSlot (.inr 2)) = _
    rw [BitMachineStackEmbedding.bank_at]
    simp [outerSlot, BitMachineBankCodec.contents]
  all_goals
    rw [BitMachineStackEmbedding.bank_outside outerSlot _ _ _ (by
      rintro ⟨k,hk⟩
      cases k with
      | inl k => fin_cases k <;> simp [outerSlot] at hk
      | inr k => fin_cases k <;> simp [outerSlot] at hk)]
    simp [hF]

theorem outer_start (input : List Bool) :
    BitMachineStackEmbedding.cfg outerSlot (inputBank input)
      Label.outer (fun b => {initial with outer := b}) (some .afterOuter)
      (BitMachineBankCodec.parserCfg (K := 2) (some (.scan 0)) none
        (fun _ => []) input [] []) =
    cfg (some (.outer (.scan 0))) initial (inputBank input) := by
  unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg cfg
  congr 1
  have hF : ∀ j : Stack, 5 ≤ j.val → inputBank input j = [] := by
    intro j hj
    have hj2 : j ≠ 2 := by intro he; subst j; omega
    simp [inputBank, hj2]
  have hb : BitMachineStackEmbedding.bank outerSlot (inputBank input)
      (BitMachineBankCodec.contents (fun _ => []) input [] []) = inputBank input := by
    rw [outer_contents (inputBank input) hF]
    funext j
    fin_cases j <;> simp [inputBank]
  simpa only [BitMachineBankCodec.parserCfg] using hb

theorem outer_end (B : BitMachineBankCodec.Bank 2) :
    BitMachineStackEmbedding.cfg outerSlot (inputBank [])
      Label.outer (fun b => {initial with outer := b}) (some .afterOuter)
      (BitMachineBankCodec.parserCfg (K := 2) none (some true) B [] [] []) =
    cfg (some .afterOuter) {initial with outer := some true} (outerBank B) := by
  unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg cfg
  congr 1
  have hF : ∀ j : Stack, 5 ≤ j.val → inputBank [] j = [] := by
    intro j hj
    simp [inputBank]
  have hb : BitMachineStackEmbedding.bank outerSlot (inputBank [])
      (BitMachineBankCodec.contents B [] [] []) = outerBank B := by
    rw [outer_contents (inputBank []) hF]
    funext j
    fin_cases j <;> simp [outerBank]
  simpa only [BitMachineBankCodec.parserCfg] using hb

theorem outer_run (input : List Bool) (B : BitMachineBankCodec.Bank 2)
    (hd : BitMachineBankCodec.decode 2 input = some B) :
    ∃ t ≤ 5*(input.length+1),
      run t (cfg (some (.outer (.scan 0))) initial (inputBank input)) =
        cfg (some .afterOuter) {initial with outer := some true} (outerBank B) := by
  obtain ⟨t,ht,hp⟩ := BitMachineBankCodec.parser_correct 2 input []
  rw [hd] at hp
  change BitMachineBankCodec.parserRun t
    (BitMachineBankCodec.parserCfg (some (.scan 0)) none
      (fun _ => []) input [] []) =
    BitMachineBankCodec.parserCfg none (some true) B [] [] [] at hp
  have hh := congrArg (fun c => c.l) hp
  change _ = none at hh
  obtain ⟨u,hu,hr⟩ := BitMachineStackEmbedding.outputs
    outerSlot (inputBank input) Label.outer
    (fun b => {initial with outer := b}) Control.outer
    (by intro b; rfl) (some .afterOuter)
    (BitMachineBankCodec.parser 2) program (by intro l; rfl)
    (BitMachineBankCodec.parserCfg (some (.scan 0)) none
      (fun _ => []) input [] []) t hh
  refine ⟨u, hu.trans ht, ?_⟩
  change run u _ = _ at hr
  rw [outer_start input] at hr
  unfold BitMachineBankCodec.parserRun at hp
  rw [hp] at hr
  have he : BitMachineStackEmbedding.cfg outerSlot (inputBank input)
      Label.outer (fun b => {initial with outer := b}) (some .afterOuter)
      (BitMachineBankCodec.parserCfg (K := 2) none (some true) B [] [] []) =
      cfg (some .afterOuter) {initial with outer := some true} (outerBank B) := by
    unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
      BitMachineInline.cfg cfg
    congr 1
    have hF : ∀ j : Stack, 5 ≤ j.val → inputBank input j = [] := by
      intro j hj
      have hj2 : j ≠ 2 := by intro he; subst j; omega
      simp [inputBank, hj2]
    have hb : BitMachineStackEmbedding.bank outerSlot (inputBank input)
        (BitMachineBankCodec.contents B [] [] []) = outerBank B := by
      rw [outer_contents (inputBank input) hF]
      funext j
      fin_cases j <;> simp [outerBank]
    simpa only [BitMachineBankCodec.parserCfg] using hb
  exact hr.trans he

def innerBank (B : BitMachineBankCodec.Bank 2)
    (C : BitMachineBankCodec.Bank 3) : Stack → List Bool :=
  fun j => if j = 0 then B 0 else if j = 5 then C 0 else
    if j = 6 then C 1 else if j = 7 then C 2 else []

private theorem inner_contents (B : BitMachineBankCodec.Bank 2)
    (C : BitMachineBankCodec.Bank 3)
    (source saved output : List Bool) :
    BitMachineStackEmbedding.bank innerSlot (outerBank B)
      (BitMachineBankCodec.contents C source saved output) =
    (fun j : Stack => if j = 0 then B 0 else if j = 5 then C 0 else
      if j = 6 then C 1 else if j = 7 then C 2 else
      if j = 1 then source else if j = 8 then saved else if j = 9 then output
      else []) := by
  funext j
  fin_cases j
  · rw [BitMachineStackEmbedding.bank_outside innerSlot _ _ _ (by
      rintro ⟨k,hk⟩
      cases k with
      | inl k => fin_cases k <;> simp [innerSlot] at hk
      | inr k => fin_cases k <;> simp [innerSlot] at hk)]
    simp [outerBank]
  all_goals
    first
    | change BitMachineStackEmbedding.bank innerSlot (outerBank B)
        (BitMachineBankCodec.contents C source saved output)
        (innerSlot (.inl 0)) = _
      rw [BitMachineStackEmbedding.bank_at]
      simp [BitMachineBankCodec.contents]
    | change BitMachineStackEmbedding.bank innerSlot (outerBank B)
        (BitMachineBankCodec.contents C source saved output)
        (innerSlot (.inl 1)) = _
      rw [BitMachineStackEmbedding.bank_at]
      simp [BitMachineBankCodec.contents]
    | change BitMachineStackEmbedding.bank innerSlot (outerBank B)
        (BitMachineBankCodec.contents C source saved output)
        (innerSlot (.inl 2)) = _
      rw [BitMachineStackEmbedding.bank_at]
      simp [BitMachineBankCodec.contents]
    | change BitMachineStackEmbedding.bank innerSlot (outerBank B)
        (BitMachineBankCodec.contents C source saved output)
        (innerSlot (.inr 0)) = _
      rw [BitMachineStackEmbedding.bank_at]
      simp [BitMachineBankCodec.contents]
    | change BitMachineStackEmbedding.bank innerSlot (outerBank B)
        (BitMachineBankCodec.contents C source saved output)
        (innerSlot (.inr 1)) = _
      rw [BitMachineStackEmbedding.bank_at]
      simp [BitMachineBankCodec.contents]
    | change BitMachineStackEmbedding.bank innerSlot (outerBank B)
        (BitMachineBankCodec.contents C source saved output)
        (innerSlot (.inr 2)) = _
      rw [BitMachineStackEmbedding.bank_at]
      simp [BitMachineBankCodec.contents]
    | rw [BitMachineStackEmbedding.bank_outside innerSlot _ _ _ (by
          rintro ⟨k,hk⟩
          cases k with
          | inl k => fin_cases k <;> simp [innerSlot] at hk
          | inr k => fin_cases k <;> simp [innerSlot] at hk)]
      simp [outerBank]

theorem inner_start (B : BitMachineBankCodec.Bank 2) :
    BitMachineStackEmbedding.cfg innerSlot (outerBank B)
      Label.inner (fun b => {initial with outer := some true, inner := b}) (some .afterInner)
      (BitMachineBankCodec.parserCfg (K := 3) (some (.scan 0)) none
        (fun _ => []) (B 1) [] []) =
    cfg (some (.inner (.scan 0))) {initial with outer := some true} (outerBank B) := by
  unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg cfg
  congr 1
  have hb : BitMachineStackEmbedding.bank innerSlot (outerBank B)
      (BitMachineBankCodec.contents (fun _ => []) (B 1) [] []) = outerBank B := by
    rw [inner_contents]
    funext j
    fin_cases j <;> simp [outerBank]
  simpa only [BitMachineBankCodec.parserCfg] using hb

theorem inner_end (B : BitMachineBankCodec.Bank 2)
    (C : BitMachineBankCodec.Bank 3) :
    BitMachineStackEmbedding.cfg innerSlot (outerBank B)
      Label.inner (fun b => {initial with outer := some true, inner := b}) (some .afterInner)
      (BitMachineBankCodec.parserCfg (K := 3) none (some true) C [] [] []) =
    cfg (some .afterInner) {initial with outer := some true, inner := some true}
      (innerBank B C) := by
  unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg cfg
  congr 1
  have hb : BitMachineStackEmbedding.bank innerSlot (outerBank B)
      (BitMachineBankCodec.contents C [] [] []) = innerBank B C := by
    rw [inner_contents]
    funext j
    fin_cases j <;> simp [innerBank]
  simpa only [BitMachineBankCodec.parserCfg] using hb

theorem inner_run (B : BitMachineBankCodec.Bank 2)
    (C : BitMachineBankCodec.Bank 3)
    (hd : BitMachineBankCodec.decode 3 (B 1) = some C) :
    ∃ t ≤ 7*((B 1).length+1),
      run t (cfg (some (.inner (.scan 0))) {initial with outer := some true}
        (outerBank B)) =
        cfg (some .afterInner) {initial with outer := some true, inner := some true}
          (innerBank B C) := by
  obtain ⟨t,ht,hp⟩ := BitMachineBankCodec.parser_correct 3 (B 1) []
  rw [hd] at hp
  change BitMachineBankCodec.parserRun t
    (BitMachineBankCodec.parserCfg (some (.scan 0)) none
      (fun _ => []) (B 1) [] []) =
    BitMachineBankCodec.parserCfg none (some true) C [] [] [] at hp
  have hh := congrArg (fun c => c.l) hp
  change _ = none at hh
  obtain ⟨u,hu,hr⟩ := BitMachineStackEmbedding.outputs
    innerSlot (outerBank B) Label.inner
    (fun b => {initial with outer := some true, inner := b}) Control.inner
    (by intro b; rfl) (some .afterInner)
    (BitMachineBankCodec.parser 3) program (by intro l; rfl)
    (BitMachineBankCodec.parserCfg (some (.scan 0)) none
      (fun _ => []) (B 1) [] []) t hh
  refine ⟨u, hu.trans ht, ?_⟩
  change run u _ = _ at hr
  rw [inner_start B] at hr
  unfold BitMachineBankCodec.parserRun at hp
  rw [hp] at hr
  exact hr.trans (inner_end B C)

theorem inner_fail (B : BitMachineBankCodec.Bank 2)
    (hd : BitMachineBankCodec.decode 3 (B 1) = none) :
    ∃ t ≤ 7*((B 1).length+1),
      let c := run t (cfg (some (.inner (.scan 0)))
        {initial with outer := some true} (outerBank B))
      c.l = some .afterInner ∧ c.var.inner = some false ∧ c.stk 11 = [] := by
  obtain ⟨t,ht,hp⟩ := BitMachineBankCodec.parser_correct 3 (B 1) []
  rw [hd] at hp
  obtain ⟨hl,hv,ho⟩ := hp
  obtain ⟨u,hu,hr⟩ := BitMachineStackEmbedding.outputs
    innerSlot (outerBank B) Label.inner
    (fun b => {initial with outer := some true, inner := b}) Control.inner
    (by intro b; rfl) (some .afterInner)
    (BitMachineBankCodec.parser 3) program (by intro l; rfl)
    (BitMachineBankCodec.parserCfg (some (.scan 0)) none
      (fun _ => []) (B 1) [] []) t hl
  refine ⟨u, hu.trans ht, ?_⟩
  dsimp only
  change run u _ = _ at hr
  rw [inner_start B] at hr
  rw [hr]
  have hc : (((advance (BitMachineBankCodec.parser 3))^[t])
      (BitMachineBankCodec.parserCfg (some (.scan 0)) none
        (fun _ => []) (B 1) [] [])).l = none := by
    simpa only [BitMachineBankCodec.parserRun] using hl
  constructor
  · simp [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg, hc]
  constructor
  · simpa [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg] using hv
  · simp only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg]
    have ho11 : ¬ ∃ k, innerSlot k = (11 : Stack) := by
      rintro ⟨k,hk⟩
      cases k with
      | inl k => fin_cases k <;> simp [innerSlot] at hk
      | inr k => fin_cases k <;> simp [innerSlot] at hk
    rw [BitMachineStackEmbedding.bank_outside innerSlot _ _ _ ho11]
    simp [outerBank]

theorem after_outer_step (B : BitMachineBankCodec.Bank 2) :
    advance program
      (cfg (some .afterOuter) {initial with outer := some true} (outerBank B)) =
    cfg (some (.inner (.scan 0))) {initial with outer := some true}
      (outerBank B) := by
  simp [advance, program, TM2.step, TM2.stepAux, cfg, initial]

theorem outer_fail (input : List Bool)
    (hd : BitMachineBankCodec.decode 2 input = none) :
    ∃ t ≤ 5*(input.length+1),
      let c := run t (cfg (some (.outer (.scan 0))) initial (inputBank input))
      c.l = some .afterOuter ∧ c.var.outer = some false ∧ c.stk 11 = [] := by
  obtain ⟨t,ht,hp⟩ := BitMachineBankCodec.parser_correct 2 input []
  rw [hd] at hp
  obtain ⟨hl,hv,ho⟩ := hp
  obtain ⟨u,hu,hr⟩ := BitMachineStackEmbedding.outputs
    outerSlot (inputBank input) Label.outer
    (fun b => {initial with outer := b}) Control.outer
    (by intro b; rfl) (some .afterOuter)
    (BitMachineBankCodec.parser 2) program (by intro l; rfl)
    (BitMachineBankCodec.parserCfg (some (.scan 0)) none
      (fun _ => []) input [] []) t hl
  refine ⟨u, hu.trans ht, ?_⟩
  dsimp only
  change run u _ = _ at hr
  rw [outer_start input] at hr
  rw [hr]
  have hc : (((advance (BitMachineBankCodec.parser 2))^[t])
      (BitMachineBankCodec.parserCfg (some (.scan 0)) none
        (fun _ => []) input [] [])).l = none := by
    simpa only [BitMachineBankCodec.parserRun] using hl
  constructor
  · simp [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg, hc]
  constructor
  · simpa [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg] using hv
  · simp only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg]
    have ho11 : ¬ ∃ k, outerSlot k = (11 : Stack) := by
      rintro ⟨k,hk⟩
      cases k with
      | inl k => fin_cases k <;> simp [outerSlot] at hk
      | inr k => fin_cases k <;> simp [outerSlot] at hk
    rw [BitMachineStackEmbedding.bank_outside outerSlot _ _ _ ho11]
    simp [inputBank]

theorem after_outer_fail (v : Control) (S : Stack → List Bool)
    (h : v.outer = some false) (ho : S 11 = []) :
    let c := advance program (cfg (some .afterOuter) v S)
    c.l = none ∧ c.stk 11 = [] := by
  simp [advance, program, TM2.step, TM2.stepAux, cfg, h, ho]

theorem after_inner_fail (v : Control) (S : Stack → List Bool)
    (h : v.inner = some false) (ho : S 11 = []) :
    let c := advance program (cfg (some .afterInner) v S)
    c.l = none ∧ c.stk 11 = [] := by
  simp [advance, program, TM2.step, TM2.stepAux, cfg, h, ho]

def zeroBank (B : BitMachineBankCodec.Bank 2)
    (C : BitMachineBankCodec.Bank 3) (z : Bool) : Stack → List Bool :=
  fun j => if j = 0 then B 0 else if j = 5 then C 0 else
    if j = 7 then C 2 else if j = 10 then [!z] else []

theorem zero_start (B : BitMachineBankCodec.Bank 2)
    (C : BitMachineBankCodec.Bank 3) :
    BitMachineStackEmbedding.cfg zeroSlot (innerBank B C)
      Label.zero
      (fun b => {initial with outer := some true, inner := some true, zero := b})
      (some .afterZero)
      (CodeDZeroWordV2.cfg (some .scan) CodeDZeroWordV2.initial (C 1) []) =
    cfg (some (.zero .scan))
      {initial with outer := some true, inner := some true} (innerBank B C) := by
  unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg cfg
  congr 1
  apply BitMachineStackEmbedding.bank_eq_self
  intro k
  fin_cases k <;> simp [zeroSlot, CodeDZeroWordV2.cfg, innerBank]

theorem zero_end (B : BitMachineBankCodec.Bank 2)
    (C : BitMachineBankCodec.Bank 3) :
    BitMachineStackEmbedding.cfg zeroSlot (innerBank B C)
      Label.zero
      (fun b => {initial with outer := some true, inner := some true, zero := b})
      (some .afterZero)
      (CodeDZeroWordV2.cfg none ⟨(C 1).any id, none⟩ [] [!(C 1).any id]) =
    cfg (some .afterZero)
      ({initial with outer := some true, inner := some true, zero := ⟨(C 1).any id, none⟩} : Control)
      (zeroBank B C ((C 1).any id)) := by
  unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg cfg
  congr 1
  funext j
  fin_cases j
  all_goals
    first
    | change BitMachineStackEmbedding.bank zeroSlot (innerBank B C)
        (CodeDZeroWordV2.cfg none ⟨(C 1).any id, none⟩ [] [!(C 1).any id]).stk
        (zeroSlot 0) = _
      rw [BitMachineStackEmbedding.bank_at]
      simp [zeroSlot, CodeDZeroWordV2.cfg, zeroBank]
    | change BitMachineStackEmbedding.bank zeroSlot (innerBank B C)
        (CodeDZeroWordV2.cfg none ⟨(C 1).any id, none⟩ [] [!(C 1).any id]).stk
        (zeroSlot 1) = _
      rw [BitMachineStackEmbedding.bank_at]
      simp [zeroSlot, CodeDZeroWordV2.cfg, zeroBank]
    | rw [BitMachineStackEmbedding.bank_outside zeroSlot _ _ _ (by
          rintro ⟨k,hk⟩
          fin_cases k <;> simp [zeroSlot] at hk)]
      simp [zeroBank, innerBank]

theorem zero_run (B : BitMachineBankCodec.Bank 2)
    (C : BitMachineBankCodec.Bank 3) :
    ∃ t ≤ (C 1).length+2,
      run t (cfg (some (.zero .scan))
        {initial with outer := some true, inner := some true} (innerBank B C)) =
      cfg (some .afterZero)
        ({initial with outer := some true, inner := some true, zero := ⟨(C 1).any id, none⟩} : Control)
        (zeroBank B C ((C 1).any id)) := by
  have hp := CodeDZeroWordV2.complete_run (C 1)
  have hh := congrArg (fun c => c.l) hp
  change _ = none at hh
  obtain ⟨u,hu,hr⟩ := BitMachineStackEmbedding.outputs
    zeroSlot (innerBank B C) Label.zero
    (fun b => {initial with outer := some true, inner := some true, zero := b})
    Control.zero (by intro b; rfl) (some .afterZero)
    CodeDZeroWordV2.program program (by intro l; rfl)
    (CodeDZeroWordV2.cfg (some .scan) CodeDZeroWordV2.initial (C 1) [])
    ((C 1).length+2) hh
  refine ⟨u,hu,?_⟩
  change run u _ = _ at hr
  rw [zero_start B C] at hr
  unfold CodeDZeroWordV2.run at hp
  rw [hp] at hr
  exact hr.trans (zero_end B C)

theorem after_inner_nonnegative (B : BitMachineBankCodec.Bank 2)
    (C : BitMachineBankCodec.Bank 3) (hs : C 0 = []) :
    advance program
      (cfg (some .afterInner)
        {initial with outer := some true, inner := some true} (innerBank B C)) =
    cfg (some .afterSign)
      {initial with outer := some true, inner := some true, peeked := none}
      (innerBank B C) := by
  simp [advance, program, TM2.step, TM2.stepAux, cfg, innerBank, hs]

theorem after_inner_negative (B : BitMachineBankCodec.Bank 2)
    (C : BitMachineBankCodec.Bank 3) (hs : C 0 = [true]) :
    advance program
      (cfg (some .afterInner)
        {initial with outer := some true, inner := some true} (innerBank B C)) =
    cfg (some .afterSign)
      {initial with outer := some true, inner := some true, peeked := some true}
      (innerBank B C) := by
  simp [advance, program, TM2.step, TM2.stepAux, cfg, innerBank, hs]

theorem after_inner_nonempty (B : BitMachineBankCodec.Bank 2)
    (C : BitMachineBankCodec.Bank 3) (b : Bool) (rest : List Bool)
    (hs : C 0 = b :: rest) :
    advance program
      (cfg (some .afterInner)
        {initial with outer := some true, inner := some true} (innerBank B C)) =
    cfg (some .afterSign)
      {initial with outer := some true, inner := some true, peeked := some b}
      (innerBank B C) := by
  simp [advance, program, TM2.step, TM2.stepAux, cfg, innerBank, hs]

theorem after_sign_negative (B : BitMachineBankCodec.Bank 2)
    (C : BitMachineBankCodec.Bank 3) :
    let c := advance program
      (cfg (some .afterSign)
        {initial with outer := some true, inner := some true, peeked := some true}
        (innerBank B C))
    c.l = none ∧ c.stk 11 = [] := by
  simp [advance, program, TM2.step, TM2.stepAux, cfg, innerBank]

theorem after_sign_nonempty (B : BitMachineBankCodec.Bank 2)
    (C : BitMachineBankCodec.Bank 3) (b : Bool) :
    let c := advance program
      (cfg (some .afterSign)
        {initial with outer := some true, inner := some true, peeked := some b}
        (innerBank B C))
    c.l = none ∧ c.stk 11 = [] := by
  cases b <;> simp [advance, program, TM2.step, TM2.stepAux, cfg, innerBank]

theorem after_sign_nonnegative (B : BitMachineBankCodec.Bank 2)
    (C : BitMachineBankCodec.Bank 3) :
    advance program
      (cfg (some .afterSign)
        {initial with outer := some true, inner := some true, peeked := none}
        (innerBank B C)) =
    cfg (some (.zero .scan))
      {initial with outer := some true, inner := some true} (innerBank B C) := by
  simp [advance, program, TM2.step, TM2.stepAux, cfg, initial]

theorem after_zero_nonzero (B : BitMachineBankCodec.Bank 2)
    (C : BitMachineBankCodec.Bank 3) (hz : (C 1).any id = true) :
    let c := advance program
      (cfg (some .afterZero)
        ({initial with outer := some true, inner := some true, zero := ⟨(C 1).any id, none⟩} : Control)
        (zeroBank B C ((C 1).any id)))
    c.l = none ∧ c.stk 11 = [true] := by
  simp [advance, program, TM2.step, TM2.stepAux, cfg, zeroBank, hz]

theorem after_zero_zero (B : BitMachineBankCodec.Bank 2)
    (C : BitMachineBankCodec.Bank 3) (hz : (C 1).any id = false) :
    let c := advance program
      (cfg (some .afterZero)
        ({initial with outer := some true, inner := some true, zero := ⟨(C 1).any id, none⟩} : Control)
        (zeroBank B C ((C 1).any id)))
    c.l = none ∧ c.stk 11 = [] := by
  simp [advance, program, TM2.step, TM2.stepAux, cfg, zeroBank, hz]

theorem positive_structural (input : List Bool)
    (B : BitMachineBankCodec.Bank 2) (C : BitMachineBankCodec.Bank 3)
    (hB : BitMachineBankCodec.decode 2 input = some B)
    (hC : BitMachineBankCodec.decode 3 (B 1) = some C)
    (hs : C 0 = []) (hz : (C 1).any id = true) :
    ∃ t ≤ 5*(input.length+1) + 7*((B 1).length+1) + (C 1).length+6,
      let c := run t (cfg (some (.outer (.scan 0))) initial (inputBank input))
      c.l = none ∧ c.stk 11 = [true] := by
  obtain ⟨t₁,ht₁,h₁⟩ := outer_run input B hB
  obtain ⟨t₂,ht₂,h₂⟩ := inner_run B C hC
  obtain ⟨t₃,ht₃,h₃⟩ := zero_run B C
  refine ⟨t₁+1+t₂+1+1+t₃+1, by omega, ?_⟩
  dsimp only
  rw [show t₁+1+t₂+1+1+t₃+1 = t₁+1+t₂+1+1+(t₃+1) by omega]
  simp only [run_add, run_one, h₁, after_outer_step B, h₂,
    after_inner_nonnegative B C hs, after_sign_nonnegative B C, h₃]
  exact after_zero_nonzero B C hz

theorem parsed_structural (input : List Bool)
    (B : BitMachineBankCodec.Bank 2) (C : BitMachineBankCodec.Bank 3)
    (hB : BitMachineBankCodec.decode 2 input = some B)
    (hC : BitMachineBankCodec.decode 3 (B 1) = some C) :
    ∃ t ≤ 5*(input.length+1) + 7*((B 1).length+1) + (C 1).length+6,
      let c := run t (cfg (some (.outer (.scan 0))) initial (inputBank input))
      c.l = none ∧ c.stk 11 =
        (if C 0 = [] && (C 1).any id then [true] else []) := by
  by_cases hs : C 0 = []
  · by_cases hz : (C 1).any id = true
    · obtain ⟨t,ht,h⟩ := positive_structural input B C hB hC hs hz
      refine ⟨t,ht,?_⟩
      simpa [hs,hz] using h
    · have hz' : (C 1).any id = false := by cases h : (C 1).any id <;> simp_all
      obtain ⟨t₁,ht₁,h₁⟩ := outer_run input B hB
      obtain ⟨t₂,ht₂,h₂⟩ := inner_run B C hC
      obtain ⟨t₃,ht₃,h₃⟩ := zero_run B C
      refine ⟨t₁+1+t₂+1+1+t₃+1, by omega, ?_⟩
      dsimp only
      rw [show t₁+1+t₂+1+1+t₃+1 = t₁+1+t₂+1+1+(t₃+1) by omega]
      simp only [run_add, run_one, h₁, after_outer_step B, h₂,
        after_inner_nonnegative B C hs, after_sign_nonnegative B C, h₃]
      simpa [hs,hz'] using after_zero_zero B C hz'
  · cases he : C 0 with
    | nil => exact (hs he).elim
    | cons b rest =>
        obtain ⟨t₁,ht₁,h₁⟩ := outer_run input B hB
        obtain ⟨t₂,ht₂,h₂⟩ := inner_run B C hC
        refine ⟨t₁+1+t₂+1+1, by omega, ?_⟩
        dsimp only
        simp only [run_add, run_one, h₁, after_outer_step B, h₂,
          after_inner_nonempty B C b rest he]
        simpa [hs] using after_sign_nonempty B C b

theorem inner_failed_run (input : List Bool)
    (B : BitMachineBankCodec.Bank 2)
    (hB : BitMachineBankCodec.decode 2 input = some B)
    (hC : BitMachineBankCodec.decode 3 (B 1) = none) :
    ∃ t ≤ 5*(input.length+1) + 7*((B 1).length+1) + 2,
      let c := run t (cfg (some (.outer (.scan 0))) initial (inputBank input))
      c.l = none ∧ c.stk 11 = [] := by
  obtain ⟨t₁,ht₁,h₁⟩ := outer_run input B hB
  obtain ⟨t₂,ht₂,h₂⟩ := inner_fail B hC
  refine ⟨t₁+1+t₂+1, by omega, ?_⟩
  dsimp only
  simp only [run_add, run_one, h₁, after_outer_step B]
  let c := run t₂ (cfg (some (.inner (.scan 0)))
    {initial with outer := some true} (outerBank B))
  have hc : c.l = some .afterInner ∧ c.var.inner = some false ∧ c.stk 11 = [] := h₂
  cases he : c with
  | mk l v S =>
      change run t₂ (cfg (some (.inner (.scan 0)))
        {initial with outer := some true} (outerBank B)) = ⟨l,v,S⟩ at he
      dsimp only [c] at hc
      rw [he] at hc ⊢
      have hl : l = some .afterInner := hc.1
      have hv : v.inner = some false := hc.2.1
      have ho : S 11 = [] := hc.2.2
      subst l
      change (advance program (cfg (some .afterInner) v S)).l = none ∧
        (advance program (cfg (some .afterInner) v S)).stk 11 = []
      exact after_inner_fail v S hv ho

theorem outer_failed_run (input : List Bool)
    (hB : BitMachineBankCodec.decode 2 input = none) :
    ∃ t ≤ 5*(input.length+1)+1,
      let c := run t (cfg (some (.outer (.scan 0))) initial (inputBank input))
      c.l = none ∧ c.stk 11 = [] := by
  obtain ⟨t,ht,h⟩ := outer_fail input hB
  refine ⟨t+1, by omega, ?_⟩
  dsimp only
  rw [run_add, run_one]
  let c := run t (cfg (some (.outer (.scan 0))) initial (inputBank input))
  have hc : c.l = some .afterOuter ∧ c.var.outer = some false ∧ c.stk 11 = [] := h
  cases he : c with
  | mk l v S =>
      change run t (cfg (some (.outer (.scan 0))) initial (inputBank input)) =
        ⟨l,v,S⟩ at he
      dsimp only [c] at hc
      rw [he] at hc ⊢
      have hl : l = some .afterOuter := hc.1
      have hv : v.outer = some false := hc.2.1
      have ho : S 11 = [] := hc.2.2
      subst l
      change (advance program (cfg (some .afterOuter) v S)).l = none ∧
        (advance program (cfg (some .afterOuter) v S)).stk 11 = []
      exact after_outer_fail v S hv ho

theorem raw_run (input : List Bool) :
    ∃ t ≤ 50*(input.length+1),
      let c := run t (cfg (some (.outer (.scan 0))) initial (inputBank input))
      c.l = none ∧ c.stk 11 = result input := by
  cases hB : BitMachineBankCodec.decode 2 input with
  | none =>
      obtain ⟨t,ht,h⟩ := outer_failed_run input hB
      refine ⟨t, by omega, ?_⟩
      simpa [result, hB] using h
  | some B =>
      have hBlen : (B 1).length ≤ input.length := by
        calc
          (B 1).length ≤ (BitMachineBankCodec.encode B).length :=
            BitMachineBankCodec.word_length_le_encode B 1
          _ = input.length := congrArg List.length
            (BitMachineBankCodec.encode_decode hB)
      cases hC : BitMachineBankCodec.decode 3 (B 1) with
      | none =>
          obtain ⟨t,ht,h⟩ := inner_failed_run input B hB hC
          refine ⟨t, by omega, ?_⟩
          simpa [result, hB, hC] using h
      | some C =>
          have hClen : (C 1).length ≤ (B 1).length := by
            calc
              (C 1).length ≤ (BitMachineBankCodec.encode C).length :=
                BitMachineBankCodec.word_length_le_encode C 1
              _ = (B 1).length := congrArg List.length
                (BitMachineBankCodec.encode_decode hC)
          obtain ⟨t,ht,h⟩ := parsed_structural input B C hB hC
          refine ⟨t, by omega, ?_⟩
          simpa [result, hB, hC] using h

theorem outputs (input : List Bool) :
    machine.OutputsWithin input (result input) (50*(input.length+1)) := by
  obtain ⟨t,ht,hh⟩ := raw_run input
  have hi : BitMachineEncoding.rawInit (2 : Stack) (.outer (.scan 0)) initial input =
      cfg (some (.outer (.scan 0))) initial (inputBank input) := by
    rfl
  apply BitMachineEncoding.outputsWithin_of_raw_run
    (2 : Stack) 11 (.outer (.scan 0)) initial program
    input (result input) t (50*(input.length+1)) ht
  · rw [hi]
    exact hh.1
  · rw [hi]
    exact hh.2

theorem result_pair (weight coeff : CodeDCodec.RawRat) :
    result (CodeDPairProductTargetV2.pairBytes weight coeff) =
      if !coeff.negative && coeff.numerator.any id then [true] else [] := by
  simp [result, CodeDPairProductTargetV2.pairBytes,
    CodeDPairProductTargetV2.pairBank, CodeDCodec.encodeRawRat,
    CodeDCodec.rawRatBank, BitMachineBankCodec.decode_encode]

theorem coeff_positive_iff (coeff : CodeDCodec.RawRat)
    (hc : coeff.Valid) :
    (0 < coeff.value) ↔
      (!coeff.negative && coeff.numerator.any id) = true := by
  obtain ⟨sg,num,den⟩ := coeff
  have hd : 0 < BitMachineBinaryMultiply.msbValue den := hc
  have hdq : (0 : ℚ) < (BitMachineBinaryMultiply.msbValue den : ℚ) := by
    exact_mod_cast hd
  by_cases hn : EncodedCommunication.bitsValue num = 0
  · have hb : num.any id = false :=
      (BitMachineBinaryZeroTest.any_false_iff_value_zero num).2 hn
    cases sg <;> simp [CodeDCodec.RawRat.value, hn, hb]
  · have hnp : 0 < EncodedCommunication.bitsValue num := Nat.pos_of_ne_zero hn
    have hnq : (0 : ℚ) < (EncodedCommunication.bitsValue num : ℚ) := by
      exact_mod_cast hnp
    have hdiv : (0 : ℚ) <
        (EncodedCommunication.bitsValue num : ℚ) /
          (BitMachineBinaryMultiply.msbValue den : ℚ) := div_pos hnq hdq
    have hb : num.any id = true := by
      cases h : num.any id with
      | false => exact (hn ((BitMachineBinaryZeroTest.any_false_iff_value_zero num).1 h)).elim
      | true => rfl
    cases sg <;> simp [CodeDCodec.RawRat.value, hb, hdiv, le_of_lt hdiv]

theorem result_pair_positive (weight coeff : CodeDCodec.RawRat)
    (hc : coeff.Valid) :
    result (CodeDPairProductTargetV2.pairBytes weight coeff) =
      if 0 < coeff.value then [true] else [] := by
  rw [result_pair]
  by_cases hp : 0 < coeff.value
  · rw [if_pos hp]
    rw [(coeff_positive_iff coeff hc).1 hp]
    rfl
  · rw [if_neg hp]
    have hb : (!coeff.negative && coeff.numerator.any id) = false := by
      cases h : (!coeff.negative && coeff.numerator.any id) with
      | false => rfl
      | true => exact (hp ((coeff_positive_iff coeff hc).2 h)).elim
    rw [hb]
    rfl

#print axioms outputs
#print axioms result_pair
#print axioms result_pair_positive

end CurrentAdditive.MinimumRatioPositiveRun
