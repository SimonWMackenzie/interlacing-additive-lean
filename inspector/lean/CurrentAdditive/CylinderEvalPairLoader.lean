import CurrentAdditive.CylinderFeatureCodec
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-! Physical parsing of one contextual cylinder pair. Three literal bank
parsers read the input and its two nested Bank2 records. No decoded bank is
installed as an initial state without running those parsers. -/

namespace CurrentAdditive.CylinderEvalPairLoader

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineBankCodec

abbrev Stack := Fin 12

inductive Phase where
  | outer | context | pair
  deriving DecidableEq,Fintype

inductive Label where
  | parse (phase : Phase) (label : ParserLabel 2)
  | after (phase : Phase)
  deriving DecidableEq,Fintype

def parseStack : Phase → (BitMachineBankCodec.Stack 2 ↪ Stack)
  | .outer => {
      toFun := Sum.elim (fun k => ![3,4] k) (fun k => ![0,1,2] k)
      inj' := by intro a b h; cases a with
        | inl a => cases b with
          | inl b => fin_cases a <;> fin_cases b <;> simp_all
          | inr b => fin_cases a <;> fin_cases b <;> simp_all
        | inr a => cases b with
          | inl b => fin_cases a <;> fin_cases b <;> simp_all
          | inr b => fin_cases a <;> fin_cases b <;> simp_all }
  | .context => {
      toFun := Sum.elim (fun k => ![5,6] k) (fun k => ![3,1,2] k)
      inj' := by intro a b h; cases a with
        | inl a => cases b with
          | inl b => fin_cases a <;> fin_cases b <;> simp_all
          | inr b => fin_cases a <;> fin_cases b <;> simp_all
        | inr a => cases b with
          | inl b => fin_cases a <;> fin_cases b <;> simp_all
          | inr b => fin_cases a <;> fin_cases b <;> simp_all }
  | .pair => {
      toFun := Sum.elim (fun k => ![7,8] k) (fun k => ![4,1,2] k)
      inj' := by intro a b h; cases a with
        | inl a => cases b with
          | inl b => fin_cases a <;> fin_cases b <;> simp_all
          | inr b => fin_cases a <;> fin_cases b <;> simp_all
        | inr a => cases b with
          | inl b => fin_cases a <;> fin_cases b <;> simp_all
          | inr b => fin_cases a <;> fin_cases b <;> simp_all }

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .parse phase label => BitMachineStackEmbedding.stmt (parseStack phase)
      (.parse phase) id id (some (.after phase)) (parser 2 label)
  | .after .outer => .load (fun _ => none) (.goto (fun _ => .parse .context (.scan 0)))
  | .after .context => .load (fun _ => none) (.goto (fun _ => .parse .pair (.scan 0)))
  | .after .pair => .halt

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label (Option Bool)

def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

noncomputable def frame (phase : Phase) (foreign : Stack → List Bool)
    (c : TM2.Cfg (fun _ : BitMachineBankCodec.Stack 2 => Bool) (ParserLabel 2) (Option Bool)) : Config :=
  BitMachineStackEmbedding.cfg (parseStack phase) foreign (.parse phase) id
    (some (.after phase)) c

theorem parser_run (phase : Phase) (foreign : Stack → List Bool)
    (words : BitMachineBankCodec.Bank 2) :
    ∃ t ≤ 5*((encode words).length+1),
      run t (frame phase foreign
        (parserCfg (some (.scan 0)) none (fun _ => []) (encode words) [] [])) =
      frame phase foreign (parserCfg none (some true) words [] [] []) := by
  obtain ⟨t,ht,hr⟩ := parser_correct 2 (encode words) []
  rw [decode_encode] at hr
  change BitMachineBankCodec.parserRun t
    (parserCfg (some (.scan 0)) none (fun _ => []) (encode words) [] []) =
    parserCfg none (some true) words [] [] [] at hr
  have hh : (BitMachineBankCodec.parserRun t
      (parserCfg (K:=2) (some (.scan 0)) none (fun _ => []) (encode words) [] [])).l=none := by
    rw [hr]; rfl
  obtain ⟨u,hu,he⟩ := BitMachineStackEmbedding.outputs (parseStack phase) foreign
    (.parse phase) id id (by intro v; rfl) (some (.after phase))
    (parser 2) program (by intro l; rfl)
    (parserCfg (some (.scan 0)) none (fun _ => []) (encode words) [] []) t hh
  change run u (frame phase foreign _) = frame phase foreign
    (BitMachineBankCodec.parserRun t _) at he
  rw [hr] at he
  exact ⟨u,hu.trans ht,he⟩

def input (q tuple coordinate symbol : List Bool) : List Bool :=
  encode ![encode ![q,tuple],encode ![coordinate,symbol]]

def loaded (q tuple coordinate symbol : List Bool) : Stack → List Bool :=
  fun k => if k=5 then q else if k=6 then tuple else if k=7 then coordinate
    else if k=8 then symbol else []

def words (phase : Phase) (q tuple coordinate symbol : List Bool) : Bank 2 :=
  match phase with
  | .outer => ![encode ![q,tuple],encode ![coordinate,symbol]]
  | .context => ![q,tuple]
  | .pair => ![coordinate,symbol]

def stage (p : Phase) (q tuple coordinate symbol : List Bool) : Stack → List Bool :=
  match p with
  | .outer => fun k => if k=0 then input q tuple coordinate symbol else []
  | .context => fun k => if k=3 then encode ![q,tuple]
      else if k=4 then encode ![coordinate,symbol] else []
  | .pair => fun k => if k=4 then encode ![coordinate,symbol]
      else if k=5 then q else if k=6 then tuple else []

def nextStage (p : Phase) (q tuple coordinate symbol : List Bool) : Stack → List Bool :=
  match p with
  | .outer => stage .context q tuple coordinate symbol
  | .context => stage .pair q tuple coordinate symbol
  | .pair => loaded q tuple coordinate symbol

private theorem bank_eq {K J : Type} [DecidableEq K] [DecidableEq J]
    (e : K ↪ J) (S : J → List Bool) (T : K → List Bool) (U : J → List Bool)
    (hin : ∀ k,U (e k)=T k) (hout : ∀ j, (¬∃ k,e k=j) → U j=S j) :
    BitMachineStackEmbedding.bank e S T=U := by
  classical
  funext j
  by_cases h : ∃ k,e k=j
  · obtain ⟨k,rfl⟩ := h
    rw [BitMachineStackEmbedding.bank_at]
    exact (hin k).symm
  · rw [BitMachineStackEmbedding.bank_outside _ _ _ _ h]
    exact (hout j h).symm

theorem frame_initial (p : Phase) (q tuple coordinate symbol : List Bool) :
    frame p (stage p q tuple coordinate symbol)
      (parserCfg (some (.scan 0)) none (fun _ => [])
        (encode (words p q tuple coordinate symbol)) [] []) =
      ⟨some (.parse p (.scan 0)),none,stage p q tuple coordinate symbol⟩ := by
  unfold frame BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg
  congr 1
  apply BitMachineStackEmbedding.bank_eq_self
  intro k
  cases p <;> cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

theorem frame_final (p : Phase) (q tuple coordinate symbol : List Bool) :
    frame p (stage p q tuple coordinate symbol)
      (parserCfg none (some true) (words p q tuple coordinate symbol) [] [] []) =
      ⟨some (.after p),some true,nextStage p q tuple coordinate symbol⟩ := by
  unfold frame BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg
  congr 1
  apply bank_eq
  · intro k
    cases p <;> cases k with
    | inl k => fin_cases k <;> rfl
    | inr k => fin_cases k <;> rfl
  · intro k hk
    cases p <;> fin_cases k
    all_goals first
      | rfl
      | exact (hk ⟨Sum.inl (0 : Fin 2),rfl⟩).elim
      | exact (hk ⟨Sum.inl (1 : Fin 2),rfl⟩).elim
      | exact (hk ⟨Sum.inr (0 : Fin 3),rfl⟩).elim
      | exact (hk ⟨Sum.inr (1 : Fin 3),rfl⟩).elim
      | exact (hk ⟨Sum.inr (2 : Fin 3),rfl⟩).elim

theorem phase_run (p : Phase) (q tuple coordinate symbol : List Bool) :
    ∃ t ≤ 5*((encode (words p q tuple coordinate symbol)).length+1),
      run t ⟨some (.parse p (.scan 0)),none,stage p q tuple coordinate symbol⟩ =
      ⟨some (.after p),some true,nextStage p q tuple coordinate symbol⟩ := by
  obtain ⟨t,ht,hr⟩ := parser_run p (stage p q tuple coordinate symbol)
    (words p q tuple coordinate symbol)
  rw [frame_initial,frame_final] at hr
  exact ⟨t,ht,hr⟩

theorem run_add {c c' : Config} {n : ℕ} (h : run n c=c') (m : ℕ) :
    run (n+m) c=run m c' := by
  rw [Nat.add_comm,run,Function.iterate_add_apply]
  exact congrArg (run m) h

theorem after_outer (q tuple coordinate symbol : List Bool) :
    run 1 ⟨some (.after .outer),some true,nextStage .outer q tuple coordinate symbol⟩ =
      ⟨some (.parse .context (.scan 0)),none,stage .context q tuple coordinate symbol⟩ := rfl

theorem after_context (q tuple coordinate symbol : List Bool) :
    run 1 ⟨some (.after .context),some true,nextStage .context q tuple coordinate symbol⟩ =
      ⟨some (.parse .pair (.scan 0)),none,stage .pair q tuple coordinate symbol⟩ := rfl

theorem loaded_run (q tuple coordinate symbol : List Bool) :
    ∃ t ≤ 18*((input q tuple coordinate symbol).length+1),
      run t ⟨some (.parse .outer (.scan 0)),none,stage .outer q tuple coordinate symbol⟩ =
      ⟨none,some true,loaded q tuple coordinate symbol⟩ := by
  obtain ⟨a,ha,hA⟩ := phase_run .outer q tuple coordinate symbol
  obtain ⟨b,hb,hB⟩ := phase_run .context q tuple coordinate symbol
  obtain ⟨c,hc,hC⟩ := phase_run .pair q tuple coordinate symbol
  have h1 := (run_add hA 1).trans (after_outer q tuple coordinate symbol)
  have h2 := (run_add h1 b).trans hB
  have h3 := (run_add h2 1).trans (after_context q tuple coordinate symbol)
  have h4 := (run_add h3 c).trans hC
  have hd : run 1 ⟨some (.after .pair),some true,nextStage .pair q tuple coordinate symbol⟩ =
      ⟨none,some true,loaded q tuple coordinate symbol⟩ := rfl
  have hctx := word_length_le_encode (words .outer q tuple coordinate symbol) (0 : Fin 2)
  have hpair := word_length_le_encode (words .outer q tuple coordinate symbol) (1 : Fin 2)
  refine ⟨a+1+b+1+c+1,?_,(run_add h4 1).trans hd⟩
  change (encode ![q,tuple]).length ≤ (input q tuple coordinate symbol).length at hctx
  change (encode ![coordinate,symbol]).length ≤ (input q tuple coordinate symbol).length at hpair
  change a ≤ 5*((input q tuple coordinate symbol).length+1) at ha
  change b ≤ 5*((encode ![q,tuple]).length+1) at hb
  change c ≤ 5*((encode ![coordinate,symbol]).length+1) at hc
  omega

end CurrentAdditive.CylinderEvalPairLoader

#print axioms CurrentAdditive.CylinderEvalPairLoader.parser_run
#print axioms CurrentAdditive.CylinderEvalPairLoader.loaded_run
