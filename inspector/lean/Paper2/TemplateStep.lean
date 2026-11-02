import Paper2.NavJoin
import Paper2.RequestSelectActual
import Paper2.TemplateLookup
import Paper2.LocateUniform
import Paper2.RawRowSplit

/-! Unit 3, segment (2): ONE bank and ONE fixed program for one level of
`RecursiveEntries.request` (level `k+1 → k`), template case, with the
raw-row sum-bit dispatch.

Program `step Src` (sequenced by the production `BitMachineRawSequence`):
1. `NavJoin.program` (segment 1) through `iN`: the level-`k` sub-codes
   `E_k, G_k, col_k, row_k, copies (s+1) col_k, outerCode col_k,
   append (ticket q₁) row_k` from the serialized `row_{k+1}`, `col_{k+1}`;
2. `RequestSelect.program` (frozen) through `i1`, whose `E`/`G` cells ARE the
   join's cells 2/3: the tagged column word `(x y.1).2` and the raw-row word
   `y.2 (x y.1).1`;
3. `TagDispatch.ifProgram` (frozen) on the raw-row cell: pops the sum bit;
   bit `false` (template) runs `arm`, bit `true` (source) runs `Src` (the
   source-case program of segment 3, a parameter here);
4. `arm`: `RawRowSplit.readU` (frozen; unary outer index `p` into cell `pc`,
   template word left in the raw-row cell), `LocateUniform.program` (frozen)
   through `eL` (tagged word, `copies (s+1) col_k` = join cell 6,
   `outerCode col_k` = join cell 7, blank `my`, index `pc`), then
   `RequestSelect.program` again through `i2` = `TemplateLookup`, whose
   `X` is the raw-row cell (template word), `Y` the locate label cell (outer
   word), `E` join cell 8, `G` join cell 4.

Every handoff is a charged `BitMachineRawSequence` / `ifProgram` step; every
input except the level-`k+1` words and codes is produced inside. -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.TemplateStep

noncomputable section

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open GeneratorCode GeneratorSerialization GeneratorSource
open RecursiveLabelCodecScratch RecursiveEntries
open BitMachineRawSequence (leftLabel)

abbrev RS := RequestSelect.Stack
/-- The ambient bank: join bank, two `RequestSelect` banks, the locate fetch
scratch, and two single cells (`pc`, `my`). -/
abbrev J := NavJoin.Stack ⊕ (RS ⊕ (RS ⊕ (FetchLabel.Stack ⊕ Fin 2)))

def nC (i : Fin 9) : J := .inl (.inr i)
def r1 (x : RS) : J := .inr (.inl x)
def r2 (x : RS) : J := .inr (.inr (.inl x))
def lC (j : FetchLabel.Stack) : J := .inr (.inr (.inr (.inl j)))
def pcC : J := .inr (.inr (.inr (.inr 0)))
def myJ : J := .inr (.inr (.inr (.inr 1)))

/-! ### Embeddings -/

def iN : NavJoin.Stack ↪ J := ⟨Sum.inl, Sum.inl_injective⟩

def i1Fun : RS → J
  | .inl j => r1 (.inl j)
  | .inr (.inl j) => r1 (.inr (.inl j))
  | .inr (.inr q) => (![r1 RequestSelect.Xc, r1 RequestSelect.Yc, nC 2, nC 3,
      r1 RequestSelect.jc, r1 RequestSelect.remc, r1 RequestSelect.ic,
      r1 RequestSelect.sc] : Fin 8 → J) q

theorem i1Fun_injective : Function.Injective i1Fun := by
  intro a b h
  rcases a with a | a | a <;> rcases b with b | b | b
  · simpa [i1Fun, r1] using h
  · simp [i1Fun, r1] at h
  · fin_cases b <;> simp [i1Fun, r1, nC, RequestSelect.Xc, RequestSelect.Yc,
      RequestSelect.jc, RequestSelect.remc, RequestSelect.ic, RequestSelect.sc] at h
  · simp [i1Fun, r1] at h
  · simpa [i1Fun, r1] using h
  · fin_cases b <;> simp [i1Fun, r1, nC, RequestSelect.Xc, RequestSelect.Yc,
      RequestSelect.jc, RequestSelect.remc, RequestSelect.ic, RequestSelect.sc] at h
  · fin_cases a <;> simp [i1Fun, r1, nC, RequestSelect.Xc, RequestSelect.Yc,
      RequestSelect.jc, RequestSelect.remc, RequestSelect.ic, RequestSelect.sc] at h
  · fin_cases a <;> simp [i1Fun, r1, nC, RequestSelect.Xc, RequestSelect.Yc,
      RequestSelect.jc, RequestSelect.remc, RequestSelect.ic, RequestSelect.sc] at h
  · fin_cases a <;> fin_cases b <;> simp_all [i1Fun, r1, nC, RequestSelect.Xc,
      RequestSelect.Yc, RequestSelect.jc, RequestSelect.remc, RequestSelect.ic,
      RequestSelect.sc]

def i1 : RS ↪ J := ⟨i1Fun, i1Fun_injective⟩

def eLFun : FetchIndexed.Stack → J
  | .inl j => lC j
  | .inr q => (![r1 RequestSelect.tagC, nC 6, nC 7, myJ, pcC] : Fin 5 → J) q

theorem eLFun_injective : Function.Injective eLFun := by
  intro a b h
  rcases a with a | a <;> rcases b with b | b
  · simpa [eLFun, lC] using h
  · fin_cases b <;> simp [eLFun, lC, r1, nC, myJ, pcC, RequestSelect.tagC] at h
  · fin_cases a <;> simp [eLFun, lC, r1, nC, myJ, pcC, RequestSelect.tagC] at h
  · fin_cases a <;> fin_cases b <;> simp_all [eLFun, r1, nC, myJ, pcC,
      RequestSelect.tagC]

def eL : FetchIndexed.Stack ↪ J := ⟨eLFun, eLFun_injective⟩

def i2Fun : RS → J
  | .inl j => r2 (.inl j)
  | .inr (.inl j) => r2 (.inr (.inl j))
  | .inr (.inr q) => (![r1 RequestSelect.rowC, lC FetchLabel.lblC, nC 8, nC 4,
      r2 RequestSelect.jc, r2 RequestSelect.remc, r2 RequestSelect.ic,
      r2 RequestSelect.sc] : Fin 8 → J) q

theorem i2Fun_injective : Function.Injective i2Fun := by
  intro a b h
  rcases a with a | a | a <;> rcases b with b | b | b
  · simpa [i2Fun, r2] using h
  · simp [i2Fun, r2] at h
  · fin_cases b <;> simp [i2Fun, r1, r2, lC, nC, RequestSelect.rowC, RequestSelect.jc,
      RequestSelect.remc, RequestSelect.ic, RequestSelect.sc] at h
  · simp [i2Fun, r2] at h
  · simpa [i2Fun, r2] using h
  · fin_cases b <;> simp [i2Fun, r1, r2, lC, nC, RequestSelect.rowC, RequestSelect.jc,
      RequestSelect.remc, RequestSelect.ic, RequestSelect.sc] at h
  · fin_cases a <;> simp [i2Fun, r1, r2, lC, nC, RequestSelect.rowC, RequestSelect.jc,
      RequestSelect.remc, RequestSelect.ic, RequestSelect.sc] at h
  · fin_cases a <;> simp [i2Fun, r1, r2, lC, nC, RequestSelect.rowC, RequestSelect.jc,
      RequestSelect.remc, RequestSelect.ic, RequestSelect.sc] at h
  · fin_cases a <;> fin_cases b <;> simp_all [i2Fun, r1, r2, lC, nC, RequestSelect.rowC,
      RequestSelect.jc, RequestSelect.remc, RequestSelect.ic, RequestSelect.sc]

def i2 : RS ↪ J := ⟨i2Fun, i2Fun_injective⟩

/-! ### Generic transport and bank algebra -/

theorem lift {K L V : Type*} [DecidableEq K] (ι : K ↪ J)
    (P : L → TM2.Stmt (fun _ : K => Bool) L V)
    (W : J → List Bool) (S T : K → List Bool) (hS : ∀ k, S k = W (ι k)) (l : L) (v v' : V)
    (t : ℕ)
    (hrun : ((advance P)^[t]) (⟨some l, v, S⟩ : TM2.Cfg (fun _ : K => Bool) L V) =
      ⟨none, v', T⟩) :
    ((advance (fun l => stackStmt ι (P l)))^[t])
        (⟨some l, v, W⟩ : TM2.Cfg (fun _ : J => Bool) L V) =
      ⟨none, v', bank ι W T⟩ := by
  have hs := BitMachineStackRun.run ι W P (⟨some l, v, S⟩ : TM2.Cfg (fun _ : K => Bool) L V) t
  rw [hrun] at hs
  simp only [stackCfg] at hs
  rwa [bank_eq_self ι W S hS] at hs

theorem mk_updates (a b X Y E G jw R iw : List Bool) :
    RequestSelect.mk a b (RequestSelect.vec X Y E G jw R iw) =
      Function.update (Function.update (Function.update (Function.update (Function.update
        (RequestSelect.mk [] [] (RequestSelect.vec X Y E G [] [] [])) RequestSelect.tagC a)
        RequestSelect.rowC b) RequestSelect.jc jw) RequestSelect.remc R) RequestSelect.ic iw := by
  rw [show RequestSelect.tagC = .inl FetchLabel.lblC from rfl, RequestSelect.upd_A,
    show RequestSelect.rowC = .inr (.inl FetchLabel.lblC) from rfl, RequestSelect.upd_B,
    show RequestSelect.jc = .inr (.inr 4) from rfl, RequestSelect.upd_vec,
    show RequestSelect.remc = .inr (.inr 5) from rfl, RequestSelect.upd_vec,
    show RequestSelect.ic = .inr (.inr 6) from rfl, RequestSelect.upd_vec]
  congr 1
  funext q; fin_cases q <;> rfl

theorem bank_mk (ι : RS ↪ J) (W : J → List Bool) (X Y E G : List Bool)
    (hS : ∀ k, RequestSelect.mk [] [] (RequestSelect.vec X Y E G [] [] []) k = W (ι k))
    (a b jw R iw : List Bool) :
    bank ι W (RequestSelect.mk a b (RequestSelect.vec X Y E G jw R iw)) =
      Function.update (Function.update (Function.update (Function.update (Function.update W
        (ι RequestSelect.tagC) a) (ι RequestSelect.rowC) b) (ι RequestSelect.jc) jw)
        (ι RequestSelect.remc) R) (ι RequestSelect.ic) iw := by
  rw [mk_updates, bank_update, bank_update, bank_update, bank_update, bank_update,
    bank_eq_self ι W _ hS]

theorem bank_iN_inl (W : J → List Bool) (T : NavJoin.Stack → List Bool) (y : NavJoin.Stack) :
    bank iN W T (.inl y) = T y := bank_at iN W T y

theorem bank_iN_inr (W : J → List Bool) (T : NavJoin.Stack → List Bool)
    (x : RS ⊕ (RS ⊕ (FetchLabel.Stack ⊕ Fin 2))) :
    bank iN W T (.inr x) = W (.inr x) :=
  bank_outside iN W T _ (by rintro ⟨k, hk⟩; exact Sum.inl_ne_inr hk)

/-! ### Cell values of the embeddings (all `rfl`) -/

theorem eL_inl (j : FetchLabel.Stack) : eL (.inl j) = lC j := rfl
theorem eL_fw : eL FetchIndexed.fwC = r1 RequestSelect.tagC := rfl
theorem eL_cc : eL FetchIndexed.ccC = nC 6 := rfl
theorem eL_rc : eL FetchIndexed.rcC = nC 7 := rfl
theorem eL_my : eL FetchIndexed.myC = myJ := rfl
theorem eL_idx : eL FetchIndexed.idxC = pcC := rfl
theorem eL_lbl : eL SuccessFetchJoin.lblF = lC FetchLabel.lblC := rfl
theorem i1_tag : i1 RequestSelect.tagC = r1 RequestSelect.tagC := rfl
theorem i1_row : i1 RequestSelect.rowC = r1 RequestSelect.rowC := rfl
theorem i1_j : i1 RequestSelect.jc = r1 RequestSelect.jc := rfl
theorem i1_rem : i1 RequestSelect.remc = r1 RequestSelect.remc := rfl
theorem i1_i : i1 RequestSelect.ic = r1 RequestSelect.ic := rfl
theorem i2_tag : i2 RequestSelect.tagC = r2 RequestSelect.tagC := rfl
theorem i2_row : i2 RequestSelect.rowC = r2 RequestSelect.rowC := rfl

/-! ### Programs -/

def srcCell : J := r1 RequestSelect.rowC

def navP := fun l => stackStmt iN (NavJoin.program l)
def rs1 := fun l => stackStmt i1 (RequestSelect.program l)
def rs2 := fun l => stackStmt i2 (RequestSelect.program l)

def armA := BitMachineRawSequence.program (RawRowSplit.readU srcCell pcC)
  (LocateUniform.program eL) (.inl ()) (none : Option Bool) LocateUniform.startControl
/-- The template arm. -/
def arm := BitMachineRawSequence.program armA rs2 RequestSelect.startLabel
  ((none : Option Bool), LocateUniform.startControl) RequestSelect.startControl
def armStart := ChildNav.labelOf arm (leftLabel (leftLabel ()))
def armCtl := (((none : Option Bool), LocateUniform.startControl), RequestSelect.startControl)

def pre := BitMachineRawSequence.program navP rs1 RequestSelect.startLabel NavJoin.ctl
  RequestSelect.startControl

/-- One request level; `Src` is the source-case arm (segment 3). -/
def step {LS VS : Type*} (Src : LS → TM2.Stmt (fun _ : J => Bool) LS VS) (srcStart : LS)
    (srcCtl : VS) :=
  BitMachineRawSequence.program pre
    (TagDispatch.ifProgram srcCell arm Src armStart srcStart armCtl srcCtl) (.inl ())
    (NavJoin.ctl, RequestSelect.startControl) ((none : Option Bool), (armCtl, srcCtl))

def stepCtl {VS : Type*} (srcCtl : VS) :=
  ((NavJoin.ctl, RequestSelect.startControl), ((none : Option Bool), (armCtl, srcCtl)))

/-! ### The template arm on an arbitrary bank satisfying its precondition -/

variable {n p s q₁ q₂ w Q : ℕ} [NeZero n] [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q]

theorem arm_run (hp : 0 < p) (hs : 4 ≤ s) (k : ℕ)
    (zt : SourceMatrix.TaggedColumn q₁ q₂ s
      (Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k))
    (ξ₀ : SourceMatrix.Tail s
      (Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k))
    (pp : Fin s)
    (z : SourceMatrix.Template q₁ q₂
      (Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k))
    (S : J → List Bool)
    (hsrc : S srcCell = List.replicate pp.val true ++ false ::
      (piCodec (prodCodec (finCodec q₁) (defaultCarrierCodecs n p s q₁ q₂ w Q k).1) q₂).encode z)
    (hpc : S pcC = []) (hL : ∀ j, S (lC j) = []) (hmy : S myJ = [])
    (htag : S (r1 RequestSelect.tagC) =
      (taggedColumnCodec q₁ q₂ s (defaultCarrierCodecs n p s q₁ q₂ w Q k).2).encode zt)
    (hcps : S (nC 6) = encodeCode (copies (s + 1) (seedRecursiveCodes n p s q₁ q₂ w Q k).2))
    (hout : S (nC 7) = encodeCode (outerCode q₁ q₂ s (seedRecursiveCodes n p s q₁ q₂ w Q k).2))
    (hte : S (nC 8) = encodeCode (.append (.ticket q₁) (seedRecursiveCodes n p s q₁ q₂ w Q k).1))
    (hcol : S (nC 4) = encodeCode (seedRecursiveCodes n p s q₁ q₂ w Q k).2)
    (hr2 : ∀ x, S (r2 x) = []) :
    let C := defaultCarrierCodecs n p s q₁ q₂ w Q k
    let c := seedRecursiveCodes n p s q₁ q₂ w Q k
    let o := (SourceMatrix.forgetTag ξ₀ zt).2 pp
    let TW := (piCodec (prodCodec (finCodec q₁) C.1) q₂).encode z
    let OW := (outerColumnCodec q₁ q₂ s C.2).encode o
    let S1 := Function.update (Function.update S srcCell TW) pcC (List.replicate pp.val true)
    ∃ t ≤ (pp.val + 1) + LocateUniform.locBound q₁ q₂ s C.2 c.2 pp.val zt + 1 +
        RequestSelect.clock OW o.1.val (z o.1).1.val (.append (.ticket q₁) c.1) c.2
          (List.ofFn (fun a => (prodCodec (finCodec q₁) C.1).encode (z a)))
          (List.ofFn (fun b => C.2.encode (o.2 b))) + 1,
      ∃ v, ∃ F : J → List Bool,
      ((advance arm)^[t]) (⟨some armStart, armCtl, S⟩ : TM2.Cfg (fun _ : J => Bool) _ _) =
        ⟨none, v, bank i2 F (RequestSelect.mk (C.1.encode (z o.1).2)
          (C.2.encode (SourceMatrix.head o.2 (z o.1).1))
          (RequestSelect.vec TW OW (encodeCode (.append (.ticket q₁) c.1)) (encodeCode c.2)
            (List.replicate o.1.val true) ((piCodec C.2 (q₁ + s + 1)).encode o.2)
            (List.replicate (z o.1).1.val true)))⟩ ∧
      LocateUniform.Frame eL S1 F ∧ F (lC FetchLabel.lblC) = OW := by
  intro C c o TW OW S1
  have hne : srcCell ≠ pcC := by simp [srcCell, pcC, r1]
  have r0 := RawRowSplit.readU_run srcCell pcC hne pp.val TW [] S none hsrc hpc
  rw [List.append_nil] at r0
  have h1 : ∀ x, x ≠ srcCell → x ≠ pcC → S1 x = S x := by
    intro x hx1 hx2
    simp only [S1]
    rw [Function.update_of_ne hx2, Function.update_of_ne hx1]
  obtain ⟨tL, htL, vL, F, pL, hFl, hFr⟩ := LocateUniform.locate_run (n := n) (p := p)
    (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) hp hs k zt ξ₀ pp eL S1
    (fun j => by rw [eL_inl, h1 _ (by simp [lC, srcCell, r1]) (by simp [lC, pcC])]; exact hL j)
    (by rw [eL_fw, h1 _ (by simp [srcCell, r1, RequestSelect.tagC, RequestSelect.rowC])
          (by simp [pcC, r1])]; exact htag)
    (by rw [eL_cc, h1 _ (by simp [srcCell, r1, nC]) (by simp [pcC, nC])]; exact hcps)
    (by rw [eL_rc, h1 _ (by simp [srcCell, r1, nC]) (by simp [pcC, nC])]; exact hout)
    (by rw [eL_my, h1 _ (by simp [srcCell, r1, myJ]) (by simp [pcC, myJ])]; exact hmy)
    (by rw [eL_idx]; simp [S1])
  rw [eL_lbl] at hFl
  -- the frame, in the ambient names
  have hF : ∀ x, x ≠ r1 RequestSelect.tagC → x ≠ myJ → x ≠ lC FetchLabel.lblC → F x = S1 x :=
    fun x a b c' => hFr x (by rwa [eL_fw]) (by rwa [eL_my]) (by rwa [eL_lbl])
  obtain ⟨t2, ht2, v2, p2⟩ := TemplateLookup.template_run (n := n) (p := p) (s := s)
    (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) hp hs k o z
  have hS2 : ∀ x, RequestSelect.mk [] [] (RequestSelect.vec TW OW
      (encodeCode (.append (.ticket q₁) c.1)) (encodeCode c.2) [] [] []) x = F (i2 x) := by
    intro x
    rcases x with x | x | x
    · rw [show i2 (.inl x) = r2 (.inl x) from rfl,
        hF _ (by simp [r2, r1]) (by simp [r2, myJ]) (by simp [r2, lC]),
        h1 _ (by simp [r2, srcCell, r1]) (by simp [r2, pcC]), hr2]
      exact RequestSelect.inner_nil x
    · rw [show i2 (.inr (.inl x)) = r2 (.inr (.inl x)) from rfl,
        hF _ (by simp [r2, r1]) (by simp [r2, myJ]) (by simp [r2, lC]),
        h1 _ (by simp [r2, srcCell, r1]) (by simp [r2, pcC]), hr2]
      exact RequestSelect.inner_nil x
    · fin_cases x
      · show TW = F (r1 RequestSelect.rowC)
        rw [hF _ (by simp [r1, RequestSelect.rowC, RequestSelect.tagC]) (by simp [r1, myJ])
          (by simp [r1, lC])]
        simp [S1, srcCell, pcC, r1]
      · show OW = F (lC FetchLabel.lblC)
        exact hFl.symm
      · show encodeCode (.append (.ticket q₁) c.1) = F (nC 8)
        rw [hF _ (by simp [r1, nC]) (by simp [myJ, nC]) (by simp [lC, nC]),
          h1 _ (by simp [srcCell, r1, nC]) (by simp [pcC, nC])]
        exact hte.symm
      · show encodeCode c.2 = F (nC 4)
        rw [hF _ (by simp [r1, nC]) (by simp [myJ, nC]) (by simp [lC, nC]),
          h1 _ (by simp [srcCell, r1, nC]) (by simp [pcC, nC])]
        exact hcol.symm
      all_goals
        first
        | (show [] = F (r2 RequestSelect.jc)
           rw [hF _ (by simp [r2, r1]) (by simp [r2, myJ]) (by simp [r2, lC]),
             h1 _ (by simp [r2, srcCell, r1]) (by simp [r2, pcC]), hr2])
        | (show [] = F (r2 RequestSelect.remc)
           rw [hF _ (by simp [r2, r1]) (by simp [r2, myJ]) (by simp [r2, lC]),
             h1 _ (by simp [r2, srcCell, r1]) (by simp [r2, pcC]), hr2])
        | (show [] = F (r2 RequestSelect.ic)
           rw [hF _ (by simp [r2, r1]) (by simp [r2, myJ]) (by simp [r2, lC]),
             h1 _ (by simp [r2, srcCell, r1]) (by simp [r2, pcC]), hr2])
        | (show [] = F (r2 RequestSelect.sc)
           rw [hF _ (by simp [r2, r1]) (by simp [r2, myJ]) (by simp [r2, lC]),
             h1 _ (by simp [r2, srcCell, r1]) (by simp [r2, pcC]), hr2])
  have l2 := lift i2 RequestSelect.program F _ _ hS2 _ _ _ _ p2
  obtain ⟨u1, hu1, q1⟩ := BitMachineRawSequence.runs (RawRowSplit.readU srcCell pcC)
    (LocateUniform.program eL) () (.inl ()) none (some false) LocateUniform.startControl vL
    _ _ _ _ _ r0 pL
  obtain ⟨u2, hu2, q2⟩ := BitMachineRawSequence.runs armA rs2 (leftLabel ())
    RequestSelect.startLabel ((none : Option Bool), LocateUniform.startControl)
    ((none : Option Bool), vL) RequestSelect.startControl v2 _ _ _ _ _ q1 l2
  refine ⟨u2, ?_, _, F, q2, hFr, hFl⟩
  have htL' : tL ≤ LocateUniform.locBound q₁ q₂ s C.2 c.2 pp.val zt := htL
  have ht2' : t2 ≤ RequestSelect.clock OW o.1.val (z o.1).1.val (.append (.ticket q₁) c.1) c.2
      (List.ofFn (fun a => (prodCodec (finCodec q₁) C.1).encode (z a)))
      (List.ofFn (fun b => C.2.encode (o.2 b))) := ht2
  omega

end

#print axioms i1Fun_injective
#print axioms eLFun_injective
#print axioms i2Fun_injective
#print axioms lift
#print axioms bank_mk
#print axioms arm_run

end Paper2.TemplateStep
