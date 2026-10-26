import EthInapproximability.CurrentPaper.VectorsProducer
import EthInapproximability.CurrentPaper.QArithmeticJoined

/-!
# Segment 1c (completion): `q2 G s` produced, no supplied operand word

Lane owner:b-stage4-entry-program-3 (Paper B, unit 2, map item 3).

ONE fixed controller on `Z2 = VectorsProducer.Z ⊕ QProduct.Stack`: the
`Z` region starts with the literal guarded graph code, unary `s`, a BLANK
third input cell and the blank writer region (arbitrary old output); the
`QProduct` region starts blank. Phases:

(A1) charged copy of the graph code into the `QProduct` parser input cell;
(A2) the admitted parser `SourceNormalizationMachineDecode` on the
     `QProduct` parser region (`guarded_valid_run`);
(A3) charged copy of `s` into `QProduct` writer cell 28;
(A4) the admitted `QArithmeticJoined.program` (`QArithmeticJoined.run`),
     which writes unary `2 ^ clog 2 (12 s |E|) = q2 G s` into writer cell 56;
(A5) charged copy of that word into the third `Z` input cell;
(B)  the checked `VectorsProducer.program`, lifted on `Z`.

Five charged handoffs. The exit bank is exact on `Z`
(`VectorsProducer.exitBank`) and, on the `QProduct` region, existential
ONLY in the named arithmetic scratch of `QArithmeticJoined.run` (its
`QProduct.temp`/`QProduct.log` cells); all parser/writer cells of that region
are stated.
-/

namespace EthInapproximability.CurrentPaper.VectorsFromGraphQ

open Turing BitMachineEncoding BitMachineStackEmbedding
open MatrixStage4ScalarPreparationOps
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open EthInapproximability.ParameterizedNP.GuardedSourceSlab
open VectorsProducer (Z b inp)

noncomputable section

abbrev QS := QProduct.Stack
abbrev Z2 := Z ⊕ QS

/-- Instance search does not reach this nested sum under the strict flags;
the instance is the standard `instDecidableEqSum` of the two components. -/
instance instDecZ2 : DecidableEq Z2 :=
  @instDecidableEqSum Z QS (inferInstanceAs (DecidableEq Z)) (inferInstanceAs (DecidableEq QS))

def zc (k : Z) : Z2 := .inl k
def qc (k : QS) : Z2 := .inr k
def qIn : QS := .inl (.inl (.inl 0))

def sA1 : Fin 3 ↪ Z2 := ⟨![zc (inp 0), qc qIn, zc (b 11)], by decide⟩
def sA3 : Fin 3 ↪ Z2 := ⟨![zc (inp 1), qc QProduct.s, zc (b 11)], by decide⟩
def sA5 : Fin 3 ↪ Z2 := ⟨![qc QProduct.q, zc (inp 2), zc (b 11)], by decide⟩

def pq : SourceNormalizationMachineDecode.Stack ↪ Z2 :=
  ⟨fun k => .inr (.inl (.inl k)), fun _ _ h => by cases h; rfl⟩
def qInj : QS ↪ Z2 := ⟨Sum.inr, Sum.inr_injective⟩
def zInj : Z ↪ Z2 := ⟨Sum.inl, Sum.inl_injective⟩

def decQ := fun l => stackStmt pq (SourceNormalizationMachineDecode.program l)
def arithQ := fun l => stackStmt qInj (QArithmeticJoined.program l)
def prodZ := fun l => stackStmt zInj (VectorsProducer.program l)

def j5 := VectorsProducer.initial
def a5 := BitMachineRawSequence.program (copyProgram sA5) prodZ
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) (none : Option Bool) j5
def j4 := ((none : Option Bool), j5)
def a4 := BitMachineRawSequence.program arithQ a5
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) QArithmeticJoined.initial j4
def j3 := (QArithmeticJoined.initial, j4)
def a3 := BitMachineRawSequence.program (copyProgram sA3) a4
  (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel QProductJoined.start))
  (none : Option Bool) j3
def j2 := ((none : Option Bool), j3)
def a2 := BitMachineRawSequence.program decQ a3
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) VectorsProducer.ctl0 j2
def j1 := (VectorsProducer.ctl0, j2)
/-- The single fixed controller. -/
def program := BitMachineRawSequence.program (copyProgram sA1) a2
  (BitMachineRawSequence.leftLabel
    (Sum.inr SourceNormalizationMachineDecode.Admin.gate :
      SourceNormalizationMachineDecode.Label)) (none : Option Bool) j1
def initial := ((none : Option Bool), j1)

theorem upd_inl {A B : Type} [DecidableEq A] [DecidableEq B]
    (f : A → List Bool) (g : B → List Bool) (k : A) (w : List Bool) :
    Function.update (Sum.elim f g) (.inl k) w = Sum.elim (Function.update f k w) g := by
  funext j
  rcases j with j | j
  · by_cases h : j = k
    · subst h; simp
    · simp [Function.update_of_ne h, Function.update_of_ne (fun e => h (Sum.inl_injective e))]
  · simp

theorem upd_inr {A B : Type} [DecidableEq A] [DecidableEq B]
    (f : A → List Bool) (g : B → List Bool) (k : B) (w : List Bool) :
    Function.update (Sum.elim f g) (.inr k) w = Sum.elim f (Function.update g k w) := by
  funext j
  rcases j with j | j
  · simp
  · by_cases h : j = k
    · subst h; simp
    · simp [Function.update_of_ne h, Function.update_of_ne (fun e => h (Sum.inr_injective e))]

/-! ## Banks -/

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

def inputs0 (G : EndpointGraph V E) (s : ℕ) : Fin 3 → List Bool :=
  ![VectorsProducer.code G, List.replicate s true, []]

def Z0 (G : EndpointGraph V E) (s : ℕ) (output : List Bool) : Z → List Bool :=
  Sum.elim (inputs0 G s)
    (MatrixTableWriter.ready (K := 25) (fun _ => []) 0 0 0 0 0 0 [] output).contents

def Q0 : QS → List Bool := fun _ => []

def Q1 (G : EndpointGraph V E) : QS → List Bool :=
  Function.update Q0 qIn (VectorsProducer.code G)

/-- The parser's exit on `serializeGraph G`, all other cells blank. -/
def Qd (G : EndpointGraph V E) : QS → List Bool :=
  Sum.elim (Sum.elim (Sum.elim (fun _ => [])
    (![List.replicate (Fintype.card V) true, List.replicate (Fintype.card E) true, [], [],
      SourceGraphPayloadMachine.endpointStream (EncodedETHSource.serializeGraph G).edges, []] :
        Fin 6 → List Bool)) (fun _ => [])) (fun _ => [])

def Qa (G : EndpointGraph V E) (s : ℕ) : QS → List Bool :=
  Function.update (Qd G) QProduct.s (List.replicate s true)

/-! ## Phases -/

theorem phA1 (G : EndpointGraph V E) (s : ℕ) (output : List Bool) :
    ((advance (copyProgram sA1))^[2 * (VectorsProducer.code G).length + 2])
      (⟨some BitMachineCopy.Label.scan, none, Sum.elim (Z0 G s output) Q0⟩ :
        TM2.Cfg (fun _ : Z2 => Bool) _ _) =
      ⟨none, none, Sum.elim (Z0 G s output) (Q1 G)⟩ := by
  have h := FamilyRowGeneric.copy_blank sA1 (Sum.elim (Z0 G s output) Q0) (by rfl) (by rfl)
  have hsrc : Sum.elim (Z0 G s output) Q0 (sA1 0) = VectorsProducer.code G := rfl
  rw [hsrc] at h
  rw [show (sA1 1) = (Sum.inr qIn : Z2) from rfl, upd_inr] at h
  exact h

theorem phA2 (G : EndpointGraph V E) (s : ℕ) (output : List Bool) :
    ∃ t ≤ 101 * ((EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length + 1) ^ 3,
      ((advance decQ)^[t])
        (⟨some (Sum.inr SourceNormalizationMachineDecode.Admin.gate), VectorsProducer.ctl0,
          Sum.elim (Z0 G s output) (Q1 G)⟩ : TM2.Cfg (fun _ : Z2 => Bool) _ _) =
        ⟨none, SourceNormalizationMachineDecode.doneControl true,
          Sum.elim (Z0 G s output) (Qd G)⟩ := by
  obtain ⟨t, ht, hr⟩ := SourceNormalizationMachineDecode.guarded_valid_run
    (EncodedETHSource.serializeGraph G) (EncodedETHSource.serializeGraph_valid G)
  rw [EncodedETHSource.serializeGraph_edges,
    ← SourceGraphPayloadMachine.endpointStream_graph] at hr
  have hrun := BitMachineStackRun.run pq (Sum.elim (Z0 G s output) (Q1 G))
    SourceNormalizationMachineDecode.program
    (SourceNormalizationMachineDecode.guardedStart
      (true :: EncodedGraph.encode (EncodedETHSource.serializeGraph G))) t
  unfold SourceNormalizationMachineDecode.run at hr
  rw [hr] at hrun
  have hs : bank pq (Sum.elim (Z0 G s output) (Q1 G))
      (SourceNormalizationMachineDecode.guardedStart
        (true :: EncodedGraph.encode (EncodedETHSource.serializeGraph G))).stk =
      Sum.elim (Z0 G s output) (Q1 G) := by
    apply bank_eq_self
    intro k
    rcases k with k | k <;> fin_cases k <;> rfl
  have hf : bank pq (Sum.elim (Z0 G s output) (Q1 G))
      (SourceNormalizationMachineDecode.cfg none
        (SourceNormalizationMachineDecode.doneControl true) {}
        (List.replicate (EncodedETHSource.serializeGraph G).vertices true)
        (List.replicate (Fintype.card E) true) [] []
        (SourceGraphPayloadMachine.endpointStream (EncodedETHSource.serializeGraph G).edges)
        []).stk = Sum.elim (Z0 G s output) (Qd G) := by
    funext j
    rcases j with z | ((p | w) | r)
    · rw [bank_outside]
      · rfl
      · rintro ⟨k, hk⟩
        cases hk
    · rw [show (Sum.inr (Sum.inl (Sum.inl p)) : Z2) = pq p from rfl, bank_at]
      rcases p with k | k <;> fin_cases k <;> rfl
    · rw [bank_outside]
      · rfl
      · rintro ⟨k, hk⟩
        cases hk
    · rw [bank_outside]
      · rfl
      · rintro ⟨k, hk⟩
        cases hk
  have e1 : stackCfg pq (Sum.elim (Z0 G s output) (Q1 G))
      (SourceNormalizationMachineDecode.guardedStart
        (true :: EncodedGraph.encode (EncodedETHSource.serializeGraph G))) =
      (⟨some (Sum.inr SourceNormalizationMachineDecode.Admin.gate), VectorsProducer.ctl0,
        Sum.elim (Z0 G s output) (Q1 G)⟩ : TM2.Cfg (fun _ : Z2 => Bool) _ _) := by
    unfold stackCfg
    rw [hs]
    rfl
  have e2 : stackCfg pq (Sum.elim (Z0 G s output) (Q1 G))
      (SourceNormalizationMachineDecode.cfg none
        (SourceNormalizationMachineDecode.doneControl true) {}
        (List.replicate (EncodedETHSource.serializeGraph G).vertices true)
        (List.replicate (Fintype.card E) true) [] []
        (SourceGraphPayloadMachine.endpointStream (EncodedETHSource.serializeGraph G).edges)
        []) =
      (⟨none, SourceNormalizationMachineDecode.doneControl true,
        Sum.elim (Z0 G s output) (Qd G)⟩ : TM2.Cfg (fun _ : Z2 => Bool) _ _) := by
    unfold stackCfg
    rw [hf]
    rfl
  rw [e1, e2] at hrun
  exact ⟨t, ht, hrun⟩

theorem phA3 (G : EndpointGraph V E) (s : ℕ) (output : List Bool) :
    ((advance (copyProgram sA3))^[2 * s + 2])
      (⟨some BitMachineCopy.Label.scan, none, Sum.elim (Z0 G s output) (Qd G)⟩ :
        TM2.Cfg (fun _ : Z2 => Bool) _ _) =
      ⟨none, none, Sum.elim (Z0 G s output) (Qa G s)⟩ := by
  have h := FamilyRowGeneric.copy_blank sA3 (Sum.elim (Z0 G s output) (Qd G)) (by rfl) (by rfl)
  have hsrc : Sum.elim (Z0 G s output) (Qd G) (sA3 0) = List.replicate s true := rfl
  rw [hsrc, List.length_replicate] at h
  rw [show (sA3 1) = (Sum.inr QProduct.s : Z2) from rfl, upd_inr] at h
  exact h

theorem phA4 (G : EndpointGraph V E) (s : ℕ) (output : List Bool) :
    ∃ t ≤ QArithmeticJoined.cost s (Fintype.card E),
      ∃ F : QS → List Bool,
        ((advance arithQ)^[t])
          (⟨some (BitMachineRawSequence.leftLabel QProductJoined.start),
            QArithmeticJoined.initial, Sum.elim (Z0 G s output) (Qa G s)⟩ :
            TM2.Cfg (fun _ : Z2 => Bool) _ _) =
          ⟨none, QArithmeticJoined.initial, Sum.elim (Z0 G s output) F⟩ ∧
        F QProduct.q = List.replicate (q2 G s) true ∧
        (∀ j : GraphCountBridge.Stack,
          j ≠ (.inr (56 : Fin 64)) → F (.inl j) = Qa G s (.inl j)) := by
  obtain ⟨t, ht, F, hrun, hq, hframe⟩ := QArithmeticJoined.run (Qa G s) s (Fintype.card E)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (fun _ => rfl) rfl
  refine ⟨t, ht, F, ?_, hq, hframe⟩
  have hl := BitMachineStackRun.run qInj (Sum.elim (Z0 G s output) (Qa G s))
    QArithmeticJoined.program
    (⟨some (BitMachineRawSequence.leftLabel QProductJoined.start),
      QArithmeticJoined.initial, Qa G s⟩ : TM2.Cfg (fun _ : QS => Bool) _ _) t
  rw [hrun] at hl
  have hs : bank qInj (Sum.elim (Z0 G s output) (Qa G s)) (Qa G s) =
      Sum.elim (Z0 G s output) (Qa G s) :=
    bank_eq_self _ _ _ (fun _ => rfl)
  have hf : bank qInj (Sum.elim (Z0 G s output) (Qa G s)) F =
      Sum.elim (Z0 G s output) F := by
    funext j
    rcases j with z | k
    · rw [bank_outside]
      · rfl
      · rintro ⟨k, hk⟩
        cases hk
    · exact bank_at qInj _ F k
  simp only [stackCfg, hs, hf] at hl
  exact hl

theorem phA5 (G : EndpointGraph V E) (s : ℕ) (output : List Bool) (F : QS → List Bool)
    (hq : F QProduct.q = List.replicate (q2 G s) true) :
    ((advance (copyProgram sA5))^[2 * q2 G s + 2])
      (⟨some BitMachineCopy.Label.scan, none, Sum.elim (Z0 G s output) F⟩ :
        TM2.Cfg (fun _ : Z2 => Bool) _ _) =
      ⟨none, none, Sum.elim (VectorsProducer.B0 G s output) F⟩ := by
  have h := FamilyRowGeneric.copy_blank sA5 (Sum.elim (Z0 G s output) F) (by rfl) (by rfl)
  have hsrc : Sum.elim (Z0 G s output) F (sA5 0) = List.replicate (q2 G s) true := hq
  rw [hsrc, List.length_replicate] at h
  rw [show (sA5 1) = (Sum.inl (inp 2) : Z2) from rfl, upd_inl] at h
  have hz : Function.update (Z0 G s output) (inp 2) (List.replicate (q2 G s) true) =
      VectorsProducer.B0 G s output := by
    funext k
    rcases k with k | ((k | k) | k)
    · fin_cases k <;> rfl
    · rfl
    · rfl
    · rfl
  rw [hz] at h
  exact h

theorem pB (G : EndpointGraph V E) (s : ℕ) (output : List Bool) (F : QS → List Bool) :
    ∃ t ≤ VectorsProducer.producerBound G s, ∃ v,
      ((advance prodZ)^[t])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          VectorsProducer.initial, Sum.elim (VectorsProducer.B0 G s output) F⟩ :
          TM2.Cfg (fun _ : Z2 => Bool) _ _) =
        ⟨none, v, Sum.elim (VectorsProducer.exitBank G s output) F⟩ := by
  obtain ⟨t, ht, v, hr⟩ := VectorsProducer.vectors_from_graph G s output
  have hl := BitMachineStackRun.run zInj (Sum.elim (VectorsProducer.B0 G s output) F)
    VectorsProducer.program
    (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
      VectorsProducer.initial, VectorsProducer.B0 G s output⟩ :
        TM2.Cfg (fun _ : Z => Bool) _ _) t
  rw [hr] at hl
  have hs : bank zInj (Sum.elim (VectorsProducer.B0 G s output) F)
      (VectorsProducer.B0 G s output) = Sum.elim (VectorsProducer.B0 G s output) F :=
    bank_eq_self _ _ _ (fun _ => rfl)
  have hf : bank zInj (Sum.elim (VectorsProducer.B0 G s output) F)
      (VectorsProducer.exitBank G s output) =
      Sum.elim (VectorsProducer.exitBank G s output) F := by
    funext j
    rcases j with z | k
    · exact bank_at zInj _ _ z
    · rw [bank_outside]
      · rfl
      · rintro ⟨k, hk⟩
        cases hk
  simp only [stackCfg, hs, hf] at hl
  exact ⟨t, ht, v, hl⟩

/-! ## The composite -/

def fullBound (G : EndpointGraph V E) (s : ℕ) : ℕ :=
  (2 * (VectorsProducer.code G).length + 2) +
    101 * ((EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length + 1) ^ 3 +
    (2 * s + 2) + QArithmeticJoined.cost s (Fintype.card E) + (2 * q2 G s + 2) +
    VectorsProducer.producerBound G s + 5

theorem vectors_from_graph_bytes (G : EndpointGraph V E) (s : ℕ) (output : List Bool) :
    ∃ t ≤ fullBound G s, ∃ v, ∃ F : QS → List Bool,
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan), initial,
          Sum.elim (Z0 G s output) Q0⟩ : TM2.Cfg (fun _ : Z2 => Bool) _ _) =
        ⟨none, v, Sum.elim (VectorsProducer.exitBank G s output) F⟩ ∧
      F QProduct.q = List.replicate (q2 G s) true ∧
      (∀ j : GraphCountBridge.Stack,
        j ≠ (.inr (56 : Fin 64)) → F (.inl j) = Qa G s (.inl j)) := by
  obtain ⟨t4, ht4, F, h4, hq, hframe⟩ := phA4 G s output
  obtain ⟨tB, htB, vB, hB⟩ := pB G s output F
  obtain ⟨u5, hu5, r5⟩ := BitMachineRawSequence.runs (copyProgram sA5) prodZ
    BitMachineCopy.Label.scan (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    none none j5 vB (Sum.elim (Z0 G s output) F) (Sum.elim (VectorsProducer.B0 G s output) F)
    (Sum.elim (VectorsProducer.exitBank G s output) F) (2 * q2 G s + 2) tB
    (phA5 G s output F hq) hB
  obtain ⟨u4, hu4, r4⟩ := BitMachineRawSequence.runs arithQ a5
    (BitMachineRawSequence.leftLabel QProductJoined.start)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    QArithmeticJoined.initial QArithmeticJoined.initial j4 (none, vB)
    (Sum.elim (Z0 G s output) (Qa G s)) (Sum.elim (Z0 G s output) F)
    (Sum.elim (VectorsProducer.exitBank G s output) F) t4 u5 h4 r5
  obtain ⟨u3, hu3, r3⟩ := BitMachineRawSequence.runs (copyProgram sA3) a4
    BitMachineCopy.Label.scan
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel QProductJoined.start))
    none none j3 (QArithmeticJoined.initial, (none, vB))
    (Sum.elim (Z0 G s output) (Qd G)) (Sum.elim (Z0 G s output) (Qa G s))
    (Sum.elim (VectorsProducer.exitBank G s output) F) (2 * s + 2) u4 (phA3 G s output) r4
  obtain ⟨t2, ht2, h2⟩ := phA2 G s output
  obtain ⟨u2, hu2, r2⟩ := BitMachineRawSequence.runs decQ a3
    (Sum.inr SourceNormalizationMachineDecode.Admin.gate)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    VectorsProducer.ctl0 (SourceNormalizationMachineDecode.doneControl true) j2
    (none, (QArithmeticJoined.initial, (none, vB)))
    (Sum.elim (Z0 G s output) (Q1 G)) (Sum.elim (Z0 G s output) (Qd G))
    (Sum.elim (VectorsProducer.exitBank G s output) F) t2 u3 h2 r3
  obtain ⟨u1, hu1, r1⟩ := BitMachineRawSequence.runs (copyProgram sA1) a2
    BitMachineCopy.Label.scan
    (BitMachineRawSequence.leftLabel
      (Sum.inr SourceNormalizationMachineDecode.Admin.gate :
        SourceNormalizationMachineDecode.Label))
    none none j1 (VectorsProducer.ctl0, (none, (QArithmeticJoined.initial, (none, vB))))
    (Sum.elim (Z0 G s output) Q0) (Sum.elim (Z0 G s output) (Q1 G))
    (Sum.elim (VectorsProducer.exitBank G s output) F) _ u2 (phA1 G s output) r2
  refine ⟨u1, ?_, _, F, r1, hq, hframe⟩
  unfold fullBound
  omega

#print axioms upd_inl
#print axioms upd_inr
#print axioms phA2
#print axioms phA4
#print axioms phA5
#print axioms pB
#print axioms vectors_from_graph_bytes

end
end EthInapproximability.CurrentPaper.VectorsFromGraphQ
