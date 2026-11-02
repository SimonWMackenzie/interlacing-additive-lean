import CurrentAdditive.V42RawGraphParameters
import CurrentAdditive.V39PhysicalShapeTransport

/-! Literal raw graph+k parameters, a charged precision copy, and the
physical current sampler on one bank. Random bits occupy their own initial
input port; no parameter or constructor bank is supplied by the caller. -/
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 16384
namespace V42RawSamplerJoin
noncomputable section
open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open V42FullScheduleBatch
open V42RuntimeSchedule
open CurrentAdditive.V38OneStep CurrentAdditive.V39RecursiveGenerator
abbrev Shape := CurrentAdditive.V39PhysicalShapeSample.Stack
abbrev Fresh := {j : RoundedCodeOutput.Stack // j≠RoundedCodeOutput.resultPort}
abbrev Extra := Constructor ⊕ (Fresh ⊕ (Fin 65 ⊕ Fin 2))
abbrev Stack := V42RawGraphParameters.Stack ⊕ Extra
def rawSlots : V42RawGraphParameters.Stack ↪ Stack := Function.Embedding.inl
def shapeSlots : Shape ↪ Stack where
  toFun
    | .inl (.inl j) => .inr (.inl j)
    | .inl (.inr j) => .inr (.inr (.inl j))
    | .inr (.inl j) => .inr (.inr (.inr (.inl j)))
    | .inr (.inr _) => .inr (.inr (.inr (.inr 0)))
  inj' := by
    intro a b h
    rcases a with (a|a)|(a|a) <;> rcases b with (b|b)|(b|b) <;>
      simp_all
    fin_cases a; fin_cases b; rfl
def freshTape : Fresh := ⟨RoundedCodeOutput.tapePort,by decide⟩
def freshWidth : Fresh := ⟨RoundedCodeOutput.widthPort,by decide⟩
def tapePort : Stack := .inr (.inr (.inl freshTape))
def widthPort : Stack := .inr (.inr (.inl freshWidth))
def precisionPort : Stack := .inl (.inl (.inl V42FullScheduleBatch.precisionPort))
def copyScratch : Stack := .inr (.inr (.inr (.inr 1)))
def savedConstructor : Constructor ↪ Stack := ⟨fun j => .inr (.inl j),by intro a b h; cases h; rfl⟩
def constructorIndex : Fin 80 ≃ Constructor := (Fintype.equivFin Constructor).symm
def countSlots (i : Fin 80) : Fin 3 ↪ Stack :=
  ⟨![.inl (.inl (.inl (.inl (constructorIndex i)))),savedConstructor (constructorIndex i),copyScratch],by
    intro a b h; fin_cases a <;> fin_cases b <;>
      simp_all [savedConstructor,copyScratch]⟩
theorem counts_hsd : ∀ i j, countSlots i 0≠countSlots j 1 := by
  intro i j; simp [countSlots,savedConstructor]
theorem counts_hzd : ∀ i j, countSlots i 2≠countSlots j 1 := by
  intro i j; simp [countSlots,savedConstructor,copyScratch]
theorem counts_hdd : ∀ i j, countSlots i 1=countSlots j 1 → i=j := by
  intro i j h
  apply constructorIndex.injective
  simpa [countSlots,savedConstructor] using h
def copySlots : Fin 3 ↪ Stack :=
  ⟨![precisionPort,widthPort,copyScratch],by
    intro a b h; fin_cases a <;> fin_cases b <;>
      simp_all [precisionPort,widthPort,copyScratch]⟩
def rawProgram := fun l => stackStmt rawSlots (V42RawGraphParameters.program l)
def countProgram := Paper2.CopyAll.prog countSlots
def copyProgram := MatrixStage4ScalarPreparationOps.copyProgram copySlots
def sampleProgram := fun l => stackStmt shapeSlots (CurrentAdditive.V39PhysicalShapeSample.program l)
def countsFirstProgram := BitMachineRawSequence.program rawProgram countProgram
  (.inl (0 : Fin 81) : Paper2.CopyAll.Lab 80)
  V42RawGraphParameters.control (none : Option Bool)
def firstProgram := BitMachineRawSequence.program countsFirstProgram copyProgram BitMachineCopy.Label.scan
  (V42RawGraphParameters.control,(none : Option Bool)) (none : Option Bool)
def program := BitMachineRawSequence.program firstProgram sampleProgram
  CurrentAdditive.V39PhysicalShapeSample.start ((V42RawGraphParameters.control,(none : Option Bool)),(none : Option Bool))
  CurrentAdditive.V39PhysicalShapeSample.control
abbrev Label := BitMachineRawSequence.Label
  (BitMachineRawSequence.Label
    (BitMachineRawSequence.Label V42RawGraphParameters.Label (Paper2.CopyAll.Lab 80)) BitMachineCopy.Label)
  CurrentAdditive.V39PhysicalShapeSample.Label
def start : Label := .inl (.inl (.inl V42RawGraphParameters.start))
def control := (((V42RawGraphParameters.control,(none : Option Bool)),(none : Option Bool)),CurrentAdditive.V39PhysicalShapeSample.control)
def extra (tape : List Bool) : Extra → List Bool
  | .inl _ => []
  | .inr (.inl j) => if j.val=RoundedCodeOutput.tapePort then tape else []
  | .inr (.inr _) => []
def initial (graph : List Bool) (k : ℕ) (tape : List Bool) : Stack → List Bool :=
  Sum.elim (V42RawGraphParameters.initial graph k) (extra tape)
def afterRaw (graph : List Bool) (n k : ℕ) (tape : List Bool) : Stack → List Bool :=
  Sum.elim (V42RawGraphParameters.final graph n k) (extra tape)
def reservation (n k : ℕ) := 2^fullDrawExponent (Nat.clog 2 n) k
def precision (n k : ℕ) := publicBits (fullAlphabet n (Nat.clog 2 n)) (reservation n k)
def afterCounts (graph : List Bool) (n k : ℕ) (tape : List Bool) : Stack → List Bool :=
  bank savedConstructor (afterRaw graph n k tape) (constructorInput n k)
def afterCopy (graph : List Bool) (n k : ℕ) (tape : List Bool) : Stack → List Bool :=
  Function.update (afterCounts graph n k tape) widthPort (List.replicate (precision n k) true)
def constructorLength (n k : ℕ) := ∑ j : Constructor,(constructorInput n k j).length
def countClock (n k : ℕ) := 80*(2*constructorLength n k+3)+1
def sampleClock (n k : ℕ) :=
  let L := Nat.clog 2 n
  CurrentAdditive.V39PhysicalShapeSample.clock n (seedWidth L) (fullQ₁ L) (fullQ₂ L)
    (fullS L) (fullW L) (fullQ L) k (sampleSide L k) (precision n k) (reservation n k)
def clock (graph : List Bool) (n k : ℕ) :=
  V42RawGraphParameters.clock graph n k+countClock n k+(2*precision n k+2)+sampleClock n k+3

private instance seedNZ (L : ℕ) : NeZero (seedWidth L) := ⟨ne_of_gt (full_positive_widths L).1⟩
private instance q1NZ (L : ℕ) : NeZero (fullQ₁ L) := ⟨ne_of_gt (full_positive_widths L).2.1⟩
private instance q2NZ (L : ℕ) : NeZero (fullQ₂ L) := ⟨ne_of_gt (full_positive_widths L).2.2.1⟩
private instance sNZ (L : ℕ) : NeZero (fullS L) := ⟨ne_of_gt (full_positive_widths L).2.2.2.1⟩
private instance fsNZ (L : ℕ) : NeZero (4*fullS L) := ⟨ne_of_gt (full_positive_widths L).2.2.2.2.1⟩
private instance smNZ (L : ℕ) : NeZero (fullS L-3) := ⟨ne_of_gt (full_positive_widths L).2.2.2.2.2.1⟩
private instance wNZ (L : ℕ) : NeZero (fullW L) := ⟨ne_of_gt (full_positive_widths L).2.2.2.2.2.2.1⟩
private instance QNZ (L : ℕ) : NeZero (fullQ L) := ⟨ne_of_gt (full_positive_widths L).2.2.2.2.2.2.2⟩

theorem raw_run (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) (tape : List Bool) :
    ∃ t ≤ V42RawGraphParameters.clock (EncodedGraph.encode g) g.vertices k,
      ((advance rawProgram)^[t])
        (⟨some V42RawGraphParameters.start,V42RawGraphParameters.control,
          initial (EncodedGraph.encode g) k tape⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,V42RawGraphParameters.control,afterRaw (EncodedGraph.encode g) g.vertices k tape⟩ := by
  obtain ⟨t,ht,hr⟩ := V42RawGraphParameters.run g hg k
  have h := BitMachineStackRun.run rawSlots (initial (EncodedGraph.encode g) k tape)
    V42RawGraphParameters.program
    (⟨some V42RawGraphParameters.start,V42RawGraphParameters.control,
      V42RawGraphParameters.initial (EncodedGraph.encode g) k⟩ :
      TM2.Cfg (fun _ : V42RawGraphParameters.Stack => Bool) _ _) t
  rw [hr] at h
  have hi : bank rawSlots (initial (EncodedGraph.encode g) k tape)
      (V42RawGraphParameters.initial (EncodedGraph.encode g) k)=initial (EncodedGraph.encode g) k tape :=
    bank_eq_self rawSlots _ _ (fun _ => rfl)
  have hf : bank rawSlots (initial (EncodedGraph.encode g) k tape)
      (V42RawGraphParameters.final (EncodedGraph.encode g) g.vertices k)=
      afterRaw (EncodedGraph.encode g) g.vertices k tape := by
    funext j
    cases j with
    | inl j => exact bank_at rawSlots _ _ j
    | inr j => exact bank_outside rawSlots _ _ _ (by rintro ⟨x,hx⟩; cases hx)
  exact ⟨t,ht,by simpa only [rawProgram,stackCfg,hi,hf] using h⟩

theorem afterCounts_raw (graph : List Bool) (n k : ℕ) (tape : List Bool) (r : V42RawGraphParameters.Stack) :
    afterCounts graph n k tape (.inl r)=V42RawGraphParameters.final graph n k r := by
  rw [afterCounts,bank_outside]
  · rfl
  · rintro ⟨j,hj⟩; cases hj

theorem copied_counts (graph : List Bool) (n k : ℕ) (tape : List Bool) :
    Paper2.CopyAll.done countSlots 80 (afterRaw graph n k tape)=afterCounts graph n k tape := by
  funext j
  cases j with
  | inl r =>
      rw [Paper2.CopyAll.done_off countSlots _ _ (by intro i; simp [countSlots,savedConstructor])]
      exact (afterCounts_raw graph n k tape r).symm
  | inr j =>
      cases j with
      | inl ctor =>
          let i := constructorIndex.symm ctor
          have he : constructorIndex i=ctor := constructorIndex.apply_symm_apply ctor
          rw [←he]
          change Paper2.CopyAll.done countSlots 80 _ (countSlots i 1)=_
          rw [Paper2.CopyAll.done_dst countSlots counts_hdd]
          change V42RawGraphParameters.final graph n k (.inl (.inl (.inl (constructorIndex i)))) ++ [] =
            bank savedConstructor _ _ (savedConstructor (constructorIndex i))
          rw [bank_at,List.append_nil]
          exact congrFun (V42RawGraphParameters.constructor_projection graph n k) _
      | inr e =>
          rw [Paper2.CopyAll.done_off countSlots _ _ (by intro i; simp [countSlots,savedConstructor])]
          exact (bank_outside savedConstructor _ _ _ (by rintro ⟨x,hx⟩; cases hx)).symm

theorem counts_run (graph : List Bool) (n k : ℕ) (tape : List Bool) :
    ∃ t ≤ countClock n k, ∃ v : Option Bool,
      ((advance countProgram)^[t])
        (⟨some (.inl (0 : Fin 81)),(none : Option Bool),afterRaw graph n k tape⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,v,afterCounts graph n k tape⟩ := by
  obtain ⟨t,ht,v,hr⟩ := Paper2.CopyAll.all_run countSlots counts_hsd counts_hzd counts_hdd
    (afterRaw graph n k tape) (fun _ => rfl) (constructorLength n k) (by
      intro i
      change (V42RawGraphParameters.final graph n k (.inl (.inl (.inl (constructorIndex i))))).length ≤ _
      rw [congrFun (V42RawGraphParameters.constructor_projection graph n k) _]
      exact Finset.single_le_sum (f := fun j : Constructor => (constructorInput n k j).length)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)) none
  exact ⟨t,ht,v,by simpa only [countProgram,copied_counts] using hr⟩

theorem copy_run (graph : List Bool) (n k : ℕ) (tape : List Bool) :
    ((advance copyProgram)^[2*precision n k+2])
      (⟨some BitMachineCopy.Label.scan,(none : Option Bool),afterCounts graph n k tape⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none,(none : Option Bool),afterCopy graph n k tape⟩ := by
  have h := MatrixStage4ScalarPreparationOps.copy_run copySlots (afterCounts graph n k tape) (by
    rw [afterCounts,bank_outside]
    · rfl
    · rintro ⟨j,hj⟩; cases hj)
  have hs : afterCounts graph n k tape (copySlots 0)=List.replicate (precision n k) true :=
    (afterCounts_raw graph n k tape _).trans (V42RawGraphParameters.precision_exact graph n k)
  have ht : afterCounts graph n k tape (copySlots 1)=[] := by
    rw [afterCounts,bank_outside]
    · rfl
    · rintro ⟨j,hj⟩; cases hj
  simpa only [hs,ht,List.length_replicate,List.append_nil] using h

theorem sample_initial (graph : List Bool) (n k : ℕ) (tape : List Bool) (j : Shape) :
    afterCopy graph n k tape (shapeSlots j)=
      CurrentAdditive.V39PhysicalShapeSample.initial n (seedWidth (Nat.clog 2 n))
        (fullQ₁ (Nat.clog 2 n)) (fullQ₂ (Nat.clog 2 n)) (fullS (Nat.clog 2 n))
        (fullW (Nat.clog 2 n)) (fullQ (Nat.clog 2 n)) k (sampleSide (Nat.clog 2 n) k)
        tape (precision n k) j := by
  rcases j with (j|j)|(j|j)
  · change afterCopy graph n k tape (savedConstructor j)=constructorInput n k j
    rw [afterCopy,Function.update_of_ne (by simp [widthPort,savedConstructor])]
    exact bank_at savedConstructor _ _ j
  · change afterCopy graph n k tape (.inr (.inr (.inl j)))=RoundedCodeOutput.freshBank tape (precision n k) j
    by_cases hw : j.val=RoundedCodeOutput.widthPort
    · have he : j=freshWidth := Subtype.ext hw
      subst j
      have htw : RoundedCodeOutput.widthPort≠RoundedCodeOutput.tapePort := by decide
      simp [afterCopy,widthPort,RoundedCodeOutput.freshBank,freshWidth,htw]
    · have he : (.inr (.inr (.inl j)) : Stack)≠widthPort := by
        intro h; apply hw; exact congrArg Subtype.val (Sum.inl.inj (Sum.inr.inj (Sum.inr.inj h)))
      rw [afterCopy,Function.update_of_ne he]
      rw [afterCounts,bank_outside]
      · simp only [afterRaw,Sum.elim_inr,extra,RoundedCodeOutput.freshBank,hw,↓reduceIte]
      · rintro ⟨x,hx⟩; cases hx
  · rw [afterCopy,Function.update_of_ne (by simp [shapeSlots,widthPort]),afterCounts,bank_outside]
    · rfl
    · rintro ⟨x,hx⟩; cases hx
  · fin_cases j
    rw [afterCopy,Function.update_of_ne (by simp [shapeSlots,widthPort]),afterCounts,bank_outside]
    · rfl
    · rintro ⟨x,hx⟩; cases hx

def final (graph : List Bool) (n k edgeCount : ℕ) [NeZero n] (cc δv ζ : ℚ)
    (ht : FullTests cc (Nat.clog 2 n) edgeCount δv ζ)
    (bits : CurrentAdditive.RoundedDraw.BitBlocks (precision n k) (reservation n k))
    (suffix : List Bool) : Stack → List Bool :=
  let L := Nat.clog 2 n
  let tape := RoundedCodeLoop.tapeWord (precision n k) (reservation n k) bits ++ suffix
  bank shapeSlots (afterCopy graph n k tape)
    (CurrentAdditive.V39PhysicalShapeSample.final n (seedWidth L) (fullQ₁ L) (fullQ₂ L)
      (fullS L) (fullW L) (fullQ L)
      (by have h := fullS_ge_256 L; omega) rfl k (sampleSide L k) (reservation n k)
      (fullDrawCap_le cc L edgeCount k δv ζ ht) bits suffix)

theorem run (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) [NeZero g.vertices]
    (cc δv ζ : ℚ) (ht : FullTests cc (Nat.clog 2 g.vertices) g.edges.length δv ζ)
    (bits : CurrentAdditive.RoundedDraw.BitBlocks (precision g.vertices k) (reservation g.vertices k))
    (suffix : List Bool) :
    let tape := RoundedCodeLoop.tapeWord (precision g.vertices k) (reservation g.vertices k) bits ++ suffix
    ∃ t ≤ clock (EncodedGraph.encode g) g.vertices k,
      ((advance program)^[t])
        (⟨some start,control,initial (EncodedGraph.encode g) k tape⟩ :
          TM2.Cfg (fun _ : Stack => Bool) Label _) =
        ⟨none,control,final (EncodedGraph.encode g) g.vertices k g.edges.length cc δv ζ ht bits suffix⟩ := by
  intro tape
  let n := g.vertices
  let L := Nat.clog 2 n
  obtain ⟨a,ha,hra⟩ := raw_run g hg k tape
  obtain ⟨d,hd,v,hrd⟩ := counts_run (EncodedGraph.encode g) n k tape
  have hrc := copy_run (EncodedGraph.encode g) n k tape
  obtain ⟨b,hb,hrb⟩ := CurrentAdditive.V39PhysicalShapeSample.physical_from_bank
    n (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L) (fullW L) (fullQ L)
    shapeSlots (afterCopy (EncodedGraph.encode g) n k tape)
    (by have h := fullS_ge_256 L; omega) rfl k (sampleSide L k) (reservation n k)
    (fullDrawCap_le cc L g.edges.length k δv ζ ht) bits suffix
    (sample_initial (EncodedGraph.encode g) n k tape)
  obtain ⟨u,hu,hru⟩ := BitMachineRawSequence.runs rawProgram countProgram
    V42RawGraphParameters.start (.inl (0 : Fin 81) : Paper2.CopyAll.Lab 80)
    V42RawGraphParameters.control V42RawGraphParameters.control
    (none : Option Bool) v
    (initial (EncodedGraph.encode g) k tape) (afterRaw (EncodedGraph.encode g) n k tape)
    (afterCounts (EncodedGraph.encode g) n k tape) a d hra hrd
  obtain ⟨c,hc,hrc'⟩ := BitMachineRawSequence.runs countsFirstProgram copyProgram
    (BitMachineRawSequence.leftLabel V42RawGraphParameters.start) BitMachineCopy.Label.scan
    (V42RawGraphParameters.control,(none : Option Bool)) (V42RawGraphParameters.control,v)
    (none : Option Bool) (none : Option Bool)
    (initial (EncodedGraph.encode g) k tape) (afterCounts (EncodedGraph.encode g) n k tape)
    (afterCopy (EncodedGraph.encode g) n k tape) u (2*precision n k+2)
    (by simpa only [countsFirstProgram] using hru) hrc
  obtain ⟨t,htt,hrt⟩ := BitMachineRawSequence.runs firstProgram sampleProgram
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel V42RawGraphParameters.start))
    CurrentAdditive.V39PhysicalShapeSample.start
    ((V42RawGraphParameters.control,(none : Option Bool)),(none : Option Bool))
    ((V42RawGraphParameters.control,(none : Option Bool)),(none : Option Bool))
    CurrentAdditive.V39PhysicalShapeSample.control CurrentAdditive.V39PhysicalShapeSample.control
    (initial (EncodedGraph.encode g) k tape) (afterCopy (EncodedGraph.encode g) n k tape)
    (final (EncodedGraph.encode g) n k g.edges.length cc δv ζ ht bits suffix)
    c b (by simpa only [firstProgram] using hrc') hrb
  refine ⟨t,?_,by simpa only [program,start,control] using hrt⟩
  change b ≤ sampleClock n k at hb
  dsimp only [n] at hd hc hu htt hb
  unfold clock
  omega

theorem final_raw_preserved (graph : List Bool) (n k edgeCount : ℕ) [NeZero n] (cc δv ζ : ℚ)
    (ht : FullTests cc (Nat.clog 2 n) edgeCount δv ζ)
    (bits : CurrentAdditive.RoundedDraw.BitBlocks (precision n k) (reservation n k))
    (suffix : List Bool) (r : V42RawGraphParameters.Stack) :
    final graph n k edgeCount cc δv ζ ht bits suffix (.inl r)=
      V42RawGraphParameters.final graph n k r := by
  rw [final,bank_outside]
  · rw [afterCopy,Function.update_of_ne (by simp [widthPort])]
    exact afterCounts_raw graph n k _ r
  · rintro ⟨j,hj⟩
    rcases j with (j|j)|(j|j) <;> simp only [shapeSlots] at hj
    all_goals cases hj

#print axioms run
#print axioms final_raw_preserved
end
end V42RawSamplerJoin

