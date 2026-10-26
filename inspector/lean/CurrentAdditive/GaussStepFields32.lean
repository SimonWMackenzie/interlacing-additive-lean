import CurrentAdditive.GaussAssemblerReset32
import CurrentAdditive.GaussPivotPayload32

/-!
One fixed Fin32 TM2 controller for Gauss state-field preparation. Its two
entry labels encode the terminal decision made by the outer physical row
guard. The active entry reads pivot-search tag20 itself. The pivot path runs
the checked parser, branch copy/counter updates, body splitter, pair emitter,
pair framer, body append, worker reset, count framer, final list join, scratch
reset, and Bank4 state assembler. The no-pivot and terminal paths use the
same parser/branch/assembler and bypass pivot-list construction.

The operational correspondence and time theorem are stated separately below
the fixed program; defining these finite statements is not a correctness
claim by itself.
-/

namespace CurrentAdditive.GaussStepFields32

noncomputable section

set_option maxRecDepth 1024

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding

abbrev Stack := Fin 32

structure Control where
  parse : GaussParsedState32.Control
  branch : GaussBranchFields32.Control
  split : GaussPivotBodySplit32.Control
  pair : GaussPivotPairEmit32.Control
  payload : GaussPivotPayload32.Control
  append : GaussPivotAppend32.Control
  resetWriter : GaussWorkerReset32.Control
  header : GaussPivotHeader32.Control
  join : GaussPivotJoin32.Control
  resetAssembler : GaussAssemblerReset32.Control
  assemble : GaussStateAssemble16.Control
  deriving DecidableEq

private abbrev HeadControl :=
  GaussParsedState32.Control × GaussBranchFields32.Control ×
    GaussPivotBodySplit32.Control × GaussPivotPairEmit32.Control ×
      GaussPivotPayload32.Control
private abbrev TailControl :=
  GaussPivotAppend32.Control × GaussWorkerReset32.Control ×
    GaussPivotHeader32.Control × GaussPivotJoin32.Control ×
      GaussAssemblerReset32.Control × GaussStateAssemble16.Control

private def controlEquiv : (HeadControl × TailControl) ≃ Control where
  toFun x :=
    ⟨x.1.1,x.1.2.1,x.1.2.2.1,x.1.2.2.2.1,x.1.2.2.2.2,
     x.2.1,x.2.2.1,x.2.2.2.1,x.2.2.2.2.1,
     x.2.2.2.2.2.1,x.2.2.2.2.2.2⟩
  invFun v :=
    ((v.parse,v.branch,v.split,v.pair,v.payload),
      (v.append,v.resetWriter,v.header,v.join,
        v.resetAssembler,v.assemble))
  left_inv := by intro x; rcases x with ⟨⟨a,b,c,d,e⟩,⟨f,g,h,i,j,k⟩⟩; rfl
  right_inv := by intro v; cases v; rfl

noncomputable instance : Fintype Control :=
  Fintype.ofEquiv (HeadControl × TailControl) controlEquiv

def defaultControl : Control where
  parse := none
  branch := ((),none)
  split := (((),none),(none,none))
  pair := none
  payload := (((),none),
    (SourceListMachineWriter.framingMachine true).initial)
  append := ((),none)
  resetWriter := ((),none)
  header := (((),none),
    (SourceListMachineWriter.framingMachine false).initial)
  join := ((),none)
  resetAssembler := ((),none)
  assemble := ((),none)

inductive Label where
  | parse (terminal : Bool) (l : GaussParsedState32.Label)
  | afterParse (terminal : Bool)
  | saveTag (l : SourceClausePreservingBroadcast.Label)
  | afterSaveTag
  | branch (l : GaussBranchFields32.Label)
  | afterBranch
  | split (l : GaussPivotBodySplit32.Label)
  | afterSplit
  | pair (l : GaussPivotPairEmit32.Label)
  | afterPair
  | payload (l : GaussPivotPayload32.Label)
  | afterPayload
  | append (l : GaussPivotAppend32.Label)
  | afterAppend
  | resetWriter (l : GaussWorkerReset32.Label)
  | afterResetWriter
  | header (l : GaussPivotHeader32.Label)
  | afterHeader
  | join (l : GaussPivotJoin32.Label)
  | afterJoin
  | resetAssembler (l : GaussAssemblerReset32.Label)
  | afterResetAssembler
  | assemble (l : GaussStateAssemble16.Label)
  | done
  deriving DecidableEq, Fintype

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def eParse (v : GaussParsedState32.Control) : Control :=
  {defaultControl with parse := v}
def eBranch (v : GaussBranchFields32.Control) : Control :=
  {defaultControl with branch := v}
def eSplit (v : GaussPivotBodySplit32.Control) : Control :=
  {defaultControl with split := v}
def ePair (v : GaussPivotPairEmit32.Control) : Control :=
  {defaultControl with pair := v}
def ePayload (v : GaussPivotPayload32.Control) : Control :=
  {defaultControl with payload := v}
def eAppend (v : GaussPivotAppend32.Control) : Control :=
  {defaultControl with append := v}
def eResetWriter (v : GaussWorkerReset32.Control) : Control :=
  {defaultControl with resetWriter := v}
def eHeader (v : GaussPivotHeader32.Control) : Control :=
  {defaultControl with header := v}
def eJoin (v : GaussPivotJoin32.Control) : Control :=
  {defaultControl with join := v}
def eResetAssembler (v : GaussAssemblerReset32.Control) : Control :=
  {defaultControl with resetAssembler := v}
def eAssemble (v : GaussStateAssemble16.Control) : Control :=
  {defaultControl with assemble := v}

def assembleSlot : Fin 16 ↪ Stack where
  toFun j := ⟨j.val, by omega⟩
  inj' := by intro a b h; exact Fin.ext (by
    have hv := congrArg Fin.val h
    exact hv)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .parse terminal l => BitMachineInline.stmt (Label.parse terminal)
      eParse Control.parse (some (.afterParse terminal))
      (GaussParsedState32.program l)
  | .afterParse terminal => .load (fun _ => eBranch ((),none))
      (.goto (fun _ => if terminal then .branch (.copy .halted 0 .scan)
        else .saveTag .scan))
  | .saveTag l => BitMachineInline.stmt Label.saveTag
      eBranch Control.branch (some .afterSaveTag)
      (SourceClausePreservingBroadcast.program (20 : Stack) 31 [25] l)
  | .afterSaveTag => .load (fun _ => eBranch ((),none))
      (.goto (fun _ => .branch .active))
  | .branch l => BitMachineInline.stmt Label.branch
      eBranch Control.branch (some .afterBranch)
      (GaussBranchFields32.program l)
  | .afterBranch => .pop 25 (fun v b => {v with parse := b})
      (.branch (fun v => v.parse.getD false)
        (.load (fun _ => eSplit (((),none),(none,none)))
          (.goto (fun _ => .split (.copy .scan))))
        (.goto (fun _ => .afterJoin)))
  | .split l => BitMachineInline.stmt Label.split
      eSplit Control.split (some .afterSplit)
      (GaussPivotBodySplit32.program l)
  | .afterSplit => .load (fun _ => ePair none)
      (.goto (fun _ => .pair (.inl (.emit 0))))
  | .pair l => BitMachineInline.stmt Label.pair
      ePair Control.pair (some .afterPair)
      (GaussPivotPairEmit32.program l)
  | .afterPair => .load (fun _ => ePayload (((),none),
      (SourceListMachineWriter.framingMachine true).initial))
      (.goto (fun _ => .payload (.copyIn .scan)))
  | .payload l => BitMachineInline.stmt Label.payload
      ePayload Control.payload (some .afterPayload)
      (GaussPivotPayload32.program l)
  | .afterPayload => .load (fun _ => eAppend ((),none))
      (.goto (fun _ => .append (.copyBodyDirect .scan)))
  | .append l => BitMachineInline.stmt Label.append
      eAppend Control.append (some .afterAppend)
      (GaussPivotAppend32.program l)
  | .afterAppend => .load (fun _ => eResetWriter ((),none))
      (.goto (fun _ => .resetWriter (.inl 0)))
  | .resetWriter l => BitMachineInline.stmt Label.resetWriter
      eResetWriter Control.resetWriter (some .afterResetWriter)
      (GaussWorkerReset32.program l)
  | .afterResetWriter => .load (fun _ => eHeader (((),none),
      (SourceListMachineWriter.framingMachine false).initial))
      (.goto (fun _ => .header (.copyIn .scan)))
  | .header l => BitMachineInline.stmt Label.header
      eHeader Control.header (some .afterHeader)
      (GaussPivotHeader32.program l)
  | .afterHeader => .load (fun _ => eJoin ((),none))
      (.goto (fun _ => .join .clear7))
  | .join l => BitMachineInline.stmt Label.join
      eJoin Control.join (some .afterJoin)
      (GaussPivotJoin32.program l)
  | .afterJoin => .load (fun _ => eResetAssembler ((),none))
      (.goto (fun _ => .resetAssembler (.inl 0)))
  | .resetAssembler l => BitMachineInline.stmt Label.resetAssembler
      eResetAssembler Control.resetAssembler (some .afterResetAssembler)
      (GaussAssemblerReset32.program l)
  | .afterResetAssembler => .load (fun _ => eAssemble ((),none))
      (.goto (fun _ => .assemble (.copy 0 .scan)))
  | .assemble l => BitMachineStackEmbedding.stmt assembleSlot
      Label.assemble eAssemble Control.assemble (some .done)
      (GaussStateAssemble16.program l)
  | .done => .halt

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c c' : Config} {n : Nat} (h : run n c = c') (u : Nat) :
    run (n+u) c = run u c' := by
  rw [Nat.add_comm, run, Function.iterate_add_apply]
  exact congrArg (run u) h

end
end CurrentAdditive.GaussStepFields32
