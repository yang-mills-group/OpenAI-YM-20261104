import YM.Integration.WilsonIndependentRawNamedProduct

/-! A finite tree of occupied ordinary inputs on one normalized orbit board.
Each original named section retains its grade, position, and choice of
survey. Independent copies of the same name are permitted. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentRawRosterWord
open Lattice RG Wilson Source Labels PertExtension Orb XSpace XSpace.Rose XSpace.Cirrus
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Halo
open RegulatorIR.Profiles RegulatorIR.Budget RegulatorIR.Budget.Packet
open RegulatorIR.Step RegulatorIR.Prim RegulatorIR.Cluster RegulatorIR.Diagram
open RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Taping FVA2
open WilsonIndependentRawNamedStencil WilsonIndependentMatchedNamedPair
open scoped Classical
variable {G:Gauge}{I:Type}(R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)
    (σ:I → Bool)(d:I → ℕ)(key:∀i,(R.family.labels.level (d i)).Index)

def fold {A:Type}[Mul A] (vals:I → A):Composite I → A
  | .atom i => vals i
  | .pair a b => fold vals a * fold vals b

def degree (i:I):ℕ:=((R.family.labels.level (d i)).grades (key i)).2

def body (J:Composite I)(o:I → Cover):Portrait G:=
  Gather J fun i=>convey (o i) (brand R W (σ i) (d i) (key i))

def bank (J:Composite I)(o:I → Cover):Orders (Foot G):=
  J.product fun i=>shifted R W (σ i) (d i) (key i) (o i)

theorem enrolled (J:Composite I)(o:I → Cover):
    let D:=J.accounts (degree R d key)
    BasisT D D (body R W σ d key J o) (bank R W σ d key J o) ∧ Ranks D (bank R W σ d key J o):=by
  intro D
  exact ⟨Profiles.BasisT.given J (fun i=>convey (o i) (brand R W (σ i) (d i) (key i)))
    (fun i _=>(named R W (σ i) (d i) (key i) (o i)).1)
    (fun i _=>(named R W (σ i) (d i) (key i) (o i)).2),
    J.ranks _ (fun i _=>(named R W (σ i) (d i) (key i) (o i)).2)⟩

variable (Y:Sample 2)(pt:I → Cover)
def physical (J:Composite I):Config G Y.F.p.side → ℝ:=
  fold (fun i=>placed R W Y (σ i) (d i) (pt i) (key i)) J

def film (J:Composite I):Bare.Series (W.tree Y.F.p) G:=
  fold (fun i=>printed R W Y (σ i) (d i) (pt i) (key i)) J

local notation "O" => physical R W σ d key Y pt
local notation "A" => film R W σ d key Y pt
theorem finite (J:Composite I):Orb.PreTest (O J) ∧
    PowerSeries.X^(J.accounts (degree R d key))*A J=BareOrb.stencil (W.tree Y.F.p) (O J):=by
  induction J with
  | atom i =>
    exact ⟨admitted R W Y (σ i) (d i) (pt i) (key i),ranked R W Y (σ i) (d i) (pt i) (key i)⟩
  | pair l r hl hr =>
    change Orb.PreTest (O l*O r) ∧ PowerSeries.X^(_+_)*(A l*A r)=BareOrb.stencil _ (O l*O r)
    refine ⟨WilsonIndependentMatchedClosedPlan.product hl.1 hr.1,?_⟩
    rw [pow_add,WilsonOriginalPivotWardProduct.product _ hl.1 hr.1,←hl.2,←hr.2]
    ring

theorem submitted_all (J:Composite I):
    vital Y.F.p.side (body R W σ d key J pt)=WilsonIndependentMatchedOrbitReading.insert (O J):=by
  induction J with
  | atom i => exact submitted R W (σ i) (d i) (key i) (pt i) Y
  | pair l r hl hr =>
    funext t v h
    exact congrArg₂ (·*·) (congrFun (congrFun (congrFun hl t) v) h)
      (congrFun (congrFun (congrFun hr t) v) h)

theorem hearing (J:Composite I)(q:ℕ):
    PowerSeries.coeff q (Bare.normalized (W.tree Y.F.p) G (A J))=
      (plotPT WilsonIndependentMatchedOrbitReading.originalClock (vital Y.F.p.side (body R W σ d key J pt))
        (J.accounts (degree R d key)) q:ℂ):=by
  obtain ⟨test,filed⟩:=finite R W σ d key Y pt J
  rw [submitted_all R W σ d key Y pt J]
  exact WilsonIndependentMatchedRankedPair.ranked _ (O J) test
    (WilsonIndependentMatchedClosedPlan.actual (even_iff_two_dvd.mpr Y.F.p.even) _ test) _ _ _ filed

end YM.Integration.WilsonIndependentRawRosterWord
