import YM.Integration.WilsonOriginalPublicNodalPhysicalHelper

/-! The physical-prefix and the grouped helper are commissioned with the same original kernel and unmarked book. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalHelperElection
open Lattice RG RG.Supply Org Input PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open Source Labels PertExtension RegulatorIR.Epoch RegulatorIR.Epoch.League
open XSpace Precision RegulatorIR RegulatorIR.Oracle RegulatorIR.Atlas RegulatorIR.Ledger RegulatorIR.Ledger.Sky
open RegulatorIR.Taping RegulatorIR.Uniform RegulatorIR.Calibration RegulatorIR.FVAAlt2 RegulatorIR.Momentum
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.AuxPlates Next.Foundations
open WilsonOriginalPublicNodalHelperShape (length physical)
open WilsonOriginalPublicNodalCommonRaw (Court)
open scoped Classical ENNReal NNReal
variable {G:Gauge}{H:Hol G}(R:PhysicalNext.Repeat.Legato.Run G)(P:Master H)(chart:ChartRatio G)(V:XSpace.Run)
    (e h k tier extra:ℕ)(p b u:ℕ)(γ:ℝ)(lo:0<γ)(hi:γ<1)
variable (Z:∀P:Patch,P.Branches R.family.path.levels.clock.kernel G)(col:G.ColorIndex)
    (B:WilsonIndependentEvenPassport.Menu P chart R.family.path.levels.clock.kernel V e h k tier extra)
    (late:5≤tier){X:Type}(m j:X → ℕ)(w:X → ℕ → ℕ)
    (blocks:∀x t,(R.family.S.block (m x+t)).val=V.ratio^(w x t))(r:X → ℕ)(ap:X → ℝ)(pos:∀x,0≤ap x)
local notation "N" => WilsonPositionProgramInfraredCircuit.circuit R V m j w blocks
local notation "Gd" => WilsonOriginalPublicNodalHelperCircuit.circuit V (physical j w) r B.a tier B.positive (le_trans (by decide:4 ≤ 5) late)


def GroupFund (F:Tent (length (physical j w) r B.a)):Prop:=
  let L:=WilsonIndependentGroupedOrbitBills.meter (Gd) ap pos
  let U:=(Gd).lane (Oracle.books R.family.path.levels.clock.kernel) G Z (sheet F)
  let c:=(Gd).leadA (Oracle.books R.family.path.levels.clock.kernel) G (quantum b u)
  Cylinder U ((Gd).payroll (Oracle.books R.family.path.levels.clock.kernel) G Z (sheet F)) ((Gd).pushP (Oracle.books R.family.path.levels.clock.kernel) G) ((Gd).takeP (Oracle.books R.family.path.levels.clock.kernel) G) L c p b u ∧
    Lantern ((Gd).dialect (Oracle.books R.family.path.levels.clock.kernel) G Z (sheet F)) (Rocket.native _) L c γ ∧ U.Endings L


structure TwoNotebooks where
  F:Tent j
  F':Tent (length (physical j w) r B.a)
  old:Notebook (N) (Oracle.books R.family.path.levels.clock.kernel) G Z col (Rocket.native _) F p
  fresh:Notebook (Gd) (Oracle.books R.family.path.levels.clock.kernel) G Z col (Rocket.native _) F' p
  flat:∀x,sheet F (Page.opening _ x)=Clocks.flat
  flat':∀x,sheet F' (Page.opening _ x)=Clocks.flat
  phys:∀(i:X → ℕ)(H:ℝ),WilsonOriginalPublicNodalPhysicalNote.Funded R V m j w blocks Z p i H F
  groupMoney:GroupFund R P chart V e h k tier extra p b u γ Z B late j w r ap pos F'


variable {simple:G.Simple}{axis:Axis}{ε:ℝ}
include lo hi in
theorem original (first:WilsonPositionProgramNestedElection.course simple axis ε R.kit)
    (fiscal:WilsonPositionProgramStageInvoice.Requested R.kit)(slow:WilsonWindowReportingPace.Slow R.kit)
    (paid:WilsonIndependentPublicPlateGrant.floor (G:=G) R.family.path.levels.clock.kernel tier (Oracle.books R.family.path.levels.clock.kernel) p b u γ lo hi ≤ extra)
    (width:p≤u)(rate:0<b):
    ∃base:ℕ,∀(m j:X → ℕ)(w:X → ℕ → ℕ)
      (blocks:∀x t,(R.family.S.block (m x+t)).val=V.ratio^(w x t)),(∀x,base ≤ m x) →
      ∀(r:X → ℕ),(∀x,r x<B.a) → (∀x,0<length (physical j w) r B.a x) →
      ∀(ap:X → ℝ)(pos:∀x,0≤ap x),
      Nonempty (TwoNotebooks R P chart V e h k tier extra p b u γ Z col B late m j w blocks r ap pos):=by
  obtain ⟨base,phys⟩:=WilsonOriginalPublicNodalPhysicalNote.original (X:=X) R V Z col p first fiscal slow
  refine ⟨base,?_⟩
  intro m j w blocks old r res enough ap pos
  obtain ⟨F,book,flat,salary⟩:=phys m j w blocks old
  obtain ⟨F',fresh,flat',fund⟩:=WilsonOriginalPublicNodalHelperBook.original P chart R.family.path.levels.clock.kernel V e h k tier extra (Oracle.books R.family.path.levels.clock.kernel) Z
    p b u γ lo hi B simple late width rate paid (physical j w) r res enough ap pos col
  exact ⟨⟨F,F',book,fresh,flat,flat',salary,fund⟩⟩

variable (T:TwoNotebooks R P chart V e h k tier extra p b u γ Z col B late m j w blocks r ap pos)
include T

def physicalCourt (i:X → ℕ)(H:ℝ):Court G X p:=
  WilsonOriginalPublicNodalPhysicalHelper.court (N) (Oracle.books R.family.path.levels.clock.kernel) Z T.F
    (WilsonPositionProgramInfraredMeter.wallet R V m j w i H) ((N).leadA (Oracle.books R.family.path.levels.clock.kernel) G (FVAAlt2.Lodge.through p))
    p 1 0 (Rocket.native _) (1/2) (T.phys i H)
    (WilsonPositionProgramInfraredCircuit.units R V m j w blocks).1 T.flat

def groupedCourt:Court G X p:=
  WilsonOriginalPublicNodalPhysicalHelper.court (Gd) (Oracle.books R.family.path.levels.clock.kernel) Z T.F'
    (WilsonIndependentGroupedOrbitBills.meter (Gd) ap pos) ((Gd).leadA (Oracle.books R.family.path.levels.clock.kernel) G (quantum b u))
    p b u (Rocket.native _) γ T.groupMoney
    (WilsonOriginalPublicNodalHelperCircuit.opening V (physical j w) r B.a tier B.positive (by omega)) T.flat'

end YM.Integration.WilsonOriginalPublicNodalHelperElection
end
