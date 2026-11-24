import YM.Integration.WilsonMovingForkFiniteCell
import YM.Integration.WilsonMovingForkForgotten
import YM.Integration.WilsonOriginalTwoFlatCompact

/-! Use the genuine funded compact word at the captured date to pay the
change of the original positive receiver on the very same fitted vote. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 1100000
noncomputable section
namespace YM.Integration.WilsonMovingForkCapturedFee
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Labels Marker Multi QuadraticLocal
open Push.Local Push.AbsoluteSums Planned.GuardedAtom Extra.Histories Next.Foundations
open RG16 RG16.Literal OPE Trace.Pilot Trace.Physical.GermGraph PhysicalNext.Repeat.Legato
open WilsonRootedKioskOccupiedSlip WilsonThermometerUnitFilingCoarse WilsonThermometerUnitFilingFourSquare
open WilsonThermometerUnitFilingFlatTelescope WilsonOriginalTwoFlatTelescope
open WilsonMacroscopicRichCaptureFilingBudget (capital)
open WilsonMovingForkHeterogeneousCut (Filed Invoice)
open WilsonMovingForkFiniteCell (Later)
open WilsonMovingForkMixedSeed (doses product)
open scoped Classical BigOperators Topology
variable {G:Gauge}{R:Run G}{S:Table R.family.book}{l:Ultrafilter (ℕ×ℕ)}
  {j n u v c K:ℕ}{d:Fin n → ℕ}{x:∀i,S.Field (d i)}
  (file:Filed R d K)(arms:∀i,Arm R.family S (l:Filter _) (d i) (x i))
  (jK:j≤K)(uv:u≤v)(vc:v≤c)
local notation "C" => R.family

def word (s:Fin n → Cover)(z:ℕ×ℕ):∀i:ℕ,Config G ((C).side i z.2)→ℂ:=
  let q:=doses R d file.station (N:=z.1) (per:=z.2) (file.A z.1 z.2) (fun i=>(arms i).source z)
  let ξ:=WilsonMovingForkSeededPoint.seats (R:=R) jK z.2 s
  file.row z.1 z.2 q ξ

variable (s:Fin n → Cover)(N per:ℕ)
local notation "rep" => (C).path.rep N per c
local notation "words" => word file arms jK s (N,per)

theorem original (simple:G.Simple)(cu:(C).ref 0≤u)(cN:c<N)(ou:Opened (C) 0 u per)(ov:Opened (C) 0 v per)
    (ready:WilsonCenteredCaptureClock.first R simple≤c)
    {V X ι:Type}[DecidableEq V][Fintype V][Countable ι]{J:Census V}
    {o:V→Site ((C).side c per)}{p:BudgetPoint}(L:Lamps X ι G p o J)(same:(rep).p=p)
    (t:X)(mode:J.Mode)(Z:Support ((C).side c per))(center:0∈Z)(reside:∀a∈mode.val,o a∈Z)
    (rad:ℕ)(near:∀a∈mode.val,separation (o a) 0≤rad)(w:V→ℝ)(wp:∀a,0<w a)
    {derivative gross:ℝ}(he:L.Paid w p.B (p.supportExponent+2) derivative)
    (hg:Gross L w p.B (p.supportExponent+2) gross)
    (named:words c=fun U=>(Poly.pass (bare L t U)).part mode)(I:ℂ)(bill:Invoice)
    (hired:∀i,v ≤ i → i ≤ K → Integrable (numerator R N per i (words i)) (prior G _))
    (fine:∀i∈Finset.Ico c K,‖feeAt R N per u words i‖≤bill.fine i)
    (coarse:∀i∈Finset.Ico v c,‖feeAt R N per v words i‖≤bill.coarse i)
    (bottom:‖reading R (N:=N) (numerator R N per v (words v)) v le_rfl-I‖≤bill.terminal):
    let earn:=WilsonPlantedOrdinary.fare (rep).p Z w derivative gross rad ((C).localSection 0)
      (C).params (price G (max (rep).p.order (rep).p.power)) (R.alloy.B.a.clock.forcedAllowance c)
      (LocalComparison.forcedDivisor (C) c) mode
    ∀(P D:ℕ){g Λ:ℝ},0≤g → (C).S.a c/(C).S.a v≤(g^(4*(P+D)))^2 →
      |2*capital (C) c earn 1| *g^D≤Λ → Λ*g^P≤bill.across →
      Later file arms jK uv vc s (N,per) I bill:=by
  intro earn P D g Λ gp length pay room
  refine ⟨hired,fine,?_,coarse,bottom⟩
  have hearing:=WilsonOriginalTwoFlatCompact.original R simple cu uv vc cN ou ov ready L same t mode Z
    center reside rad near w wp he hg
  have expense:=WilsonMovingForkForgotten.transmission (c:=c) (v:=v) R P D gp length pay
  change ‖reading R (N:=N) (numerator R N per c (words c)) u _-
    reading R (N:=N) (numerator R N per c (words c)) v _‖≤_
  rw [named]
  exact hearing.trans (expense.trans room)

end YM.Integration.WilsonMovingForkCapturedFee
