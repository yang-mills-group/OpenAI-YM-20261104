import YM.Integration.OriginalMarkedHistoryBirth
import YM.Integration.WilsonInvariantActionCurvatureReturn
import YM.Integration.WilsonMatrixTicketLanesSelectedNormalization

/-! The unconditioned original Q birth and its retained partner under the true nonlinear prior. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionFineSource
open Function Filter Set Finset MeasureTheory Lattice Wilson RG RG.Shoot Marker OPE.Therm Comparison.RG02
open Comparison.Density.RenderM Comparison.Density.RenderM.Token ActualRunPacketRetuning
open LocalComparison FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric Pert.Asymptotics
open ManuscriptQLocalOriginalConditionalTail ManuscriptQLocalRegularConditional ManuscriptQLocalSourceFourier
open RG.Supply Next.Rank Push.GridApprox WardBin.Wheels
open MergeProof PhysicalNext.Repeat.Legato PhysicalNext.Repeat Next.Scheduling Next.Scheduling.Clock
open Push.PriceCompiler Next.Foundations Source RG3.Script.Picnic PhysicalNext.ThroughLaunch WilsonLimitConstruction
open Actual Order IterationFour IterationFour.Vacuum
open WilsonInvariantActionTransportedOld WilsonInvariantActionMixedMaterial
open RG16 PertExtension Tree Precision RG17 RG12 Extraction Spec OPE Table SharpGram.Lenses Pier.Lair Overlay PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology
open MergeProof.Accent


open OPE.Therm OriginalMarkedBirthStencil
open Extra.Trajectories

variable {V:Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable {G:Gauge} {B:MS.Local.Physical.Deck G} (R:Run G) (simple:G.Simple)
  (u:V→MS.Rake.Label B) (J:Request V) (A:NumericSchedule R.family J)
  (d:LocalFormal.Datum R.family (Stock.census V)) (Q:MS.Land.Prescription B)
  (o:V→Site (R.family.side (d.level+1) d.period)) (μ:ℝ) (orders:V→ℕ)
local notation "target₀" => ActualOriginalQPointSetup.request R u J
local notation "packet₀" => ActualOriginalQInitialInput.packets R simple u J A d Q o μ orders
local notation "g" => Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
local notation "vacuum₀" => R.family.path.rep d.cutoff d.period (d.level+1)
local notation "Ω" => Config G (R.family.side (d.level+1) d.period)
variable (x:IndependentTests (ActualOriginalQPointSetup.request R u J).tests)

def plain : Ω→Marker.Poly (Stock.census V):=(packet₀).read (testInclusion (target₀).tests x) (g)
def held : Ω→Marker.Poly (Stock.census V):=ManuscriptQLocalOriginalConditionalTail.source (packet₀) (vacuum₀).p (g) x 1

theorem birth (ready:ActualOriginalQLayout.referenceLevel R u≤d.level+1) (T:Ω):
    OriginalMarkedHistoryBirth.response R simple u J A d Q o μ orders x le_rfl T=
      plain R simple u J A d Q o μ orders x T-held R simple u J A d Q o μ orders x T:=by
  let F:=vacuum₀
  let X:=plain R simple u J A d Q o μ orders x
  let Y:=held R simple u J A d Q o μ orders x
  let D:=OriginalMarkedHistoryBirth.input R simple u J A d Q o μ orders x
  let E:=OriginalMarkedHistoryBirth.cooled R simple u J A d Q o μ orders x
  have hx(t:Ω):D t=F.eval t • Poly.pass (X t):=
    QLocalNormalizedQBirth.source R simple u J A d Q o μ orders ready (testInclusion (target₀).tests x) t
  have he(t:Ω):E t=F.eval t • Poly.pass (Y t):=rfl
  have norm (f:Ω→Poly (Stock.census V)) (w:Ω→Poly (Stock.census V)) (eq:∀t,f t=F.eval t • w t):
      actualSignedTransport R.family (N:=d.cutoff) f le_rfl T=w T:=by
    unfold actualSignedTransport
    rw [actualTransport_base R.family R.makes d.below]
    change (F.eval T)⁻¹ • f T=w T
    have nz:F.eval T≠0:=(Multi.AxisShift.chosen_positive R.makes.wilson d.below T).ne'
    rw [eq T,smul_smul,inv_mul_cancel₀ nz,one_smul]
  have paid:=OriginalMarkedBirthStencil.paid R simple u J A d Q o μ orders OriginalMarkedBirthStencil.mesh (g)
  have quiet:=ManuscriptQLocalOriginalFineMaskLoss.means_quiet (packet₀) paid x F.p T
  have zeroX:(X T).part (Stock.census V).quiet=0:=quiet.1
  have zeroY:(Y T).part (Stock.census V).quiet=0:=quiet.2
  change connected (actualSignedTransport R.family (N:=d.cutoff) D le_rfl T)-
    connected (actualSignedTransport R.family (N:=d.cutoff) E le_rfl T)=X T-Y T
  rw [norm D _ hx,norm E _ he,RG02.Marks.recover_connected zeroX,RG02.Marks.recover_connected zeroY]

theorem paid (warm:Poetry R.family.path.levels) (q:ℕ) {ε:ℝ} (hp:0<ε):
    ∀ᶠm:ℕ in atTop,∀(d:LocalFormal.Datum R.family (Stock.census V)),d.level=m→
      ∀(Q:MS.Land.Prescription B)(o:V→Site (R.family.side (d.level+1) d.period))(μ:ℝ)(orders:V→ℕ)
        (x:IndependentTests (target₀).tests),
        let change:=fun T=>plain R simple u J A d Q o μ orders x T-held R simple u J A d Q o μ orders x T
        let cost:=fun T=>Poly.price (fun _:V=>(1:ℝ)) (change T)
        let ν:=scene R.family.path d.cutoff d.period (d.level+1)
        Integrable cost ν ∧ (∫T,cost T ∂ν)≤ε*Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)^q:=by
  filter_upwards [OriginalMarkedHistoryBirth.physical R simple u J A warm 0 q hp,
    eventually_ge_atTop (ActualOriginalQLayout.referenceLevel R u)] with m income deep d level Q o μ orders x change cost ν
  have sold:=income d level Q o μ orders x (d.level+1) le_rfl
  have ready:ActualOriginalQLayout.referenceLevel R u≤d.level+1:=by omega
  simpa only [Nat.zero_add,pow_one,birth R simple u J A d Q o μ orders x ready] using sold

end YM.Integration.WilsonInvariantActionFineSource
