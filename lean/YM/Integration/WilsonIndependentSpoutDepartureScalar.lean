import YM.Integration.WilsonIndependentSpoutVisitRoster
import YM.Integration.WilsonIndependentSpoutFiledDoseReturn
/-! Reading the reported returned series on the genuine dated field in the original thermal variable. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutDepartureScalar
open Lattice RG Source Labels PertExtension XSpace XSpace.Rose XSpace.Cirrus Precision
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Mer
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Budget RegulatorIR.Budget.Layer
open RegulatorIR.Cluster RegulatorIR.Prim RegulatorIR.Gain RegulatorIR.Halo RegulatorIR.Taping
open RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Uniform RegulatorIR.Oracle RegulatorIR.Atlas
open RegulatorIR.Epoch RegulatorIR.Epoch.League RegulatorIR.Momentum RegulatorIR.Profiles RegulatorIR.Calibration
open WilsonIndependentExactPlate WilsonIndependentLicensedCircuit WilsonIndependentRawRosterWord
open WilsonIndependentMatchedOpeningRoster (field)
open scoped Classical
open WilsonIndependentSpoutFittedRosterExit (returned)
open WilsonIndependentSpoutScalarLedger (ground scalar)
open WilsonIndependentSpoutFundedClocks (clock age)
open WilsonCoeffUV.Bank WilsonCoeffUV.Cosmos Wilson
variable {G:Gauge}(R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)(K:KernelChoices)
    (Y:Program K)(Z:∀P:Patch,P.Branches K G)(V:XSpace.Run)(a j:ℕ)(ha:0<a)(late:4≤j)
    (A:Requests a → Levels G)(s:Requests a → ℕ)(D:Tent (M V a))(p:ℕ)

variable {I T:Type} (σ:T → I → Bool)(d:I → ℕ)(key:T → (i:I) → (R.family.labels.level (d i)).Index)
    {E:I → ℕ}(cut:∀i,d i<E i)(arms:Composite I)(sample:Requests a → Sample 2)(sites:Requests a → I → Cover)


theorem original (O:ChartRatio G)(w:Requests a)(t:T):
    returned R W V a A s σ d key cut arms sites O w t=
    PowerSeries.map (algebraMap ℝ ℂ) (WilsonIndependentSpoutDoseBoundary.measure (A w) O (s w+M V a w)
      (arms.accounts (degree R d (key t))) (s w+M V a w) (s w)
      (field R W (σ t) d (key t) cut (sites w) arms)):=by
  let X:=cruises (A w) O (s w+M V a w) (arms.accounts (degree R d (key t))) (s w+M V a w) (s w)
      (field R W (σ t) d (key t) cut (sites w) arms)
  have native:=WilsonIndependentSpoutScalarLedger.reported A O s (Page.finallyW (M V a) w) X
  have cal:clock A O s (Page.finallyW (M V a) w)=relativeC (A w) O (s w+M V a w) (s w) ((s w+M V a w)-s w):=by
    simp [clock,age,Page.finallyW]
  rw [cal] at native
  ext q
  rw [PowerSeries.coeff_map]
  change ((PowerSeries.coeff (R:=ℝ) q (scalar (WilsonIndependentSpoutOriginalMarkedJourney.source A s O (Page.finallyW (M V a) w) X))):ℂ)=_
  rw [native]
  rfl

end YM.Integration.WilsonIndependentSpoutDepartureScalar
