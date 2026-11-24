import YM.Integration.WilsonOriginalCensusFiledProbe
import YM.Integration.WilsonNeutralTwoPrintPathSpectrum

/-! Evaluate the signed deposited polynomial on the two wallets fixed on the actual child
sheets. The spatial origin is inherited from the parent of the first sheet. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusChildReading
open Finset Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene QuadraticLocal.Sunrise
open AllOrder AllOrder.Floe Laurent Comparison.RG02 Comparison.Density Comparison.Density.Mirrors
open Transport AnalyticBridge.SectorAffine.Offset WilsonEmittedWordJointFare WilsonEmittedCutGrouping
open WilsonEmittedFiledCatalogue Push.AbsoluteSums WilsonOriginalCensusPhysicalLoad
open scoped BigOperators ContDiff Classical Matrix.Norms.Frobenius

open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise Stationary
open AllOrder AllOrder.Floe Exterior Comparison.RG02 Comparison.RG02.Adjacent Multi
open FVA1Physical FVA1Physical.TwoReset Further.PhysicalPeriodLimitF933 Macrame
open RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Pipeline RegulatorIR.FVAAlt2.Booth
open RegulatorIR.Budget RegulatorIR.Budget.Packet RegulatorIR.Diagram
open WilsonCapturedRootedAngularSlots WilsonCapturedPrimaryWindingMaterialRead
open WilsonNeutralTwoPrintPeg WilsonCoeffUV WilsonCoeffUV.Blue FormalBulk08
open WilsonOriginalCensusFiledProbe WilsonNeutralTwoPrintPeg
open Stationary RegulatorIR.Budget RegulatorIR.Diagram WilsonCoeffUV.Blue

variable {G:Gauge}{n:Side}{V:Type}[Fintype V][DecidableEq V]{Γ:Census V}
  {I X:Bool→Type}{P:Bool→Passport n V}(M:(a:Bool)→I a→Row (P a) Γ G (X a))
  (w:Bool→V→ℝ)(grades:Bool→V→ℕ)(x:(a:Bool)→X a)
  (B:BudgetPoint)(σ b:Bool→ℝ)(p:Bool→ℕ)(g:ℝ)
  (s:Multi.Hot Γ)(v:V)(o:Site n)(tube:LinkTube G)
  (source target:ℕ)(A δ:ℝ)
local notation "D₀" => WilsonOriginalCensusPhysicalLoad.rank grades
local notation "pole₀" => WilsonOriginalCensusPhysicalLoad.head grades s.val
local notation "lag" => WilsonOriginalCensusPhysicalLoad.delay grades s.val
local notation "debt" => WilsonOriginalCensusTariff.debit source D₀
local notation "height" => pole₀+debt+target
local notation "sig" => (fun a=>WilsonEmittedCompactTariff.strip (σ a))

local notation "Slots" => Site n × Loc G 1

/-- The room and the original roster on each side remain attached to their own held test. -/
def original (layout:Bool→Layout G)(tape:Bool→Finset Age)(legal:∀a,Legal (tape a) (layout a))
    {seats shelf:Bool→ℕ}(stock:∀a,Scene.Armada (M a) (w a) (grades a) (σ a) (b a) (p a) (seats a) (shelf a))
    (positive:∀a,0<σ a)(resident:v∈s.val.val)(here:(P false).origin v=o)
    (child:(P true).origin v=(P false).origin v)
    (D:ℕ→Bool→MvPolynomial (Slots) ℝ)(ε:ℝ)(eps:0≤ε)
    (fare:(e r:ℕ)→(Fin r→Slots)→ℝ)
    (angular:∀e,e+pole₀<3*height → ∀l Y,
      phase l ((peek dvd_rfl (M false) (grades false) (layout false) (tape false) (x false) e Y).part s.val)-
      phase l ((peek dvd_rfl (M true) (grades true) (layout true) (tape true) (x true) e Y).part s.val)=
      MvPolynomial.eval Y (D e l))
    (term:∀e,e+pole₀<3*height → ∀r≤e+pole₀,∀z,
      ‖((Lava.marble r (D e false) z:ℝ):ℂ)+((Lava.marble r (D e true) z:ℝ):ℂ)*Complex.I‖≤fare e r z)
    (total:∀e,e+pole₀<3*height →
      ((e+pole₀).factorial:ℝ)*(∑r∈range (e+pole₀+1),∑z,fare e r z)≤ε)
    (width:ℝ)(room:Room B n tube B.B width)(radius:0≤width)(held:width≤2*g^(1/2:ℝ))
    (H β:ℝ)(thermal:H/2≤β ∧ β≤2*H)(dated:g=(Real.sqrt β)⁻¹)(small:g≤1/2)
    (side:B.B=Nat.ceil ((Real.log H)^2))(tax:B.supportExponent+2≤102)(reserve:∀a,Real.exp ((σ a)⁻¹^2)≤H)
    (begun:WilsonOriginalCensusTariffDate.Begun tube (Fintype.card V) D₀ (3*height) height p lag H)
    (quote:((g^pole₀)⁻¹*(groupPrice tube 0*((2*height:ℕ):ℝ)*((3*height:ℕ):ℝ)))*ε+
      (WilsonEmittedOutputPower.constant height+1)*(posted A D₀)*g^target≤δ):
    Reading M grades x B σ p g s v o tube source target A δ:=by
  refine ⟨layout,tape,legal,ε,eps,?_,?_,small,width,room,radius,held,H,β,thermal,dated,
    side,tax,reserve,begun,quote⟩
  · intro e fired
    exact (WilsonNeutralTwoPrintPathSpectrum.invoice M x grades s layout tape stock positive legal
      ⟨v,resident⟩ e (e+pole₀) (D e) (angular e fired) (fare e) (term e fired)).trans (total e fired)
  · intro a
    cases a
    · exact here
    · exact child.trans here

end YM.Integration.WilsonOriginalCensusChildReading
end
