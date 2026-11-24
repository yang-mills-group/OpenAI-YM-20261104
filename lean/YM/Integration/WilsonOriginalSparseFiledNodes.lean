import YM.Integration.WilsonOriginalSparseFiledProbe
import YM.Integration.WilsonOriginalSparsePegReading
/-! The physical signed aperture is local to an occupied root; the original scored arms fund both remote tails. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalSparseFiledNodes
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

open WilsonOriginalSparseFiledRanks Push.AbsoluteSums Animals
local notation "entry" t:max l:max e:max => WilsonNeutralTwoPrintAccount.entry M x grades s l t e

def factor (d:ℕ):ℝ:=max 1 (2*WilsonOriginalSparsePeg.cost d)

def original (layout:Bool→Layout G)(tape:Bool→Finset Age)(legal:∀a,Legal (tape a) (layout a))
    {seats shelf:Bool→ℕ}(stock:∀a,Scene.Armada (M a) (w a) (grades a) (σ a) (b a) (p a) (seats a) (shelf a))
    (positive:∀a,0<σ a)(wallet:∀a i,0<w a i)(resident:v∈s.val.val)(site:∀a,(P a).origin v=o)
    (m:ℕ)(localFee:ℕ→ℕ→ℝ)(nonnegative:∀e r,0≤localFee e r)(ε:ℝ)(eps:0≤ε)
    (unit:∀e, e + pole₀ < 3*height →
      ‖(peek dvd_rfl (M false) (grades false) (layout false) (tape false) (x false) e 0).part s.val-
       (peek dvd_rfl (M true) (grades true) (layout true) (tape true) (x true) e 0).part s.val‖ ≤ localFee e 0)
    (nodes:∀e, e + pole₀ < 3*height → ∀r:ℕ, 0 < r → r ≤ e + pole₀ → ∀z:Fin r→Slots,
      (∀j,z j∈hull G o m) → ∀S j, let Y:=WilsonOriginalSparsePeg.probe (e+pole₀) z S j
      ‖(peek dvd_rfl (M false) (grades false) (layout false) (tape false) (x false) e Y).part s.val -
       (peek dvd_rfl (M true) (grades true) (layout true) (tape true) (x true) e Y).part s.val‖ ≤ localFee e r)
    (total:∀e, e + pole₀ < 3*height →((e+pole₀).factorial:ℝ)*
      (∑r∈range (e+pole₀+1),WilsonOriginalSparseFiledProbe.fare (G:=G) s m e r (factor (e+pole₀)*localFee e r) w σ b grades)≤ε)
    (width:ℝ)(room:Room B n tube B.B width)(radius:0≤width)(held:width≤2*g^(1/2:ℝ))
    (H β:ℝ)(thermal:H/2≤β ∧ β≤2*H)(dated:g=(Real.sqrt β)⁻¹)(small:g≤1/2)
    (side:B.B=Nat.ceil ((Real.log H)^2))(tax:B.supportExponent+2≤102)(reserve:∀a,Real.exp ((σ a)⁻¹^2)≤H)
    (begun:WilsonOriginalCensusTariffDate.Begun tube (Fintype.card V) D₀ (3*height) height p lag H)
    (quote:((g^pole₀)⁻¹*(groupPrice tube 0*((2*height:ℕ):ℝ)*((3*height:ℕ):ℝ)))*ε+
      (WilsonEmittedOutputPower.constant height+1)*(posted A D₀)*g^target≤δ):
    Reading M grades x B σ p g s v o tube source target A δ:=by
  have one (d:ℕ):1≤factor d:=le_max_left _ _
  refine WilsonOriginalSparseFiledProbe.original M w grades x B σ b p g s v o tube source target A δ
    layout tape legal stock positive wallet resident site m (fun e r=>factor (e+pole₀)*localFee e r)
    (fun e r=>mul_nonneg (zero_le_one.trans (one _)) (nonnegative e r)) ε eps ?_ ?_ total
    width room radius held H β thermal dated small side tax reserve begun quote
  · intro e live
    exact (unit e live).trans (le_mul_of_one_le_left (nonnegative e 0) (one _))
  · intro e live r _ hcap z keep
    exact (WilsonOriginalSparsePegReading.entry M x grades s layout tape legal stock positive
      ⟨v,resident⟩ e r hcap z (localFee e r) (nonnegative e r) (nodes e live r (by assumption) hcap z keep)).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (nonnegative e r))

end YM.Integration.WilsonOriginalSparseFiledNodes
end
