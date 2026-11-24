import YM.Integration.WilsonOriginalSparseFiledRanks

/-! The physical signed aperture is local to an occupied root; the original scored arms fund both remote tails. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalSparseFiledProbe
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

def fare {G:Gauge}{V:Type}[DecidableEq V]{Γ:Census V}(s:Hot Γ)(m e r:ℕ)(d:ℝ)
    (w:Bool→V→ℝ)(σ b:Bool→ℝ)(grades:Bool→V→ℕ):ℝ:=
  if r=0 then d else ((ballCost m*Fintype.card (Loc G 1):ℕ):ℝ)^r*d+
    Real.exp (-((σ false/8)*(m:ℝ)))*(2*(bill G (w false) s (σ false) (b false) (Launch.index Γ (grades false) s.val+1) e r))+
    Real.exp (-((σ true/8)*(m:ℝ)))*(2*(bill G (w true) s (σ true) (b true) (Launch.index Γ (grades true) s.val+1) e r))

def original (layout:Bool→Layout G)(tape:Bool→Finset Age)(legal:∀a,Legal (tape a) (layout a))
    {seats shelf:Bool→ℕ}(stock:∀a,Scene.Armada (M a) (w a) (grades a) (σ a) (b a) (p a) (seats a) (shelf a))
    (positive:∀a,0<σ a)(wallet:∀a i,0<w a i)(resident:v∈s.val.val)(site:∀a,(P a).origin v=o)
    (m:ℕ)(localFee:ℕ→ℕ→ℝ)(nonnegative:∀e r,0≤localFee e r)(ε:ℝ)(eps:0≤ε)
    (unit:∀e, e + pole₀ < 3*height →
      ‖(peek dvd_rfl (M false) (grades false) (layout false) (tape false) (x false) e 0).part s.val-
       (peek dvd_rfl (M true) (grades true) (layout true) (tape true) (x true) e 0).part s.val‖ ≤ localFee e 0)
    (near:∀e, e + pole₀ < 3*height → ∀r:ℕ, 0 < r → r ≤ e + pole₀ → ∀z,
      (∀j,z j∈hull G o m)→‖(entry tape layout e) r z‖ ≤ localFee e r)
    (total:∀e, e + pole₀ < 3*height →((e+pole₀).factorial:ℝ)*
      (∑r∈range (e+pole₀+1),fare (G:=G) s m e r (localFee e r) w σ b grades)≤ε)
    (width:ℝ)(room:Room B n tube B.B width)(radius:0≤width)(held:width≤2*g^(1/2:ℝ))
    (H β:ℝ)(thermal:H/2≤β ∧ β≤2*H)(dated:g=(Real.sqrt β)⁻¹)(small:g≤1/2)
    (side:B.B=Nat.ceil ((Real.log H)^2))(tax:B.supportExponent+2≤102)(reserve:∀a,Real.exp ((σ a)⁻¹^2)≤H)
    (begun:WilsonOriginalCensusTariffDate.Begun tube (Fintype.card V) D₀ (3*height) height p lag H)
    (quote:((g^pole₀)⁻¹*(groupPrice tube 0*((2*height:ℕ):ℝ)*((3*height:ℕ):ℝ)))*ε+
      (WilsonEmittedOutputPower.constant height+1)*(posted A D₀)*g^target≤δ):
    Reading M grades x B σ p g s v o tube source target A δ:=by
  refine ⟨layout,tape,legal,ε,eps,?_,site,small,width,room,radius,held,H,β,thermal,dated,
    side,tax,reserve,begun,quote⟩
  intro e within
  apply le_trans _ (total e within)
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  unfold WilsonEmittedAngularJointFare.mass
  apply sum_le_sum
  intro r hr
  by_cases h:r=0
  · subst r
    simpa [fare] using
      WilsonOriginalSparseFiledRanks.zero M x grades s layout tape e (localFee e 0) (unit e within)
  · have hrpos:=Nat.pos_of_ne_zero h
    have hcap:=Nat.le_of_lt_succ (mem_range.mp hr)
    simpa only [fare,if_neg h] using WilsonOriginalSparseFiledRanks.original M x grades s ⟨v,resident⟩
      layout tape stock positive legal wallet o site m e r hrpos (localFee e r) (nonnegative e r)
        (near e within r hrpos hcap)

end YM.Integration.WilsonOriginalSparseFiledProbe
end
