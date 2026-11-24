import YM.Integration.WilsonOriginalCensusAngularFace
import YM.Integration.WilsonOriginalCensusTariffDate

/-! A signed finite angular table on the genuine two submitted prints. Its debit and
highest pole₀ are fixed by the physical grades, restored source income and requested
accuracy before choosing either Taylor degree. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusFiledProbe
open Finset Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene QuadraticLocal.Sunrise
open AllOrder AllOrder.Floe Laurent Comparison.RG02 Comparison.Density Comparison.Density.Mirrors
open Transport AnalyticBridge.SectorAffine.Offset WilsonEmittedWordJointFare WilsonEmittedCutGrouping
open WilsonEmittedFiledCatalogue Push.AbsoluteSums WilsonOriginalCensusPhysicalLoad
open scoped BigOperators ContDiff Classical Matrix.Norms.Frobenius

variable {G:Gauge}{n:Side}{V:Type}[Fintype V][DecidableEq V]{Γ:Census V}
  {I X:Bool→Type}{P:Bool→Passport n V}(M:(a:Bool)→I a→Row (P a) Γ G (X a))
  (w:Bool→V→ℝ)(grades:Bool→V→ℕ)(x:(a:Bool)→X a)
  (B:BudgetPoint)(σ b:Bool→ℝ)(p:Bool→ℕ)(g:ℝ)
  (s:Multi.Hot Γ)(v:V)(o:Site n)(tube:LinkTube G)
  (source target:ℕ)(A δ:ℝ)
def posted (A:ℝ)(D:ℕ):ℝ:=A*(2+((2:ℝ)^(D+1)*WilsonEmittedGrossTariff.fixedCost)*2^(D+219)*Real.exp 1)
local notation "D₀" => WilsonOriginalCensusPhysicalLoad.rank grades
local notation "pole₀" => WilsonOriginalCensusPhysicalLoad.head grades s.val
local notation "lag" => WilsonOriginalCensusPhysicalLoad.delay grades s.val
local notation "debt" => WilsonOriginalCensusTariff.debit source D₀
local notation "height" => pole₀+debt+target
local notation "sig" => (fun a=>WilsonEmittedCompactTariff.strip (σ a))

structure Reading where
  layout : Bool→Layout G
  tape : Bool→Finset Age
  legal : ∀a,Legal (tape a) (layout a)
  ε : ℝ
  tolerance : 0 ≤ ε
  entries : ∀e,e+pole₀<3*height → ((e+pole₀).factorial:ℝ)*
    WilsonEmittedAngularJointFare.mass (WilsonNeutralTwoPrintAccount.entry M x grades s layout tape e) (e+pole₀) ≤ ε
  home : ∀a,(P a).origin v=o
  small : g ≤ 1/2
  width : ℝ
  room : Room B n tube B.B width
  radius : 0 ≤ width
  held : width ≤ 2*g^(1/2:ℝ)
  hat : ℝ
  beta : ℝ
  thermal : hat/2 ≤ beta ∧ beta ≤ 2*hat
  atDate : g=(Real.sqrt beta)⁻¹
  side : B.B=Nat.ceil ((Real.log hat)^2)
  tax : B.supportExponent+2 ≤ 102
  reserve : ∀a,Real.exp ((σ a)⁻¹^2) ≤ hat
  begun : WilsonOriginalCensusTariffDate.Begun tube (Fintype.card V) D₀ (3*height) height p lag hat
  quote : ((g^pole₀)⁻¹*(groupPrice tube 0*((2*height:ℕ):ℝ)*((3*height:ℕ):ℝ)))*ε+
    (WilsonEmittedOutputPower.constant height+1)*(posted A D₀)*g^target ≤ δ

def purchased (q:Reading M grades x B σ p g s v o tube source target A δ)(positive:∀a,0<σ a)
    (salary:∀a,0 ≤ b a)(wallet:∀a v,0<w a v)(Ap:0 ≤ A)
    (income:WilsonEmittedJoinedFares.cash s.val w (fun a=>if a then -1 else 1) b ≤ A*(g^source)⁻¹):
    WilsonOriginalCensusAngularFace.Probe M w grades x B σ b sig p (fun _=>Fintype.card V)
      (fun _=>D₀) g s v o tube δ:=by
  let d:=q.begun
  have hi:1<q.hat:=d.1
  have beta:0<q.beta:=lt_of_lt_of_le (by linarith:q.hat/2>0) q.thermal.1
  have gp:0<g:=q.atDate ▸ inv_pos.mpr (Real.sqrt_pos.mpr beta)
  have fare:=WilsonOriginalCensusTariff.original tube B s.val w (fun a=>if a then -1 else 1)
    grades lag p b σ source (3*height) hi d.2.1 gp (q.small.trans (by norm_num)) beta
    q.thermal.1 q.thermal.2 q.atDate q.side q.tax (fun a=>Poly.worth (wallet a) s.val)
    salary positive q.reserve d.2.2.2.1 (WilsonOriginalCensusTariffDate.fits G (Fintype.card V) D₀ (3*height) p lag)
    d.2.2.2.2 Ap income
  exact ⟨pole₀,debt,target,height,rfl,lag,cleared grades s.val,
    q.layout,q.tape,q.legal,q.ε,q.tolerance,q.entries,q.home,q.small,3*height,le_rfl,
    q.width,q.room,q.radius,q.held,q.hat,q.beta,zero_lt_one.trans hi,beta,q.thermal.2,q.atDate,
    q.side,q.tax,(fun _=>le_rfl),q.reserve,d.2.2.1,posted A D₀,fare.1,fare.2.1,fare.2.2,q.quote⟩

end YM.Integration.WilsonOriginalCensusFiledProbe
end
