import YM.Integration.WilsonPositionProgramTrialPublicJointGroundBirth

/-! A scalar series follows the genuine old-vacuum reversion openLaw every blocking step. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointGroundSuspension
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels XSpace
open WilsonSurveyedEquationFrameInlet (bank master loan price)
open WilsonIndependentMatchedFiledIncome (plate charge)
open WilsonMarkedIndependentNormalizedElection (deck)
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G) (W : Initialize G) {h hi D k u e : ℕ}
local notation "L" => R.family.path.levels
local notation "O" => R.metals.O
local notation "CC" => Credit.leanC


open WilsonIndependentMatchedReportedProxy (sectionSeal)
open WilsonIndependentMatchedFreshWhole (projected)
open WilsonPositionProgramTrialReverseLens (received)
open WilsonPositionProgramTrialFittedLens (matrix)
open WilsonPositionProgramTrialPublicJointCapFiling (sectionAt)
open WilsonSurveyedEquationFrameStability (course)

open WilsonPositionProgramTrialPublicJointCapArrival (high own linear)


open PowerSeries Matrix WilsonCoeffUV.Bank.Carp

open WilsonPositionProgramTrialPublicJointGroundBirth (accrued)

theorem traveled (A:Levels G)(O':ChartRatio G)(simple:G.Simple)(valid:LocalRatio O')
    (N k h m j:ℕ)(before:m+j≤N)(f:Cost)(P:TowerS G D)(openLaw:On k P):
    spools A O' N k h m j (Stem f P)=
      Stem (reel (relativeF A O' N m j) f) (spools A O' N k h m j P):=by
  induction j generalizing f P with
  | zero =>
    change Stem f P=Stem (reel 1 f) P
    rw [reel_one]
  | succ j ih =>
    have here:m+j<N:=by omega
    rw [spools,resonated A O' P f openLaw here simple valid,ih (by omega) _
      _ (ShedG A O' (h:=h) here simple valid openLaw le_rfl)]
    change Stem ((reel (relativeF A O' N m j)).comp (reel (ratioHigh A O' N (m+j))) f) _=_
    rw [reel_chart]
    rfl

theorem stamped (F:Frame G h)(P:TowerS G D)(openLaw:On k P)(f:Cost):
    opal F (Stem f P)=fun i=>f*opal F P i:=by
  funext i
  ext1 a
  rw [PowerSeries.coeff_mul]
  simp only [opal,PowerSeries.coeff_mk,Stem]
  exact glean_stake F P.2 (solo_stretch openLaw) f a i

theorem read (simple:G.Simple)(valid:LocalRatio R.metals.O)(fit:h<D)(m K N k:ℕ)(before:m≤K)(upper:K≤N)
    (P:TowerS G D)(openLaw:On k P)(f:Cost)(i:Alma (R.family.labels.level h)):
    accrued R fit m K N k (Stem f P) i=reel (relativeF L O N m (K-m)) f*accrued R fit m K N k P i:=by
  have ages:m+(K-m)≤N:=by omega
  unfold accrued
  rw [traveled L O simple valid N k h m (K-m) ages f P openLaw]
  rw [stamped _ _ (spoolEnd ages simple valid openLaw)]
  unfold matrix
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _=>?_
  simp only [Algebra.smul_def]
  ring

theorem clear (simple:G.Simple)(valid:LocalRatio R.metals.O)(fit:h<D)(m K N k:ℕ)(before:m≤K)(upper:K≤N)
    (P:TowerS G D)(openLaw:On k P)(u:ℝ)(r q:ℕ)(i:Alma (R.family.labels.level h)):
    coeff (q+r) (accrued R fit m K N k (Stem (PowerSeries.C u*PowerSeries.X^r) P) i)=
      u*coeff q ((relativeF L O N m (K-m))^r*accrued R fit m K N k P i):=by
  let B:=relativeF L O N m (K-m)
  let E:=accrued R fit m K N k P i
  rw [read R simple valid fit m K N k before upper P openLaw]
  change coeff (q+r) (reel B (PowerSeries.C u*PowerSeries.X^r)*E)=_
  rw [map_mul (reel B),map_pow (reel B),reel_C,reel_X,mul_pow]
  rw [show PowerSeries.C u*(B^r*PowerSeries.X^r)*E=PowerSeries.X^r*(PowerSeries.C u*(B^r*E)) by ring]
  simp [PowerSeries.coeff_X_pow_mul',B,E]

theorem leading (simple:G.Simple)(valid:LocalRatio R.metals.O)(fit:h<D)(m K N k:ℕ)(before:m≤K)(upper:K≤N)
    (P:TowerS G D)(openLaw:On k P)(u:ℝ)(r:ℕ)(i:Alma (R.family.labels.level h)):
    coeff r (accrued R fit m K N k (Stem (PowerSeries.C u*PowerSeries.X^r) P) i)=
      u*coeff 0 (accrued R fit m K N k P i):=by
  have unit:constantCoeff (relativeF L O N m (K-m))=1:=angularF simple valid (by omega)
  simpa only [Nat.zero_add,coeff_zero_eq_constantCoeff_apply,map_mul,map_pow,unit,one_pow,one_mul] using
    clear R simple valid fit m K N k before upper P openLaw u r 0 i

end YM.Integration.WilsonPositionProgramTrialPublicJointGroundSuspension
