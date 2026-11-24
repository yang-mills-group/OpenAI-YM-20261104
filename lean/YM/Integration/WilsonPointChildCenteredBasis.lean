import YM.Integration.WilsonPointChildCenteredSalary
import YM.Integration.WilsonPointChildDigitIncome
import YM.Integration.WilsonPointChildNamedSalary
import YM.Integration.WilsonPointChildPairedHistory
import YM.Integration.WilsonPointChildFoldedField
import YM.Integration.WilsonPointChildDigitReturn
import YM.Integration.WilsonPointChildDigitLedger
import YM.Integration.WilsonPointChildHalfCell
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPointChildCenteredBasis
open Function Filter Finset Matrix Lattice Wilson RG Laurent PowerSeries Work.F08
open FormalBulk08 Flat Reef Jets Orb Wick Stationary Series Shore Gorge Lotus Mesa Rift Lava Dawn Kemp Roof Sierra Rial
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Power
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Winding
open YM Next.Foundations PhysicalNext.Repeat.Legato Pose Palm Quire Wine Dove WilsonCoeffUV.Embroider
open WilsonPointChildTestCoordinates WilsonNeutralPointCourse WilsonPointChildCoverStep
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge}{d D:ℕ}
open WilsonCoeffUV.Wheel WilsonCoeffUV.Embroider.Canvas
open WilsonPointChildTestJet WilsonPointChildTestCoordinates WilsonCoeffUV.Wheel.Mark
variable {ι:Type}

open WilsonPointChildNamedBasis

def slide (D:ℕ)(z:Pier)(t:Spring D):Scroll D:=scroll (WilsonPointChildCenteredJet.shape D z t)
theorem restored (D:ℕ)(z:Pier)(t:Spring D):physical (slide D z t)=portrait D (WilsonPointChildCenteredJet.shape D z t):=physical_scroll _
def mark (h:ι → ℕ)(s:ι)(t:Spring (h s))(c:Chamber):ℝ →L[ℝ] Pen h {s}:=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (petal h s (claim (h s) (finger (paper_fits t)) c))
theorem tested (h:ι → ℕ)(s:ι)(t:Spring (h s))(c:Chamber)(V:Case h)(x:ℝ):
    touch V {s} (mark h s t c x)=x*(claim (h s) (finger (paper_fits t)) c (V s)):=by
  change (touch V {s}) (x • petal h s (claim (h s) (finger (paper_fits t)) c))=_
  rw [map_smul,petal_hit,smul_eq_mul]
theorem small (h:ι → ℕ)(s:ι)(t:Spring (h s))(c:Chamber):‖mark h s t c‖≤1:=by
  let eval:=claim (h s) (finger (paper_fits t)) c
  have fee:‖eval‖≤1:=ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun p=>by rw [one_mul];change ‖p.val (finger (paper_fits t)) c‖≤‖p‖;exact registry p _ _
  have charge:‖petal h s eval‖≤1:=((petal h s).le_opNorm _).trans (mul_le_one₀ (petal_bound h s) (norm_nonneg _) fee)
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖x • petal h s eval‖≤_
  rw [norm_smul,one_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) charge
def nodes (R:Run G)(digit:∀i,Site (R.family.S.block i))(N j:ℕ):Pier:=WilsonPointChildTestSupport.points R digit (N-j) j
def samples (R:Run G)(digit:∀i,Site (R.family.S.block i))(N j:ℕ):Chamber:=WilsonPointChildAddress.seat R digit (N-j) j

end YM.Integration.WilsonPointChildCenteredBasis
