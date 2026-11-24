import YM.Integration.WilsonPointChildCenteredTensor
import YM.Integration.WilsonPointChildCenteredBasis
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
namespace YM.Integration.WilsonPointChildCenteredSeam
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

open WilsonPointChildNamedBasis WilsonPointChildCenteredBasis
open WilsonCoeffUV.Bank.Carp
open WilsonPointChildCenteredFunctional (issue)
open WilsonMarkedIndependentNormalizedScale (rate)
open Filter
section
variable (R:Run G)(u:G.ColorIndex)(k E:ℕ)(h:ι→ℕ)(s:ι)(depth:k<h s)(o:Loc G 1)
variable (tags:∀i n,(Flat.primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)
include o tags in
theorem original (simple:G.Simple)(price:ℕ→Gear G→ℝ)(paid:FundedMarkedCoverRows.prices price R.kit)
    (finite:WilsonPointChildDigitHierarchy.Filed R):
    ∀ᶠj:ℕ in atTop,∀(digit:∀i,Site (R.family.S.block i)) N per,j≤N →
    ∀(v:Letter (R.family.labels.level k)) e,e≤E → ∀r x,
    let n:=R.family.side j per
    let X:=issue R u k h s depth digit N j v
    ‖X.1 n e r x-plume (X.2 e r) n x‖≤
      (∑t:Spring (h s),(1+WilsonPointChildCenteredSalary.bill t))*rate R.family.path.levels j per:=by
  filter_upwards [finite u k E (h s) depth o tags] with j seam
  intro digit N per live v e enough r x n X
  let p(t:Spring (h s)):=slide (h s) (nodes R digit N j) t
  let Z(t:Spring (h s)):=WilsonPointChildDigitLedger.ledger R u depth digit N (N-j) j v (p t)
  let L(t:Spring (h s)):=mark h s t (samples R digit N j)
  have ready(t):Auth k (Z t):=WilsonPointChildDigitLedger.honest R u depth digit simple o N (N-j) j (by omega) v (p t)
  apply (WilsonPointChildCenteredTensor.finite Z L ready n e r x).trans
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun t _=>?_
  have delta:=seam digit N per live v (p t) e enough r x
  have f:=WilsonPointChildDigitFinite.original R u depth digit tags simple o price paid N (N-j) j (by omega) v (p t) n
  have c:=WilsonPointChildDigitLedger.covered R u depth digit tags simple o price paid N (N-j) j (by omega) v (p t)
  calc
    ‖L t‖*|(Z t).1 n e r x-plume ((Z t).2 e r) n x|≤|(Z t).1 n e r x-plume ((Z t).2 e r) n x|:=
      mul_le_of_le_one_left (abs_nonneg _) (WilsonPointChildCenteredBasis.small _ _ _ _)
    _≤(1+‖physical (p t)‖)*rate R.family.path.levels j per:=by simpa only [Z,f,c] using delta
    _≤_:=mul_le_mul_of_nonneg_right (add_le_add_right (by
      dsimp only [p]; rw [WilsonPointChildCenteredBasis.restored]; exact WilsonPointChildCenteredSalary.bound _ _) _) (Real.exp_pos _).le

include o tags in
theorem physical (simple:G.Simple)(price:ℕ→Gear G→ℝ)(paid:FundedMarkedCoverRows.prices price R.kit)
    (digit:∀i,Site (R.family.S.block i))(N j:ℕ)(live:j≤N)(up:k≤R.family.path.levels.clock.J j)
    (v:Letter (R.family.labels.level k))(e r:ℕ)(x:chain (edgeL G) r)
    (p:Scroll (h s))(V:Case h)(same:V s=page (h s) p):
    touch V {s} ((issue R u k h s depth digit N j v).2 e r x)=
      WilsonNeutralPointCourse.filed R (routes R) u depth digit N j v (physical p) e r x:=by
  rw [WilsonPointChildCenteredFunctional.original R u k h s depth digit o simple price paid tags N j live up v e r x V,same]
  exact congrFun (congrFun (congrFun (WilsonPointChildCenteredJet.original R (routes R) u depth digit N j v p).symm e) r) x

end
end YM.Integration.WilsonPointChildCenteredSeam
