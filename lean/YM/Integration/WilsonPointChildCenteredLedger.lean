import YM.Integration.WilsonPointChildCenteredSeat
import YM.Integration.WilsonPointChildCenteredSeam
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
namespace YM.Integration.WilsonPointChildCenteredLedger
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
open WilsonPointChildCenteredFunctional (issue seat)
open WilsonMarkedIndependentNormalizedScale (rate)
open Bloch
variable {r:ℕ}
open Filter Function
open WilsonPointChildCenteredFunctional (factor factor_nonneg)
open private folded from YM.Integration.WilsonPointChildCenteredTensor

theorem rental (R:Run G)(u:G.ColorIndex)(k E:ℕ)(h:ι→ℕ)(s:ι)(depth:k<h s)(o:Loc G 1)
    (tags:∀i n,(Flat.primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)
    (simple:G.Simple)(price:ℕ→Gear G→ℝ)(paid:FundedMarkedCoverRows.prices price R.kit)
    (booked:WilsonPointChildFiledTest.Filed R){η:ℝ}(pos:0<η):
    ∀ᶠj:ℕ in atTop,∀(digit:∀i,Site (R.family.S.block i)) N,j≤N →
    ∀(v:Letter (R.family.labels.level k)) e,e≤E → ∀r n x z,
    let X:=seat R u k h s depth digit N j v z
    ‖Carp.plume (X.2 e r) n x‖≤(R.family.path.levels.clock.hatBeta j)^η*factor h s:=by
  have age:=WilsonPointChildDigitIncome.original R simple booked u depth o tags price paid E pos
  filter_upwards [age,(WardBin.bell R.family.path.levels simple).eventually_ge_atTop 1] with j earns steady
  intro digit N live v e enough r n x z X
  let p(t:Spring (h s)):=slide (h s) (nodes R digit N j) t
  let Z(t:Spring (h s)):=WilsonPointChildDigitLedger.ledger R u depth digit N (N-j) j v (p t)
  let L(t:Spring (h s)):=mark h s t (samples R digit N j)
  let Y(t:Spring (h s)):=tuftV (L t) (shifted (Z t) z)
  have vr(t):Auth k (Z t):=(earns N live digit v (p t)).1
  have yr(t):Auth k (Y t):=((vr t).shifted z).tuft (L t)
  change ‖Carp.plume ((∑t,Y t).2 e r) n x‖≤_
  rw [folded Finset.univ Y (fun t _=>yr t) n e r]
  simp only [Finset.sum_apply,factor,Finset.mul_sum]
  apply (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _=>?_)
  obtain ⟨w,A,hw,raw⟩:=(((vr t).shifted z).wing e r).land
  change ‖Carp.plume (L t ∘ (shifted (Z t) z).2 e r) n x‖≤_
  rw [Carp.plume_map _ raw hw (L t) n]
  refine ((L t).le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) (WilsonPointChildCenteredBasis.small _ _ _ _)).trans ?_)
  change |Carp.plume (revolve z ((Z t).2 e r)) n x|≤_
  rw [Carp.plume_shift]
  refine ((earns N live digit v (p t)).2 e enough r).2 n _ |>.trans ?_
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (zero_le_one.trans steady) _)
  rw [show physical (p t)=_ from WilsonPointChildCenteredBasis.restored _ _ t]
  exact WilsonPointChildCenteredSalary.bound _ _

end YM.Integration.WilsonPointChildCenteredLedger
