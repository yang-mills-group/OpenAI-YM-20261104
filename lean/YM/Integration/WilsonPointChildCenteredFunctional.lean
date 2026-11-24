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
namespace YM.Integration.WilsonPointChildCenteredFunctional
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
def issue (R:Run G)(u:G.ColorIndex)(k:ℕ)(h:ι → ℕ)(s:ι)(depth:k<h s)(digit:∀i,Site (R.family.S.block i))(N j:ℕ)
    (v:Letter (R.family.labels.level k)):Era G (Pen h {s}):=
  ∑t:Spring (h s),tuftV (mark h s t (samples R digit N j)) (WilsonPointChildDigitLedger.ledger R u depth digit N (N-j) j v (slide (h s) (nodes R digit N j) t))

section
variable (R:Run G)(u:G.ColorIndex)(k:ℕ)(h:ι → ℕ)(s:ι)(depth:k<h s)(digit:∀i,Site (R.family.S.block i))(o:Loc G 1)

include o in
theorem original (simple:G.Simple)(price:ℕ → Gear G → ℝ)(paid:FundedMarkedCoverRows.prices price R.kit)
    (tags:∀i n,(Flat.primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)
    (N j:ℕ)(live:j≤N)(up:k≤R.family.path.levels.clock.J j)
    (v:Letter (R.family.labels.level k))(e r:ℕ)(x:chain (edgeL G) r)(V:Case h):
    let Y:=WilsonNeutralPointCourse.filed R (routes R) u depth digit N j v
    touch V {s} ((issue R u k h s depth digit N j v).2 e r x)=Y (WilsonPointChildCenteredJet.extend (h s) (nodes R digit N j) (samples R digit N j) (V s)) e r x:=by
  intro Y
  let F:=R.family.path.levels
  have enough:∀a:ℕ,j ≤ a → a<N → k≤F.clock.J (a+1):=fun a hj _=>up.trans (F.fits.mono (by omega))
  let Z(t:Spring (h s)):=WilsonPointChildDigitLedger.ledger R u depth digit N (N-j) j v (slide (h s) (nodes R digit N j) t)
  have same(t:Spring (h s)):(Z t).2=Y (portrait (h s) (WilsonPointChildCenteredJet.shape (h s) (nodes R digit N j) t)):=by
    have first:=WilsonPointChildDigitLedger.covered R u depth digit tags simple o price paid N (N-j) j (by omega) v (slide (h s) (nodes R digit N j) t)
    have out:=WilsonPointChildDigitReturn.original R u depth digit simple o N (N-j) j (by omega) enough v (slide (h s) (nodes R digit N j) t)
    exact first.trans (out.trans (congrArg Y (WilsonPointChildCenteredBasis.restored _ (nodes R digit N j) _)))
  have court:=WilsonNeutralPointCourse.original R (routes R) u depth digit N j simple o live
    (up.trans (F.fits.mono (Nat.le_succ _)))
  let read:=WilsonPointChildCoveredTariff.linear Y (court.officers v).toIsLinearMap e r x
  change touch V {s} ((∑t:Spring (h s),tuftV (mark h s t (samples R digit N j)) (Z t)).2 e r x)=read (WilsonPointChildCenteredJet.extend (h s) (nodes R digit N j) (samples R digit N j) (V s))
  rw [Prod.snd_sum]
  simp only [Finset.sum_apply,map_sum]
  change ∑t:Spring (h s),touch V {s} (mark h s t (samples R digit N j) ((Z t).2 e r x))=read (WilsonPointChildCenteredJet.extend (h s) (nodes R digit N j) (samples R digit N j) (V s))
  rw [show WilsonPointChildCenteredJet.extend (h s) (nodes R digit N j) (samples R digit N j) (V s)=∑t:Spring (h s),claim (h s) (finger (paper_fits t)) (samples R digit N j) (V s) • portrait (h s) (WilsonPointChildCenteredJet.shape (h s) (nodes R digit N j) t) from by simp only [WilsonPointChildCenteredJet.extend,_root_.sum_apply,ContinuousLinearMap.smulRight_apply]]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [WilsonPointChildCenteredBasis.tested,same, map_smul,smul_eq_mul,mul_comm]
  rfl

end
open WilsonPointChildFiledPress WilsonPointChildCoveredTariff
open WilsonCoeffUV.Shard WilsonCoeffUV.Bank.Mosaic
def factor (h:ι → ℕ)(s:ι):ℝ:=∑t:Spring (h s),WilsonPointChildCenteredSalary.bill t

theorem factor_nonneg (h:ι → ℕ)(s:ι):0≤factor h s:=Finset.sum_nonneg fun t _=>WilsonPointChildCenteredSalary.nonnegative t
def seat (R:Run G)(u:G.ColorIndex)(k:ℕ)(h:ι → ℕ)(s:ι)(depth:k<h s)(digit:∀i,Site (R.family.S.block i))(N j:ℕ)
    (v:Letter (R.family.labels.level k))(z:Cover):Era G (Pen h {s}):=
  ∑t:Spring (h s),tuftV (mark h s t (samples R digit N j)) (shifted (WilsonPointChildDigitLedger.ledger R u depth digit N (N-j) j v (slide (h s) (nodes R digit N j) t)) z)

theorem authorized (R:Run G)(simple:G.Simple)(o:Loc G 1)(u:G.ColorIndex)(k:ℕ)(h:ι → ℕ)(s:ι)(depth:k<h s)
    (digit:∀i,Site (R.family.S.block i))(N j:ℕ)(live:j≤N)(v:Letter (R.family.labels.level k))(z:Cover):Auth k (seat R u k h s depth digit N j v z):=by
  apply Auth.sum
  intro t _
  exact ((WilsonPointChildDigitLedger.honest R u depth digit simple o N (N-j) j (by omega) v (slide (h s) (nodes R digit N j) t)).shifted z).tuft _

theorem priced (R:Run G)(simple:G.Simple)(booked:WilsonPointChildFiledTest.Filed R)
    (u:G.ColorIndex)(k:ℕ)(h:ι → ℕ)(s:ι)(depth:k<h s)(o:Loc G 1)
    (tags:∀i n,(Flat.primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)
    (price:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices price R.kit)(E:ℕ){η:ℝ}(pos:0<η):
    ∀ᶠj:ℕ in atTop,∀N,j≤N→∀digit:∀i,Site (R.family.S.block i),∀v:Letter (R.family.labels.level k),∀y:ι → Cover,∀e≤E,∀r,
      Wig terrain y (width R j) ((R.family.path.levels.clock.hatBeta j)^η*factor h s)
        {s} ((seat R u k h s depth digit N j v (y s)).2 e r):=by
  filter_upwards [WilsonPointChildDigitIncome.original R simple booked u depth o tags price funded E pos,(WardBin.bell R.family.path.levels simple).eventually_ge_atTop 1] with j full steady
  intro N live digit v y e he r
  have positive:0≤width R j:=((Primer.FamilyWindow R.family).pos _).le
  let Q:ℝ:=(R.family.path.levels.clock.hatBeta j)^η
  have each (t:Spring (h s)):let X:=WilsonPointChildDigitLedger.ledger R u depth digit N (N-j) j v (slide (h s) (nodes R digit N j) t)
      Wig terrain y (width R j) (Q*(‖mark h s t (samples R digit N j)‖*‖physical (slide (h s) (nodes R digit N j) t)‖)) {s}
        ((tuftV (mark h s t (samples R digit N j)) (shifted X (y s))).2 e r):=by
    intro X
    have atZero:=WilsonPointChildNamedSalary.rooted positive ((full N live digit v (slide (h s) (nodes R digit N j) t)).2 e he r).1
    have paid:Wig terrain y (width R j) (Q*‖physical (slide (h s) (nodes R digit N j) t)‖) {s} ((shifted X (y s)).2 e r):=
      abreast _ y s (Cork.turn _ atZero) positive
    refine ⟨?_,?_⟩
    · rw [←mul_left_comm];exact mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) paid.1
    · intro x
      change ‖mark h s t (samples R digit N j) _‖≤_
      calc _ ≤ ‖mark h s t (samples R digit N j)‖*‖(shifted X (y s)).2 e r x‖:=(mark h s t (samples R digit N j)).le_opNorm _
           _ ≤ ‖mark h s t (samples R digit N j)‖*((Q*‖physical (slide (h s) (nodes R digit N j) t)‖)*_):=mul_le_mul_of_nonneg_left (paid.2 x) (ContinuousLinearMap.opNorm_nonneg _)
           _ = _:=by ring
  have uniform(t:Spring (h s)):= (each t).more (mul_le_mul_of_nonneg_left
    (show ‖mark h s t (samples R digit N j)‖*‖physical (slide (h s) (nodes R digit N j) t)‖≤WilsonPointChildCenteredSalary.bill t from by
      rw [WilsonPointChildCenteredBasis.restored]
      exact (mul_le_of_le_one_left (norm_nonneg _) (WilsonPointChildCenteredBasis.small _ _ _ _)).trans (WilsonPointChildCenteredSalary.bound _ _))
    (Real.rpow_pos_of_pos (zero_lt_one.trans_le steady) _).le)
  dsimp only [seat]
  rw [Prod.snd_sum]
  simp only [Finset.sum_apply]
  simpa only [factor, Finset.mul_sum] using Wig.sum (Z:=univ) (fun t _=>uniform t)
end YM.Integration.WilsonPointChildCenteredFunctional
