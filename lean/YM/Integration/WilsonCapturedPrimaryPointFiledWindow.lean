import YM.Integration.WilsonCapturedPrimaryPointPeriodic
import YM.Integration.WilsonPointChildFiledTest
import YM.Integration.WilsonPointChildCoveredCut

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryPointFiledWindow
open Function Filter Finset Lattice Laurent Wilson Exterior Stationary Source Source.Drops
open FormalBulk08 FormalBulk08.Lava FormalBulk08.Lotus FormalBulk08.Mesa FormalBulk08.Gorge
open FormalBulk08.Reef FormalBulk08.Orb FormalBulk08.Shore FormalBulk08.Kemp FormalBulk08.Rift FormalBulk08.Pose
open Planned.PrimaryIntegral295 Place Carrier Film Labels Next.Foundations
open PhysicalNext.Repeat.Legato
open WilsonCapturedPrimaryPointBasis WilsonCapturedPrimaryPointWindow WilsonPointChildFiledPress
open scoped Classical Topology BigOperators ENNReal
variable {G:Gauge} {d D:ℕ}

theorem original (R:Run G)(L:Primer.Families R.family)(a:G.ColorIndex)(depth:d<D)
    (simple:G.Simple)(funded:WilsonPointChildFiledTest.Filed R)
    (o:Loc G 1)(Q r:ℕ)(row:(R.family.labels.level d).Index){η:ℝ}(eta:0<η):
    ∃K:ℝ,0≤K ∧ ∀ᶠi:ℕ in atTop,∀t:Tour R i,∀c:(R.family.labels.level d).Index,∀e≤Q,
      let F:=R.family.labels.level d
      let Z:=WilsonOlderFreshPointGauge.field R L a depth i (axis F c) (t,fixed D)
      let w:=width R i
      let fee:=(R.family.path.levels.clock.hatBeta i)^η*‖fixed D‖
      Knoxville (fame _) w (0,o) (Z e r) fee ∧ ∀n:Side,∀B:ℕ,2*B<n.val →
        |quote F B (sieve n (Z e r)) (axis F row)-pearlJ F (Z e r) row|≤
        K*(widthCost (w/2/2) (d*(F.grades row).2)+widthCost (w/2) (d*(F.grades row).2))*
        (fee*Real.exp (-w*(B:ℝ)/2)):=by
  let F:=R.family.labels.level d
  obtain ⟨K,hK,bill⟩:=WilsonCapturedPrimaryPointPeriodic.original F o (axis F row) r
  refine ⟨K,hK,?_⟩
  have reach:=R.family.path.levels.fits.deep.eventually (eventually_ge_atTop d)
  filter_upwards [funded L a depth o Q eta,reach] with i haveWallet awake
  intro t c e he _ Z w fee
  have court:=WilsonNeutralPointCourse.original R L a depth t.digit t.cutoff i simple o t.live
    (awake.trans (R.family.path.levels.fits.mono (Nat.le_succ _)))
  have charged:Knoxville (fame _) w (0,o) (Z e r) fee:=
    ((haveWallet t.cutoff t.live).1 t.digit).every court (axis F c) (fixed D) e he r
  refine ⟨charged,?_⟩
  intro n B fit
  have wp:0<w:=(Primer.FamilyWindow R.family).pos _
  have cut:=WilsonPointChildCoveredCut.cut (B:ℝ) wp.le charged
  have tail:Knoxville (fame _) (w/2) (0,o)
      (fun v=>if B≤herb (fame _) (0,o) v then Z e r v else 0)
      (fee*Real.exp (-w*(B:ℝ)/2)):=by
    have layer:WilsonPointChildCoveredCut.outside (fame _) (0,o) (B:ℝ) (Z e r)=
        (fun v=>if B≤herb (fame _) (0,o) v then Z e r v else 0):=by
      funext v
      by_cases h:B≤herb (fame _) (0,o) v
      · have hh:(B:ℝ)≤(herb (fame _) (0,o) v:ℝ):=by exact_mod_cast h
        simp only [WilsonPointChildCoveredCut.outside,if_pos hh,if_pos h]
      · have hh:¬(B:ℝ)≤(herb (fame _) (0,o) v:ℝ):=by exact_mod_cast h
        simp only [WilsonPointChildCoveredCut.outside,if_neg hh,if_neg h]
    rwa [layer] at cut
  exact bill (n:=n) B fit w wp (Z e r) fee _ charged tail

end YM.Integration.WilsonCapturedPrimaryPointFiledWindow
