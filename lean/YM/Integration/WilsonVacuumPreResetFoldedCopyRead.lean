import YM.Integration.WilsonVacuumPreResetFoldedCopyMoments

/-! Fixed-cutoff copy limit for the complete held-field difference. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetFoldedCopyRead
open AllOrder AllOrder.Floe AllOrder.Floe.Step
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration Pace Aero StateE
open scoped Classical Topology BigOperators

open Primitives.TwoWave Primitives.TwoWave.RealSlice
open Kinetic.Port PhysicalNext.Repeat.Legato FVA1Physical.MixedResets
open RG.Supply Push.PriceCompiler AbsoluteSums ConnectedActivityE6
open PhysicalNext PhysicalNext.Repeat ThroughLaunch Pane
open Bid Org Further.PhysicalPeriodLimitF933 Shingle Aero Comparison.RG02

open WilsonVacuumPreResetTorusRegister WilsonVacuumPreResetTorusMaterial
open Comparison.RG02.Order Next.SectorChange Marker Exterior
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonVacuumPreResetTorusSeason WilsonVacuumPreResetTorusMoment
open WilsonVacuumPreResetTorusSeasonMoments
open WilsonVacuumPreResetTorusActionRead (originalAction corrected)
open WilsonVacuumPreResetTorusGrade (evaluated)
open FVA1Physical.TwoReset (Covers coverFilter coverWin)
open WilsonCoeffUV.Winding
open WilsonVacuumPreResetTorusCoverAction (Cover sheets)
variable {G:Gauge}(R:Run G)

open WilsonVacuumPreResetTorusGrade (evaluated)
open WilsonVacuumPreResetFoldedCopyMoments (difference)

theorem original (simple:G.Simple){N m:ℕ}(hm:m<N)(t:ℕ)(c:Side)(z w:rule (Coarse G) c):
    let A:=R.family.path.levels
    let Ñ:=R.metals.O
    Tendsto (fun p:Cover R m c=>
      let n:=R.family.side m p.val
      let dz:=convey (coverWin p.prop) z
      let dw:=convey (coverWin p.prop) w
      (sheets R m c p:ℝ)⁻¹ •
        (((evaluated (coil0 A Ñ m N n) t dz-evaluated (coil0 A Ñ m N n) t dw)-
          (evaluated (originalAction R N m n) t dz-evaluated (originalAction R N m n) t dw):ℝ):ℂ))
        (coverFilter R.family.S m c) (𝓝 0):=by
  classical
  dsimp only
  let A:=R.family.path.levels
  let Ñ:=R.metals.O
  let n (p:Cover R m c):=R.family.side m p.val
  let M (p:Cover R m c):=(sheets R m c p:ℝ)⁻¹
  let Z (p:Cover R m c):=convey (coverWin p.prop) z
  let W (p:Cover R m c):=convey (coverWin p.prop) w
  let F (p:Cover R m c):=coil0 A Ñ m N (n p)
  let H (p:Cover R m c):=originalAction R N m (n p)
  let V (l:ℕ)(p:Cover R m c)(x:rule (Coarse G) (n p)):ℂ:=
    ((MvPolynomial.eval x (Blue.paint (l+1) (difference R N m t l (n p))):ℝ):ℂ)
  have each (l:ℕ):Tendsto (fun p:Cover R m c=>M p • (V l p (Z p)-V l p (W p)))
        (coverFilter R.family.S m c) (𝓝 0):=by
    have zlim:=WilsonVacuumPreResetFoldedCopyMoments.purchase R simple hm t l c z
    have wlim:=WilsonVacuumPreResetFoldedCopyMoments.purchase R simple hm t l c w
    simpa only [smul_sub,sub_zero] using zlim.sub wlim
  have sum:Tendsto (fun p:Cover R m c=>∑l∈Finset.range (t+2),
      M p • (V l p (Z p)-V l p (W p))) (coverFilter R.family.S m c) (𝓝 0):=by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum (Finset.range (t+2)) (fun l _=>each l)
  apply sum.congr' (Eventually.of_forall ?_)
  intro p
  have co:shellK 2 (F p):=winter_band _ _ _ _ _ (RunFormalChain.fromRun R).receipt
    (emera_far A simple (RunFormalChain.fromRun R).receipt (Nat.succ_le_of_lt hm) _).1
  have real:shellK 2 (H p):=WilsonVacuumPreResetTorusGrade.original R simple hm (n p)
  change ∑l∈Finset.range (t+2),M p • (V l p (Z p)-V l p (W p))=
    M p • (((evaluated (F p) t (Z p)-evaluated (F p) t (W p))-
       (evaluated (H p) t (Z p)-evaluated (H p) t (W p)):ℝ):ℂ)
  rw [←Finset.smul_sum,WilsonVacuumPreResetTorusGrade.positive _ co,
    WilsonVacuumPreResetTorusGrade.positive _ real,←Finset.sum_sub_distrib,Complex.ofReal_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  simp only [V,difference,Pi.sub_apply,map_sub,Complex.ofReal_sub,F,H]
  ring

end YM.Integration.WilsonVacuumPreResetFoldedCopyRead
