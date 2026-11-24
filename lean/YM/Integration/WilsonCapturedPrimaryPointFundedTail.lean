import YM.Integration.WilsonCapturedPrimaryPointStage
import YM.Integration.WilsonCapturedPrimaryPointRectangle

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryPointFundedTail
open Filter Function Finset Lattice Laurent Wilson RG Precision FormalBulk08
open Next.Free Flat Stationary Kemp Pose Gorge Reef Mesa Exterior
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open PhysicalNext.Repeat.Legato Next.Foundations RG16 RG16.Literal RG16.Guarding
open Pert.Asymptotics Trace.Physical WilsonCapturedPrimaryPointBasis WilsonPointChildFiledPress
open scoped Classical BigOperators Topology ENNReal
variable {G:Gauge}{d D:ℕ}

theorem original (R:Run G)(L:Primer.Families R.family)(a:G.ColorIndex)(depth:d<D)
    (simple:G.Simple)(funded:WilsonPointChildFiledTest.Filed R){u:ℕ→ℕ}
    (announced:WilsonWindowFormalPurchase.Canonical u R.kit)(o:Loc G 1)
    (Q r:ℕ)(row:(R.family.labels.level d).Index):
    ∀ᶠi:ℕ in atTop,∀N per:ℕ,i≤N→∀t:Tour R i,∀c:(R.family.labels.level d).Index,∀e≤Q,
      let F:=R.family.labels.level d
      let Z:=WilsonOlderFreshPointGauge.field R L a depth i (axis F c) (t,fixed D)
      |pearlJ F (Z e r) row|≤((regulatorRun R.family N per i)⁻¹)^3:=by
  let F:=R.family.labels.level d
  let s:=d*(F.grades row).2
  obtain ⟨C,C0,read⟩:=WilsonPhysicalProjectionHolonomyPrice.entered F o (axis F row) r
  obtain ⟨_,_,income⟩:=WilsonCapturedPrimaryPointFiledWindow.original R L a depth simple funded
    o Q r row (η:=1) zero_lt_one
  let A:=C*(2*‖fixed D‖)
  have A0:0≤A:=by dsimp only [A];positivity
  have cost:=WilsonPhysicalProjectionFiledCover.width_charge R simple announced s 0 A0 zero_lt_one
  filter_upwards [income,cost,(Next.Rank.Station.hat_rate R.family.path.levels simple).eventually_ge_atTop (2:ℝ)]
    with i paid widthBill warm
  intro N per here t c e he _ Z
  let w:=width R i
  let g:=regulatorRun R.family N per i
  let β:=R.family.path.β N per i
  have wp:0<w:=(Primer.FamilyWindow R.family).pos _
  have band:=(R.makes.wilson.represents N per i here).band.1
  change R.family.path.levels.clock.hatBeta i/2≤β at band
  have bp:0<β:=by linarith only [band,warm]
  have gp:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr bp)
  have hi:(g⁻¹)^2=β:=by change (((Real.sqrt β)⁻¹)⁻¹)^2=β;rw [inv_inv,Real.sq_sqrt bp.le]
  have large:R.family.path.levels.clock.hatBeta i≤2*(g⁻¹)^2:=by rw [hi];linarith only [band]
  have small:w⁻¹≤2*(WilsonPhysicalHistoryAperture.width R.family i)⁻¹:=by
    change w⁻¹≤2*w⁻¹;linarith only [inv_pos.mpr wp]
  have fixedCharge:=widthBill N per here w wp small
  have pack:widthCost w s*A≤g⁻¹:=by simpa only [pow_zero,mul_one,Real.rpow_neg_one] using fixedCharge
  have weight:0≤widthCost w s:=by unfold widthCost;positivity
  have heard:=read w wp (Z e r) _ (paid t c e he).1
  calc
    _ ≤ C*widthCost w s*(R.family.path.levels.clock.hatBeta i*‖fixed D‖):=by
      rw [Real.rpow_one] at heard
      exact heard
    _ ≤ C*widthCost w s*((2*(g⁻¹)^2)*‖fixed D‖):=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right large (norm_nonneg _)) (mul_nonneg C0 weight)
    _ = (widthCost w s*A)*(g⁻¹)^2:=by dsimp [A];ring
    _ ≤ g⁻¹*(g⁻¹)^2:=mul_le_mul_of_nonneg_right pack (sq_nonneg _)
    _ = (g⁻¹)^3:=by ring

end YM.Integration.WilsonCapturedPrimaryPointFundedTail
