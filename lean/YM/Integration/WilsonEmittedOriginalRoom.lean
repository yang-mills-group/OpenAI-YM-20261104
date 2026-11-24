import YM.Integration.WilsonEmittedCubeRoom
import YM.Integration.WilsonEmittedLengthWindow
/-! The healthy cube and its physical field size are funded before both regulators. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEmittedOriginalRoom
open Function Lattice RG Wilson Filter Real
open Comparison.Density Comparison.Density.Mirrors Comparison.Density.Transport
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Physical WilsonCoeffUV.Bank.Mosaic
open WilsonEmittedCubeRoom
open scoped Topology BigOperators
variable {G:Gauge} (A:Levels G) (tube : LinkTube G) (simple:G.Simple)

include simple
theorem width_paid {η:ℝ} (pos:0<η) :
    ∀ᶠ i:ℕ in atTop,∀ β:ℝ,A.clock.hatBeta i/2≤β → β≤2*A.clock.hatBeta i →
      width A tube i ≤ 2*((Real.sqrt β)⁻¹)^(1-η) := by
  have Hrise:Tendsto A.clock.hatBeta atTop atTop:=tendsto_atTop_add_const_left _ _
    (A.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  let cash:Credit:=⟨2,12+WilsonEmittedCubeRoom.weight tube,by
    have nn:0≤WilsonEmittedCubeRoom.weight tube:=by unfold WilsonEmittedCubeRoom.weight;positivity [tube.scale]
    linarith⟩
  filter_upwards [exp_at_band cash A simple η pos,(Real.tendsto_log_atTop.comp Hrise).eventually_ge_atTop 1] with i funded age
  intro β low high
  let H:=A.clock.hatBeta i
  have hH:0<H:=zero_lt_one.trans (A.fits.delayed i)
  have hb:0<β:=(half_pos hH).trans_le low
  have u:=Real.sqrt_pos.mpr hb
  have v:=Real.sqrt_pos.mpr hH
  have size:Real.sqrt β≤2*Real.sqrt H:=by
    nlinarith [Real.sq_sqrt hb.le,Real.sq_sqrt hH.le,sq_nonneg (Real.sqrt β-Real.sqrt H)]
  have comp:(Real.sqrt H)⁻¹≤2*(Real.sqrt β)⁻¹:=by
    rw [←one_div,←div_eq_mul_inv];exact (div_le_div_iff₀ v u).mpr (by linarith)
  calc
    _ ≤ A.clock.hatCoupling i*Real.exp (cash.buy (zz A i)):=priced A tube age
    _ ≤ (2*(Real.sqrt β)⁻¹)*((Real.sqrt β)⁻¹)^(-η):=mul_le_mul comp (funded β low) (Real.exp_pos _).le (by positivity)
    _ = _ := by rw [sub_eq_add_neg,Real.rpow_add (inv_pos.mpr u),Real.rpow_one,mul_assoc]

theorem original :
    ∀ᶠ i:ℕ in atTop,∀ per,Room (A.budget i) (A.S.side i per) tube (roof A i) (width A tube i) := by
  have Hrise:Tendsto A.clock.hatBeta atTop atTop:=tendsto_atTop_add_const_left _ _
    (A.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  have small:Tendsto (fun i:ℕ=>2*(A.clock.hatBeta i)^(-(1/4:ℝ))) atTop (𝓝 (2*(0:ℝ))):=
    tendsto_const_nhds.mul ((tendsto_rpow_neg_atTop (by norm_num:0<(1/4:ℝ))).comp Hrise)
  have target:2*(0:ℝ)< min tube.radius 1:=by simpa using lt_min tube.strict zero_lt_one
  filter_upwards [width_paid A tube simple (show 0<(1/2:ℝ) by norm_num),side A simple,small.eventually_lt_const target] with i paid room eps
  intro per
  let H:=A.clock.hatBeta i
  have hH:0<H:=zero_lt_one.trans (A.fits.delayed i)
  have eq:((Real.sqrt H)⁻¹)^(1-(1/2:ℝ))=H^(-(1/4:ℝ)):=by
    rw [Real.sqrt_eq_rpow,←Real.rpow_neg_one,←Real.rpow_mul hH.le,←Real.rpow_mul hH.le]
    norm_num
  have seen:=paid H (by dsimp [H]; linarith) (by dsimp [H]; linarith)
  rw [eq] at seen
  have win:=seen.trans_lt eps
  have fee:=axial_nonneg (A.budget i) (roof A i)
  have t:0≤(A.budget i).threshold:=(A.budget i).threshold_pos.le
  have kn:=mul_nonneg tube.scale.le fee
  refine ⟨room per,?_,?_,?_,(win.trans_le (min_le_right _ _)).le⟩
  · apply lt_of_le_of_lt _ (win.trans_le (min_le_left _ _))
    unfold width;linarith
  · unfold width;linarith
  · unfold width;linarith

end YM.Integration.WilsonEmittedOriginalRoom
