import YM.Integration.WilsonIndependentPublicSpoutGround

/-! Native quadratic calibration of the *whole* Spout action under a
field and temperature substitution. The coefficients at positive order
are the signed bias after removal of the common quadratic. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutUnmarkedClock
open Lattice RG WilsonCoeffUV WilsonCoeffUV.Bank PowerSeries Precision
open scoped Classical
variable {G:Gauge}(A:Levels G)(Ñ:ChartRatio G)

theorem original (simple:G.Simple)(chart:LocalRatio Ñ){N m:ℕ}(le:m≤N)
    (α:PowerSeries ℝ)(unit:constantCoeff α=1):
    Kstar (Blue.mix α (actionW A Ñ N m))=(α⁻¹)^2 := by
  have H:=catchment A Ñ simple chart le
  rw [reval unit (fun i=>H.paid i 2),H.rise]
  have h:subst (α*X) (1:PowerSeries ℝ)=(1:PowerSeries ℝ):=by
    calc
      subst (α*X) (1:PowerSeries ℝ)=subst (α*X) (PowerSeries.C (R:=ℝ) 1):=
        congrArg (subst (α*X) : PowerSeries ℝ → PowerSeries ℝ) (map_one _).symm
      _=PowerSeries.C 1:=subst_C 1
      _=1:=map_one _
  rw [h,one_mul]

theorem positive (simple:G.Simple)(chart:LocalRatio Ñ){N m:ℕ}(le:m≤N)
    (α:PowerSeries ℝ)(unit:constantCoeff α=1)(e:ℕ)(pos:0<e):
    coeff e (Kstar (Blue.mix α (actionW A Ñ N m))-1)=coeff e ((α⁻¹)^2) := by
  rw [original A Ñ simple chart le α unit,map_sub,coeff_one,if_neg (by omega),sub_zero]

theorem ground (simple:G.Simple)(chart:LocalRatio Ñ){N m:ℕ}(le:m≤N)
    (α:PowerSeries ℝ)(unit:constantCoeff α=1):
    constantCoeff (Kstar (Blue.mix α (actionW A Ñ N m))-1)=0 := by
  rw [original A Ñ simple chart le α unit,map_sub,map_one,map_pow,constantCoeff_inv,unit]
  norm_num

end YM.Integration.WilsonIndependentSpoutUnmarkedClock
