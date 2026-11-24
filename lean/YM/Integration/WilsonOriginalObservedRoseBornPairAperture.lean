import YM.Integration.WilsonOriginalObservedRoseBornChiralOptics
import YM.Integration.WilsonOriginalObservedRoseBornChiralClockWindow
import YM.Integration.WilsonIndependentMatchedReportedOpticalFuel
/-! Pay the retained quarter on the original upper section K=berth(t,f) and the true kinetic clock at m. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseBornPairAperture
open Lattice RG Wilson Source PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Mer
open WilsonInvariantActionPosition (berth)
open WilsonOriginalPublicRelativeGramKineticMesh (thermal)
variable {G:Gauge}


theorem refund (L:Levels G)(m K:ℕ)(r:ℝ)(pos:0<r):
    let p:=paceT L.S m K
    p^(1/4:ℝ)*((r/L.S.a K)^(1/16:ℝ))^2 =
      p^(1/8:ℝ)*(r/L.S.a m)^(1/8:ℝ):=by
  intro p
  have pp:0<p:=pace_pos .. 
  have ap:0<r/L.S.a K:=div_pos pos (L.S.a_pos _)
  have root:(r/L.S.a K)*p=r/L.S.a m:=by
    dsimp [p,paceT]
    field_simp [(L.S.a_pos K).ne',(L.S.a_pos m).ne']
  rw [←root,Real.mul_rpow ap.le pp.le,←Real.rpow_natCast _ 2,←Real.rpow_mul ap.le]
  rw [show (1/16:ℝ)*((2:ℕ):ℝ)=1/8 by norm_num]
  rw [show (1/4:ℝ)=1/8+1/8 by norm_num,Real.rpow_add pp]
  ring

theorem original (R:Run G)(simple:G.Simple)(m f K t out:ℕ)(r:ℝ)(pos:0<r)(older:m≤f)(purchase:K=berth R t f)
    (deep:16*(out+1)≤t):
    let L:=R.family.path.levels
    let g:=thermal R m
    (paceT L.S m K)^(1/4:ℝ)*g^(-(1:ℝ))*((r/L.S.a K)^(1/16:ℝ))^2 ≤
      (r/L.S.a m)^(1/8:ℝ)*g^out:=by
  intro L g
  have gp:0<g:=inv_pos.mpr (Real.sqrt_pos.2 (zero_lt_one.trans (R.family.path.levels.fits.delayed m)))
  have old:=WilsonOriginalObservedRoseBornChiralOptics.original R simple m f K t (2*out+1) older purchase (by omega)
  let p:=paceT L.S m K
  have pp:0<p:=pace_pos ..
  change p^(1/4:ℝ)*g^(-(1:ℝ)) ≤ g^(2*out+1) at old
  rw [Real.rpow_neg_one] at old
  have small:p^(1/4:ℝ) ≤ (g^(out+1))^2:=by
    have small:=mul_le_mul_of_nonneg_right old gp.le
    rw [mul_assoc,inv_mul_cancel₀ gp.ne',mul_one] at small
    apply small.trans_eq
    rw [←pow_succ,←pow_mul]
    congr 1
    omega
  have sq:(p^(1/8:ℝ))^2=p^(1/4:ℝ):=by
    rw [←Real.rpow_natCast _ 2,←Real.rpow_mul pp.le];norm_num
  have earned:p^(1/8:ℝ) ≤ g^(out+1):=by
    have t₀:=Real.rpow_nonneg pp.le (1/8:ℝ)
    have t₁:=pow_nonneg gp.le (out+1)
    nlinarith [sq,small]
  have combined:=mul_le_mul_of_nonneg_right earned (inv_pos.mpr gp).le
  rw [pow_succ,mul_assoc,mul_inv_cancel₀ gp.ne',mul_one] at combined
  calc
    _ = (p^(1/4:ℝ)*((r/L.S.a K)^(1/16:ℝ))^2)*g⁻¹:=by rw [Real.rpow_neg_one];ring
    _ = (r/L.S.a m)^(1/8:ℝ)*(p^(1/8:ℝ)*g⁻¹):=by rw [refund L m K r pos];ring
    _ ≤ _ :=mul_le_mul_of_nonneg_left combined (Real.rpow_nonneg (div_pos pos (L.S.a_pos _)).le _)

end YM.Integration.WilsonOriginalObservedRoseBornPairAperture
