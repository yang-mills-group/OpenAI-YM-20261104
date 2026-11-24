import YM.Integration.WilsonOriginalObservedRoseBornChiralClockWindow
import YM.Integration.WilsonIndependentMatchedReportedOpticalFuel
/-! Pay the retained quarter on the original upper section K=berth(t,f) and the true kinetic clock at m. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseBornChiralOptics
open Lattice RG Wilson Source PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Mer
open WilsonInvariantActionPosition (berth)
open WilsonOriginalPublicRelativeGramKineticMesh (thermal)
variable {G:Gauge}

theorem original (R:Run G)(simple:G.Simple)(m f K t out:ℕ)(older:m ≤ f)(purchase:K=berth R t f)
    (deep:8*(out+1) ≤ t):
    (paceT R.family.path.levels.S m K)^((1:ℝ)/4)*(thermal R m)^(-(1:ℝ)) ≤ (thermal R m)^out:=by
  let β:=R.family.path.levels.clock.hatBeta
  let g:=thermal R m
  have hm:1 ≤ β m:=(R.family.path.levels.fits.delayed m).le
  have hf:1 ≤ β f:=(R.family.path.levels.fits.delayed f).le
  have pos:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans_le hm))
  have before:β m ≤ β f:=WilsonStartup.Timing.hat_mono R.family.path.levels (Gauge.slopeConstant_pos simple).le older
  have clock:g⁻¹ ≤ (β f)^2:=by
    change (Real.sqrt (β m))⁻¹⁻¹ ≤ _
    rw [inv_inv]
    apply le_trans ((Real.sqrt_le_iff).2 ⟨zero_le_one.trans hm,show β m ≤ (β m)^2 by nlinarith [sq_nonneg (β m-1)]⟩)
    exact before.trans (by nlinarith [sq_nonneg (β f-1)])
  have bought:=WilsonIndependentMatchedReportedOpticalFuel.depth R m f K t (4*(out+1)) older purchase
    (by omega) g pos clock
  let δ:=paceT R.family.path.levels.S m K
  have power:(g^(4*(out+1)))^((1:ℝ)/4)=g^(out+1):=by
    rw [show 4*(out+1)=(out+1)*4 by omega,pow_mul,←Real.rpow_natCast (g^(out+1)) 4,
      ←Real.rpow_mul (pow_nonneg pos.le _)]
    norm_num
  have gain:δ^((1:ℝ)/4) ≤ g^(out+1):=
    (Real.rpow_le_rpow (pace_pos R.family.path.levels.S m K).le bought (by norm_num)).trans_eq power
  change δ^((1:ℝ)/4)*g^(-(1:ℝ)) ≤ g^out
  rw [Real.rpow_neg_one]
  exact (mul_le_mul_of_nonneg_right gain (inv_pos.mpr pos).le).trans_eq (by rw [pow_succ]; field_simp [pos.ne'])

end YM.Integration.WilsonOriginalObservedRoseBornChiralOptics
