import YM.Integration.WilsonAddressedSharpTrialUnits
import YM.Integration.WilsonOriginalPublicFigureIncome

/-! The physical inverse and dated Laurent factor of the unamplified top row.
All grades of the row use the one submitted engineering weight. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPhysicalFruitDose
open Finset Lattice RG Wilson Source Labels Extra.Histories Motion PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonOriginalPublicFigureIncome (height scale pole)
open WilsonAddressedTrialPivotUnits (row)
open WilsonReflectedMixedSharpAxis (Cash)
open WilsonReflectedFundedHearing (Arm)
open WilsonReflectedPublicGuardedMotion (coords)
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open WilsonOriginalMicroscopicGuardedReporters (stretch)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)
local notation "a" => R.family.S.a
local notation "F" d:max => R.family.labels.level d

def amounts (d K N per:ℕ)(r:ℝ)(t:ℂ)(v:R.family.label d):(F d).Coeff:=fun b=>
  (((a K/r)^d:ℝ):ℂ) * WilsonOriginalPublicTrialFigure.amount R (fun _:Unit=>d)
    (regulatorRun R.family N per K) (fun _=>row R d K N per t v) () b

theorem unamplified (d K N per:ℕ)(live:K ≤ N)(r:ℝ)(rp:0<r)(t:ℂ)(v:R.family.label d):
    (F d).coeffSize (amounts R d K N per r t v) ≤ 
      (r^d)⁻¹*‖t‖*(2:ℝ)^height R d*(F d).coeffSize v*(scale R K)^height R d:=by
  let w:=row R d K N per t v
  let D:=((a K/r)^d)
  have dp:0 ≤ D:=pow_nonneg (div_pos (R.family.S.a_pos K) rp).le _
  have tally:(F d).coeffSize (amounts R d K N per r t v) ≤ D*((F d).coeffSize w*scale R K^height R d):=by
    change (∑b,‖amounts R d K N per r t v b‖) ≤ D*((∑b,‖w b‖)*_)
    rw [Finset.sum_mul,Finset.mul_sum]
    refine Finset.sum_le_sum fun b _=>?_
    simp only [amounts,WilsonOriginalPublicTrialFigure.amount,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    change abs D *(‖w b‖*_)  ≤  D*(‖w b‖*_)
    rw [abs_of_nonneg dp]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pole R d N per K live b) (norm_nonneg (w b))) dp
  have group:=WilsonPositionProgramReportedField.purchased R d K (N,per) live ((t*((a K:ℂ)^d)⁻¹)•v)
  change (F d).coeffSize w ≤ _ at group
  rw [RG12.mass,Extra.Histories.Size.smul,norm_mul,norm_inv,norm_pow,Complex.norm_real,
    Real.norm_of_nonneg (R.family.S.a_pos K).le] at group
  have sp:0 ≤ scale R K^height R d:=pow_nonneg (zero_le_one.trans (le_max_left ..)) _
  apply tally.trans ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right group sp) dp).trans (le_of_eq ?_))
  dsimp only [D,WilsonOriginalPublicFigureIncome.height];rw [div_pow]
  field_simp [(R.family.S.a_pos K).ne',rp.ne']

theorem original {d j f K N per target:ℕ}(before:j ≤ f)(up:f ≤ K)(live:K ≤ N){η:ℝ}
    (A:R.family.label d≃ₗ[ℂ]R.family.label d)(Y:R.family.label d){W:ℝ}
    (cash:Cash (R:=R) d j f K N per target before up live η A Y W)
    (arm:Arm R d N per f K)(same:arm.w=A.symm (fitted R d j N per Y))
    (r:ℝ)(rp:0<r)(t:ℂ):
    (F d).coeffSize (amounts R d K N per r t (coords R arm)) ≤ 
      (4*‖t‖*(2:ℝ)^height R d*orbitCost (F d))*scale R K^height R d*
      ((a j/r)^((d:ℝ)+η)*W)*(r/a K)^η:=by
  have aj:=R.family.S.a_pos j
  have ak:=R.family.S.a_pos K
  have time:R.family.S.scale K-R.family.S.scale j=Real.log (a j/a K):=by
    rw [Schedule.scale,Schedule.scale,Real.log_inv,Real.log_inv,Real.log_div aj.ne' ak.ne'];ring
  have age:stretch R η j K=2*(a j/a K)^η:=by
    unfold WilsonOriginalMicroscopicGuardedReporters.stretch
    rw [Real.rpow_def_of_pos (div_pos aj ak),←time,mul_comm η]
  have split:(a j/a K)^η=(a j/r)^η*(r/a K)^η:=by
    rw [←Real.mul_rpow (div_pos aj rp).le (div_pos rp ak).le];congr 1;field_simp
  have unturned:(F d).coeffSize arm.w ≤ stretch R η j K*(2*(a j^d*W)):=by rw [same];exact cash.2.1
  have op:0 ≤ orbitCost (F d):=zero_le_one.trans (orbitCost_one_le _)
  have issued: (F d).coeffSize (coords R arm) ≤ orbitCost (F d)*(stretch R η j K*(2*(a j^d*W))):=
    (patch_cost (F d) (arm.s,arm.b) arm.w).trans (mul_le_mul_of_nonneg_left unturned op)
  have scale0:0 ≤ scale R K:=zero_le_one.trans (le_max_left ..)
  refine (unamplified R d K N per live r rp t (coords R arm)).trans
    ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left issued (by positivity)) (pow_nonneg scale0 _)).trans_eq ?_)
  rw [age,split,Real.rpow_add (div_pos aj rp),Real.rpow_natCast,div_pow]
  ring

end YM.Integration.WilsonOriginalPhysicalFruitDose
end
