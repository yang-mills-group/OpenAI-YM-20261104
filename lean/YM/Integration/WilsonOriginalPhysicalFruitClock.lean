import YM.Integration.WilsonOriginalPhysicalFruitDose
import YM.Integration.WilsonReflectedMixedSharpSchool
import YM.Integration.WilsonAddressedMixedOpticalMesh

/-! The coupling exponent of the physical top depends on the public home
and its fixed slot valence. The optical depth occurs in the onset and constant. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPhysicalFruitClock
open Finset Lattice RG Wilson Source Labels Extra.Histories Motion PhysicalNext.Repeat.Legato
open WilsonOriginalPhysicalFruitDose (amounts)
open WilsonOriginalPublicFigureIncome (scale height)
open WilsonReflectedMixedSharpAxis (Cash)
open WilsonReflectedFundedHearing (Arm)
open WilsonReflectedPublicGuardedMotion (coords)
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open scoped BigOperators Classical
variable {G:Gauge}(R:Run G)
local notation "a" => R.family.S.a
local notation "β" => R.family.path.levels.clock.hatBeta
local notation "S" d:max => R.family.labels.level d

def power (d E:ℕ):ℕ:=2*(height R d + E)
def salary (d E:ℕ)(t:ℂ)(M roof:ℝ):ℝ:=
  (4*‖t‖*(2:ℝ)^height R d*orbitCost (S d))*(2*roof)^height R d*(M*roof^E)

theorem home {j f d:ℕ}{r η W B:ℝ}(first:j ≤ f)(rp:0<r)(ar:a f ≤ r)(ep:0 ≤ η)(small:η ≤ 1)
    (nn:0 ≤ W)(cost:max 1 (2*(a j/a f)^(d+1)*W) ≤ B):
    (a j/r)^((d:ℝ)+η)*W ≤ B:=by
  have qp:0 < a j/a f:=div_pos (R.family.S.a_pos j) (R.family.S.a_pos f)
  have q1:1 ≤ a j/a f:=(one_le_div₀ (R.family.S.a_pos f)).mpr (R.family.S.strictAnti.antitone first)
  have qr:a j/r ≤ a j/a f:=div_le_div_of_nonneg_left (R.family.S.a_pos j).le (R.family.S.a_pos f) ar
  have lift:(a j/r)^((d:ℝ)+η) ≤ (a j/a f)^((d:ℝ)+1):=
    (Real.rpow_le_rpow (div_pos (R.family.S.a_pos j) rp).le qr (add_nonneg d.cast_nonneg ep)).trans
      (Real.rpow_le_rpow_of_exponent_le q1 (add_le_add_right small _))
  rw [←Nat.cast_one,←Nat.cast_add,Real.rpow_natCast] at lift
  apply (mul_le_mul_of_nonneg_right lift nn).trans
  have p:0 ≤ (a j/a f)^(d+1)*W:=mul_nonneg (pow_nonneg qp.le _) nn
  exact (show (a j/a f)^(d+1)*W ≤ 2*(a j/a f)^(d+1)*W by linarith).trans ((le_max_right ..).trans cost)

theorem original (simple:G.Simple){d j f K N per target E:ℕ}(before:j ≤ f)(up:f ≤ K)(live:K ≤ N){η:ℝ}
    (ep:0 ≤ η)(small:η ≤ 1)(A:R.family.label d≃ₗ[ℂ]R.family.label d)(Y:R.family.label d){W:ℝ}
    (cash:Cash (R:=R) d j f K N per target before up live η A Y W)
    (arm:Arm R d N per f K)(same:arm.w=A.symm (fitted R d j N per Y))
    (r g:ℝ)(rp:0<r)(gp:0<g)(ar:a f ≤ r)(t:ℂ)(M roof:ℝ)(mp:0 ≤ M)(one:1 ≤ roof)
    (nn:0 ≤ W)(card:max 1 (2*(a j/a f)^(d+1)*W) ≤ M*(β f)^E)(optical:β K*g^2 ≤ roof):
    (S d).coeffSize (amounts R d K N per r t (coords R arm)) ≤
      salary R d E t M roof*(g⁻¹)^power R d E*(r/a K)^η:=by
  have hi:=WilsonStartup.Timing.hat_mono R.family.path.levels (Gauge.slopeConstant_pos simple).le up
  have bp:1 ≤ β K:=(R.alloy.B.a.fits.delayed K).le
  have bf:0 ≤ β f:=zero_le_one.trans (R.alloy.B.a.fits.delayed f).le
  have bound:β K ≤ roof*(g⁻¹)^2:=by
    rw [inv_pow,←div_eq_mul_inv];exact (le_div_iff₀ (pow_pos gp 2)).mpr optical
  have scaleBound:scale R K ≤ (2*roof)*(g⁻¹)^2:=by
    have hi':Real.sqrt (2*β K) ≤ 2*β K:=by
      refine Real.sqrt_le_iff.mpr ⟨by linarith,?_⟩;nlinarith [sq_nonneg (β K-1)]
    apply (max_le (by linarith : 1 ≤ 2*β K) hi').trans
    linarith only [mul_le_mul_of_nonneg_left bound (by norm_num:0 ≤ (2:ℝ))]
  have scp:0 ≤ scale R K:=zero_le_one.trans (le_max_left ..)
  have hired:=(home R before rp ar ep small nn card).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ bf (hi.trans bound) E) mp)
  have pre:0 ≤ (4*‖t‖*(2:ℝ)^height R d*orbitCost (S d)):=
    mul_nonneg (by positivity) (zero_le_one.trans (orbitCost_one_le _))
  have older:0 ≤ (a j/r)^((d:ℝ)+η)*W:=mul_nonneg
    (Real.rpow_nonneg (div_pos (R.family.S.a_pos j) rp).le _) nn
  refine (WilsonOriginalPhysicalFruitDose.original R before up live A Y cash arm same r rp t).trans
    ((mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ scp scaleBound (height R d)) pre) hired older (mul_nonneg pre
      (pow_nonneg (mul_nonneg (by linarith) (sq_nonneg g⁻¹)) _)))
      (Real.rpow_nonneg (div_pos rp (R.family.S.a_pos K)).le _)).trans_eq ?_)
  unfold salary power
  simp only [mul_pow,←pow_mul,Nat.mul_add,pow_add]
  ring

end YM.Integration.WilsonOriginalPhysicalFruitClock
end
