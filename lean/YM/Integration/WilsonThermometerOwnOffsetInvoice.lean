import YM.Integration.WilsonThermometerOwnOffsetRadii
import YM.Integration.WilsonThermometerOwnOffsetJoint

/-! Actual source fees for the normalized physical columns. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerOwnOffsetInvoice
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open WilsonThermometerOwnOffsetNectar WilsonThermometerOwnOffsetRadii
open scoped Classical Topology
variable {G : Gauge} (R : Run G) {N p k d : ℕ} {I : Type}
local notation "β" => R.family.path.levels.clock.hatBeta

theorem block_one (j : ℕ) : (1:ℝ) ≤ ((R.family.S.block j).val:ℝ) := by
  exact_mod_cast (show 1 ≤ (R.family.S.block j).val from (R.family.S.block j).property)

theorem lamp_le (j : ℕ) : ld R.family.path.levels j ≤ ((R.family.S.block j).val:ℝ) :=
  Real.rpow_le_self_of_one_le (block_one R j)
    ((div_le_one (by positivity)).mpr (le_add_of_nonneg_left (by positivity)))

theorem lamp_pos (j : ℕ) : 0<ld R.family.path.levels j :=
  Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one (block_one R j)) _

theorem span_one {j : ℕ} (hj:k ≤ j) : 1 ≤ span R k j := by
  induction j,hj using Nat.le_induction with
  | base=>exact (div_self (R.family.S.a_pos _).ne').ge
  | succ j _ ih=>rw [span_next];exact one_le_mul_of_one_le_of_one_le ih (block_one R j)

theorem factor_size (k j d : ℕ) : ‖factor R k j d‖=(span R k j)^d := by
  unfold factor alto span
  simp only [norm_mul,norm_inv,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (R.family.S.a_pos _),div_eq_mul_inv,mul_pow,inv_pow]

theorem meter {j : ℕ} (hj:k ≤ j) : stringCost R.family hj ≤ span R k j := by
  induction j,hj using Nat.le_induction with
  | base=>rw [string_base];exact span_one _ le_rfl
  | succ j hj ih=>
    rw [string_next hj,span_next,mul_comm (ld ..)]
    exact mul_le_mul ih (lamp_le R j) (lamp_pos R j).le (span_pos R k j).le

variable {V : Sight R.family d p} {r : Emblems R.family d}
  {B : ℕ→ℕ→ℝ} {z : Site (R.family.side N p)}
  (H : Enrolled R.makes R.doors B k N p d (digits R N p z) V r)
  (y : Palette R.family d) (bounded : size y ≤ 1)

include H bounded
theorem ascent {j : ℕ} (hj:k ≤ j) (hn:j ≤ N) : size (finer r hj y) ≤ span R k j :=
  (H.inverse le_rfl hj hn y).trans (calc
    stringCost R.family hj * size y ≤ span R k j * 1 :=
      mul_le_mul (meter R hj) bounded (by unfold size; positivity) (span_pos R k j).le
    _ = _ := mul_one _)

theorem adjacent {u : ℝ} (hu:0 ≤ u) {j : ℕ} (hj:k ≤ j) (hn:j<N) :
    charge R r y hj u ≤ (span R k (j+1))^(d+3)*u := by
  let L : ℝ := (R.family.S.block j).val
  let X := span R k j
  let Z := span R k (j+1)
  let l := ld R.family.path.levels j
  have Xpos : 0<X := span_pos ..
  have Zpos : 0<Z := span_pos ..
  have Xone : 1 ≤ X := span_one R hj
  have lx : 0 ≤ l := (lamp_pos R j).le
  have Lpos : 0<L := zero_lt_one.trans_le (block_one R j)
  have lL : l ≤ L := lamp_le R j
  have XZ : X ≤ Z := by
    rw [show Z=X*L from span_next R k j];exact le_mul_of_one_le_right Xpos.le (block_one R j)
  have LZ : L ≤ Z := by
    rw [show Z=X*L from span_next R k j];exact le_mul_of_one_le_left Lpos.le Xone
  have lZ := lL.trans LZ
  have pay := ((H.follows j hj hn).payment (finer r (hj.trans j.le_succ) y)).1
  have joined : r j (finer r (hj.trans j.le_succ) y)=finer r hj y := by
    rw [finer_next hj];simp only [LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply]
  change size (amplify d R.family (R.family.S.block j) (finer r (hj.trans j.le_succ) y)) ≤ l*size (r j (finer r (hj.trans j.le_succ) y)) at pay
  rw [joined] at pay
  have mid := (ascent R H y bounded hj hn.le).trans XZ
  have amps : size (amplify d R.family (R.family.S.block j) (finer r (hj.trans j.le_succ) y)) ≤ Z*Z :=
    pay.trans (mul_le_mul lZ mid (by unfold size; positivity) Zpos.le)
  unfold charge
  rw [factor_size,factor_size,max_eq_left (pow_le_pow_left₀ Xpos.le XZ d)]
  calc Z^d*(l*size _*u) ≤ Z^d*(Z*(Z*Z)*u) := by gcongr; exact size_ge _
       _ = Z^(d+3)*u := by rw [pow_add];ring

theorem top {t : ℕ} {u : ℝ} (hu:0<u) (hk:k ≤ N)
    (start : 0<far R.alloy.B.a N ∧ pricesTop (fly R.alloy.B.a) (far R.alloy.B.a) N d*u ≤ far R.alloy.B.a N * β N^t)
    (wallet : radius R t k N*(span R k N)^(d+3)*β N^t ≤ 1) :
    radius R t k N*(‖factor R k N d‖*(u*size (finer r hk y)*pricesTop (fly R.alloy.B.a) (far R.alloy.B.a) N d)) ≤ far R.alloy.B.a N := by
  let P := pricesTop (fly R.alloy.B.a) (far R.alloy.B.a) N d
  let K := far R.alloy.B.a N
  let X := span R k N
  let w := radius R t k N
  have wp : 0<w := radius_pos R t k N hk
  have xp : 0<X := span_pos ..
  have xp1 : 1 ≤ X := span_one R hk
  have sizep : 0 ≤ size (finer r hk y) := by unfold size;positivity
  have bp : 0<β N:=WardBin.hot _ _
  have har : X^d*size (finer r hk y) ≤ X^(d+3) := calc
    _ ≤ X^d * X := mul_le_mul_of_nonneg_left (ascent R H y bounded hk le_rfl) (pow_nonneg xp.le _)
    _ = X^(d+1) := (pow_succ ..).symm
    _ ≤ X^(d+3) := pow_le_pow_right₀ xp1 (by omega)
  rw [factor_size]
  by_cases pp : 0 ≤ P
  · calc w*(X^d*(u*size (finer r hk y)*P)) = w*(X^d*size (finer r hk y))*(P*u) := by ring
         _ ≤ w*X^(d+3)*(K*β N^t) := mul_le_mul (mul_le_mul_of_nonneg_left har wp.le) start.2 (mul_nonneg pp hu.le) (mul_nonneg wp.le (pow_nonneg xp.le _))
         _ = (w*X^(d+3)*β N^t)*K := by ring
         _ ≤ 1*K := mul_le_mul_of_nonneg_right wallet start.1.le
         _ = K := one_mul _
  exact (mul_nonpos_of_nonneg_of_nonpos wp.le (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg xp.le _)
    (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hu.le sizep) (le_of_not_ge pp)))).trans start.1.le

end YM.Integration.WilsonThermometerOwnOffsetInvoice
end
