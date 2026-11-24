import YM.Integration.WilsonThermometerCorridorRides
import YM.Integration.WilsonThermometerOwnOffsetInvoice

/- The actual source chart at the separated date is retimed onto the earlier
   physical path. Its restored label cost is paid by the booked response at the
   earlier point, including the full engineering ratio of the original chart. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerCorridorCharge
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open WilsonThermometerOwnOffsetNectar WilsonThermometerOwnOffsetRadii
open scoped Classical Topology
open WilsonThermometerOwnOffsetInvoice Trace.Physical OPE
variable {G:Gauge}(R:Run G){N p k d f:ℕ}{D:Rail R.family}{B:ℕ→ℕ→ℝ}
  {V:Sight R.family d p}{r:Emblems R.family d}{z:Site (R.family.side N p)}
local notation "C" => R.family
local notation "β" => R.family.path.levels.clock.hatBeta

theorem quoted (H:Enrolled R.makes D B k N p d (digits R N p z) V r)
    (y:Palette (C) d){j:ℕ}(hj:k≤j)(hn:j<N){u:ℝ}(hu:0≤u):
    charge R r y hj u≤(span R k (j+1))^(d+3)*size y*u:=by
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
  have sy:=size_ge y
  have mid: size (finer r hj y) ≤ Z*size y:=
    (H.inverse (le_refl k) hj hn.le y).trans
      (mul_le_mul_of_nonneg_right ((meter R hj).trans XZ) sy)
  have amps:size (amplify _ _ _ (finer r (hj.trans j.le_succ) y)) ≤ Z*(Z*size y):=
    pay.trans (mul_le_mul lZ mid (size_ge _) Zpos.le)
  unfold charge
  rw [factor_size,factor_size,max_eq_left (pow_le_pow_left₀ Xpos.le XZ d)]
  calc Z^d*(l*size _*u) ≤ Z^d*(Z*(Z*(Z*size y))*u) := by gcongr; exact size_ge _
       _ = Z^(d+3)*size y*u := by rw [pow_add];ring

theorem span_le {j f:ℕ}(jf:j≤f):span R k j ≤ span R k f:=by
  induction f,jf using Nat.le_induction with
  | base=>rfl
  | succ n h ih=>exact ih.trans (by rw [span_next];exact le_mul_of_one_le_right (span_pos R k n).le (block_one R n))

theorem radius_paid {t j:ℕ}(H:Enrolled R.makes D B k N p d (digits R N p z) V r)
    (initial:Palette (C) d)(bj:k≤j)(jf:j<f)(fn:f≤N)
    (growth:size initial≤(span R k f)^(d+1))
    (book:radius R t k f * (span R k f)^(2*d+4) * β f^t≤1)
    {u:ℝ}(pos:0≤u)(income:2*u≤β f^t):
    2*radius R t k f*(‖WilsonCapturedPrimaryWardRetimed.ratio (C) f k d‖*
       charge R r initial bj u)≤1:=by
  let x:=span R k f
  let w:=radius R t k f
  have kf:=bj.trans jf.le
  have x_pos:=span_pos R k f
  have wp:= (radius_pos R t k f kf).le
  have scale:‖WilsonCapturedPrimaryWardRetimed.ratio (C) f k d‖≤1:=by
    rw [WilsonCapturedPrimaryWardRetimed.norm_ratio]
    have sm := (le_div_iff₀ ((C).S.a_pos f)).mp (span_one R kf)
    exact pow_le_one₀ (div_pos ((C).S.a_pos _) ((C).S.a_pos _)).le ((div_le_one ((C).S.a_pos _)).mpr (by simpa using sm))
  have estimate:=quoted R H initial bj (jf.trans_le fn) pos
  have all:‖WilsonCapturedPrimaryWardRetimed.ratio (C) f k d‖*charge R r initial bj u
      ≤ (span R k (j+1))^(d+3)*size initial*u:=
    (mul_le_mul_of_nonneg_left estimate (norm_nonneg _)).trans
      (mul_le_of_le_one_left (mul_nonneg (mul_nonneg (pow_nonneg (span_pos R k (j+1)).le _) (size_ge _)) pos) scale)
  calc 2*w*(_*_) ≤ 2*w*((span R k (j+1))^(d+3)*size initial*u) := mul_le_mul_of_nonneg_left all (by positivity)
    _ ≤ 2*w*(x^(d+3)*x^(d+1)*u) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (mul_le_mul (pow_le_pow_left₀ (span_pos R k (j+1)).le (span_le R jf) _) growth
          (size_ge _) (pow_nonneg x_pos.le _)) pos) (mul_nonneg (by norm_num) wp)
    _ = w*x^(2*d+4)*(2*u):=by rw [show 2*d+4=(d+3)+(d+1) by omega,pow_add];ring
    _ ≤ w*x^(2*d+4)*β f^t:=mul_le_mul_of_nonneg_left income (mul_nonneg wp (pow_nonneg x_pos.le _))
    _ ≤ 1:=book

end YM.Integration.WilsonThermometerCorridorCharge
end
