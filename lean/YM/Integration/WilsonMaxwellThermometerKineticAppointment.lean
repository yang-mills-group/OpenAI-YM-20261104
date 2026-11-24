import YM.Integration.WilsonMaxwellThermometerKineticCorridor
import YM.Integration.WilsonOriginalPositionFineScheme

/-! The actual Wilson fine kinetic coordinate on the co-enrolled independent mesh. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerKineticAppointment
open Filter RG Lattice Wilson Source Extraction Table Spec Climb RG17 Trace.Pilot
open PhysicalNext.Repeat.Legato FVA2.Register Pert.Asymptotics XSpace
open scoped Topology Classical
variable {G : Gauge} (R : Run G) (simple : G.Simple) {B : ℕ} (hB : 0<B)
    (Z : WilsonPrescription G) {fine index : ℝ→ℕ}
local notation "m" => WilsonMeasuredWindow.stop R.family.path.levels simple B
local notation "ℓ" => (fun r : ℝ => WilsonAdmissionScale.logarithm R.family.path.levels (m r))
local notation "Λ" => WilsonPositionAuxiliaryReporterCalendar.scale R simple (B:=B)
local notation "g" => regulatorRun R.family
local notation "hat" => R.family.path.levels.clock.hatBeta
local notation "a" => R.family.S.a
local notation "enrolled" => WilsonOriginalPositionFineScheme.enrolled (R:=R) (hG:=simple) (B:=B) Z fine index

include hB in
theorem finite (schedule : enrolled) :
    ∀ᶠ r in trail, ∀ N per, fine r≤N → |g N per (fine r)/g N per (m r)-1| ≤
      16*(G.slopeConstant+1)*(ℓ r)^2*Real.exp (-(ℓ r)) := by
  have high := (WilsonAdmissionScale.logarithm_tendsto R.family.path.levels simple).comp
    (WilsonMeasuredWindow.stop_tendsto R.family.path.levels simple B hB)
  filter_upwards [schedule,high.eventually_ge_atTop 2] with r sale large
  obtain ⟨mk,_,price,spacing⟩:=sale
  have pos:=R.family.S.a_pos
  have units:=congrArg Real.log spacing
  change Real.log (a (fine r)/a (m r)) = Real.log ((Z.run.ratio^(index r) : ℕ):ℝ)⁻¹ at units
  rw [Real.log_div (pos _).ne' (pos _).ne',Real.log_inv,Nat.cast_pow,Real.log_pow] at units
  have wide : 1 ≤ 2+ℓ r := by change 2≤ℓ r at large; linarith
  have slab : (Λ r)^((3:ℝ)/2) ≤ (2+ℓ r)^2 :=
    (Real.rpow_le_rpow_of_exponent_le wide (by norm_num : (3:ℝ)/2≤(2:ℕ))).trans_eq (Real.rpow_natCast ..)
  have limit : Real.log (a (m r))-Real.log (a (fine r)) ≤ 8*(ℓ r)^2 := by
    change _≤(Λ r)^((3:ℝ)/2)+2*(2+ℓ r) at price
    change 2≤ℓ r at large
    nlinarith [price,units,slab,mul_nonneg (show 0≤ℓ r-2 by linarith) (show 0≤ℓ r+2 by linarith),
      sq_nonneg (ℓ r-2)]
  intro N per before
  have receipt:=WilsonMaxwellThermometerKineticCorridor.original R simple (m r) (fine r) N per mk before
  have kpos : 0≤2*(G.slopeConstant+1) := by have hh:=G.slopeConstant_pos simple; positivity
  have factor:0<hat (m r):=zero_lt_one.trans (R.family.path.levels.fits.delayed _)
  apply receipt.trans
  change _≤16*(G.slopeConstant+1)*(ℓ r)^2*Real.exp (-Real.log (hat (m r)))
  rw [Real.exp_neg,Real.exp_log factor,←div_eq_mul_inv]
  apply div_le_div_of_nonneg_right _ factor.le
  nlinarith only [mul_le_mul_of_nonneg_left limit kpos]

include hB in
theorem original (schedule : enrolled) (f : Extraction.Order) (Y : Ultrafilter (ℕ×ℕ))
    (prior : (Y:Filter _)≤f.fuse) :
    Tendsto (fun w : ℝ×(ℕ×ℕ)=>g w.2.1 w.2.2 (fine w.1) / g w.2.1 w.2.2 (m w.1))
      (trail.curry (Y:Filter _)) (𝓝 1) := by
  have high := (WilsonAdmissionScale.logarithm_tendsto R.family.path.levels simple).comp
    (WilsonMeasuredWindow.stop_tendsto R.family.path.levels simple B hB)
  have cash := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp high).const_mul (16*(G.slopeConstant+1))
  rw [mul_zero] at cash
  apply Metric.tendsto_nhds.mpr
  intro ε he
  apply eventually_curry_iff.mpr
  filter_upwards [finite R simple hB Z schedule,cash.eventually_lt_const he] with r paid cost
  filter_upwards [(Next.UVStress.large_mesh f (fine r)).filter_mono prior] with z before
  rw [Real.dist_eq]
  apply (paid z.1 z.2 before).trans_lt
  change 16*(G.slopeConstant+1)*((ℓ r)^2*Real.exp (-(ℓ r))) < ε at cost
  linarith only [cost]

end YM.Integration.WilsonMaxwellThermometerKineticAppointment
