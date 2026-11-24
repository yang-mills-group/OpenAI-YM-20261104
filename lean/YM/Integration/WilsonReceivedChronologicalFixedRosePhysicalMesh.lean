import YM.Integration.WilsonReceivedChronologicalFixedRoseCutoffSalary
import YM.Integration.WilsonOriginalObservedRosePublicMesh

/-! Optical control of both public mesh costs at the actual physical top. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalFixedRosePhysicalMesh
open Function Filter Lattice Wilson RG Real Next.Rank PhysicalNext.Repeat.Legato Pert.Asymptotics
open scoped Topology Classical
variable {G:Gauge}(R:Run G)(simple:G.Simple)
local notation "H" => R.family.path.levels.clock.hatBeta
local notation "a" => R.family.S.a
local notation "σ" => R.family.S.scale

include simple in
theorem original (A:ℕ)(scale:ℝ)(positive:0<scale):
    ∀ᶠ v:ℕ in atTop,∀{K N per:ℕ},v≤K → K≤N →
    σ K-σ (v-1) ≤ (A:ℝ)*(1+Real.log (H v)) →
    (σ K-σ v≤(2*A:ℕ)*Real.log (H v)) ∧
    ∀r:ℝ,scale*r≤a v → r/(a K)≤((regulatorRun R.family N per v)⁻¹)^
      (WilsonOriginalObservedRosePublicMesh.aperture A):=by
  let amount:=Real.exp (A:ℝ)*(2:ℝ)^A/scale
  filter_upwards [(Station.hat_rate R.family.path.levels simple).eventually_ge_atTop (Real.exp 1),
    WilsonOriginalOpticalCouplingBand.cold R simple (max 1 amount)] with v heat money
  intro K N per vk kn span
  let b:=R.family.path.β N per v
  let z:=(regulatorRun R.family N per v)⁻¹
  have hp:0<H v:=zero_lt_one.trans (R.family.path.levels.fits.delayed v)
  have bp:0<b:=Overlay.beta_positive R.makes.wilson (vk.trans kn)
  have zp:0≤z:=(inv_pos.mpr (ActualRunKernelPackets.regulator_pos R N per v (vk.trans kn))).le
  have bought:=money N per (vk.trans kn)
  have seated:1≤z:=(le_max_left ..).trans bought
  have bill:amount≤z:=(le_max_right ..).trans bought
  have logOne:1≤Real.log (H v):=by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) heat
  have old:σ (v-1)≤σ v:=by
    simpa only [Schedule.scale,Real.log_inv] using
      neg_le_neg (Real.log_le_log (R.family.S.a_pos v) (R.family.S.strictAnti.antitone (Nat.sub_le v 1)))
  have clean:σ K-σ v≤(A:ℝ)*(1+Real.log (H v)):=(sub_le_sub_left old _).trans span
  constructor
  · push_cast
    nlinarith only [clean,mul_nonneg (Nat.cast_nonneg A) (sub_nonneg.mpr logOne)]
  intro r fine
  have band:H v≤2*z^2:=by
    have small: H v/2≤b:=(R.makes.wilson.represents N per v (vk.trans kn)).band.1
    have native:z^2=b:=by change ((Real.sqrt b)⁻¹)⁻¹^2=b; rw [inv_inv,Real.sq_sqrt bp.le]
    rw [native]
    linarith only [small]
  have spacing:(a v)/(a K)≤Real.exp (A:ℝ)*(H v)^A:=by
    calc (a v)/(a K)=Real.exp (σ K-σ v):=by
           rw [←WilsonIndependentCapturedDates.mesh,Real.exp_log (div_pos (R.family.S.a_pos _) (R.family.S.a_pos _))]
         _ ≤ Real.exp ((A:ℝ)*(1+Real.log (H v))):=Real.exp_le_exp.mpr clean
         _ = _:=by rw [mul_add,mul_one,Real.exp_add,Real.exp_nat_mul,Real.exp_log hp]
  have born:=div_le_div_of_nonneg_right ((le_div_iff₀ positive).2 (by simpa only [mul_comm] using fine))
    (R.family.S.a_pos K).le
  calc r/(a K)≤((a v)/scale)/(a K):=born
       _ = scale⁻¹*((a v)/(a K)):=by ring
       _ ≤ scale⁻¹*(Real.exp (A:ℝ)*(H v)^A):=mul_le_mul_of_nonneg_left spacing (inv_nonneg.mpr positive.le)
       _ ≤ scale⁻¹*(Real.exp (A:ℝ)*(2*z^2)^A):=mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp.le band _) (Real.exp_pos _).le) (inv_nonneg.mpr positive.le)
       _=amount*z^(2*A):=by simp only [amount,mul_pow,←pow_mul,div_eq_mul_inv];ring
       _≤z*z^(2*A):=mul_le_mul_of_nonneg_right bill (pow_nonneg zp _)
       _=z^(2*A+1):=by rw [pow_succ,mul_comm]
       _≤_:=pow_le_pow_right₀ seated (by unfold WilsonOriginalObservedRosePublicMesh.aperture;omega)

end YM.Integration.WilsonReceivedChronologicalFixedRosePhysicalMesh
