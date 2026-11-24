import YM.Integration.WilsonReportHarvestResidentCalendar
import YM.RG05Readout.Many.Iota

/-! Spatial room on the true earlier admitted roster for the complete
backward marked-radius product. Its lower admission interval costs a
logarithm of the original mast at the reporting date. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReportHarvestReplayRoom
open Filter Real Lattice RG Wilson PhysicalNext.Repeat.Legato
open WilsonMeasuredAdmission WilsonReportHarvestSourceReach
open scoped Topology
variable {G:Gauge}(R:Run G)(simple:G.Simple)
local notation "A" => R.family.path.levels
local notation "S" => R.family.S
local notation "β" => (A).clock.hatBeta

private theorem fourth (e:ℝ)(pos:0≤e):(1+e)^4 ≤ 256*Real.exp e:=by
  have bound:1+e≤4*Real.exp (e/4):=by linarith only [Real.add_one_le_exp (e/4)]
  have exp4:(Real.exp (e/4))^4=Real.exp e:=by rw [←Real.exp_nat_mul];congr 1;ring
  calc (1+e)^4 ≤ (4*Real.exp (e/4))^4:=pow_le_pow_left₀ (by linarith) bound 4
       _=256*Real.exp e:=by rw [mul_pow,exp4];norm_num

include simple in
theorem original {k:ℝ}(kp:0<k):
    ∀ᶠm:ℕ in atTop,∀j:ℕ,∀mj:m ≤ j,∀per:ℕ,
      let X:=mast A m
      let e:=elapsed S m j
      k*(X^3*(1+Real.log X))*(1+e)^4 ≤
        (((S).toDepth mj per).count.val:ℝ)*(((A).budget m).B:ℝ)^2:=by
  let K:=8192*k
  have hp:0<K:=by dsimp only [K];positivity
  have grown:Tendsto (mast A) atTop atTop:=
    tendsto_atTop_add_const_left _ _ (WilsonAdmissionScale.logarithm_tendsto A simple)
  have small:=grown.eventually (Real.isLittleO_log_id_atTop.bound (inv_pos.mpr hp))
  filter_upwards [small,grown.eventually_ge_atTop (max 4 K)] with m quiet paid j mj per X e
  let z:=Real.log (β m)
  have X4:4≤X:=(le_max_left ..).trans paid
  have KX:K≤X:=(le_max_right ..).trans paid
  have X1:1≤X:=by linarith only [X4]
  have Xp:0≤X:=zero_le_one.trans X1
  have lx:0≤Real.log X:=Real.log_nonneg X1
  change |Real.log X| ≤ K⁻¹*|X| at quiet
  rw [abs_of_nonneg lx,abs_of_nonneg Xp] at quiet
  have rent:Real.log X*K ≤ X:=(le_div_iff₀ hp).mp (by simpa only [div_eq_mul_inv,mul_comm] using quiet)
  have space:(4096*k)*(1+Real.log X) ≤ X:=by
    dsimp only [K] at KX rent;linarith only [KX,rent]
  have Xz:X≤2*z:=by change 2+z≤2*z;change 4≤2+z at X4;linarith only [X4]
  have z0:0≤z:=Real.log_nonneg ((A).fits.delayed m).le
  have bm:z^2≤(((A).budget m).B:ℝ):=Nat.le_ceil _
  have quart:(X/2)^4 ≤ (((A).budget m).B:ℝ)^2:=calc
    _ ≤ z^4:=pow_le_pow_left₀ (by positivity) (by linarith only [Xz]) 4
    _ = (z^2)^2:=by ring
    _ ≤ _:=pow_le_pow_left₀ (sq_nonneg _) bm 2
  have area:256*k*(X^3*(1+Real.log X)) ≤ (((A).budget m).B:ℝ)^2:=calc
    _ = (X^3/16)*((4096*k)*(1+Real.log X)):=by ring
    _ ≤ (X^3/16)*X:=mul_le_mul_of_nonneg_left space (by positivity)
    _ = (X/2)^4:=by ring
    _ ≤ _:=quart
  have gap:0≤e:=sub_nonneg.mpr ((OPE.scale_mono S).monotone mj)
  have ratio:Real.exp e=(((S).toDepth mj per).count.val:ℝ):=by
    rw [mesh];apply (div_eq_iff ((S).a_pos _).ne').mpr
    simpa [mul_comm] using ((S).embeds_scale ((S).toDepth mj per)).symm
  calc _ ≤ k*(X^3*(1+Real.log X))*(256*Real.exp e):=
           mul_le_mul_of_nonneg_left (fourth e gap) (by positivity)
       _ = (256*k*(X^3*(1+Real.log X)))*Real.exp e:=by ring
       _ ≤ _:=by rw [←ratio,mul_comm (Real.exp e)];exact mul_le_mul_of_nonneg_right area (Real.exp_pos _).le

end YM.Integration.WilsonReportHarvestReplayRoom
