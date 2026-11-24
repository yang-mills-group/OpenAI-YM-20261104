import YM.Integration.WilsonPhysicalHistoryAperture

/-! A single actual stamped block radius pays every fixed power in the independent cover tail. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalProjectionHalo
open Filter Lattice RG Wilson PhysicalNext.Repeat.Legato Pert.Asymptotics Trace.Physical
open FormalBulk08 FormalBulk08.Borough RG16
open WilsonPhysicalHistoryAperture
open scoped Topology
variable {G:Gauge} (R:Run G) (simple:G.Simple) {u:ℕ→ℕ}
variable (grant:WilsonWindowFormalPurchase.Canonical u R.kit)
local notation "β" => R.family.path.levels.clock.hatBeta

include simple grant in
theorem original (q:ℕ):
    ∀ᶠ i:ℕ in atTop,∀N per:ℕ,i≤N →
      let B:=(R.family.path.rep N per i).p.B
      4*(radius R.family q i+1)≤B ∧
      Real.exp (-(width R.family i/2)*((B-1:ℕ):ℝ))≤(regulatorRun R.family N per i)^(q+1):=by
  let P:ℝ:=16*((q+1:ℕ):ℝ)
  have P0:0<P:=by dsimp [P];positivity
  have grow:=Real.tendsto_log_atTop.comp (Next.Rank.Station.hat_rate R.family.path.levels simple)
  have small:=grow.eventually (Real.isLittleO_log_id_atTop.bound (inv_pos.mpr (show 0<2*P by positivity)))
  filter_upwards [small,grow.eventually_ge_atTop (max 4 (2*P))] with i quiet warm
  intro N per live B
  let t:=Real.log (β i)
  let w:=width R.family i
  have t4:4≤t:=(le_max_left ..).trans warm
  have tp:2*P≤t:=(le_max_right ..).trans warm
  have t1:1≤t:=by linarith only [t4]
  have t0:0≤t:=zero_le_one.trans t1
  have logt:0≤Real.log t:=Real.log_nonneg t1
  change |Real.log t|≤(2*P)⁻¹*|t| at quiet
  have lin:Real.log t≤(2*P)⁻¹*t:=by
    simpa only [Real.norm_eq_abs,id_eq,abs_of_nonneg t0,abs_of_nonneg logt] using quiet
  have logprice:Real.log t*(2*P)≤t:=(le_div_iff₀ (show 0<2*P by positivity)).mp
    (by simpa only [div_eq_mul_inv,mul_comm] using lin)
  have winv:w⁻¹≤1+Real.log t:=width_paid R grant i
  have budget:P*w⁻¹≤t:=by
    have h:=mul_le_mul_of_nonneg_left winv P0.le
    nlinarith only [h,logprice,tp]
  let z:=RG16.Lambda R.family.path.levels i
  have z0:0≤z:=by change 0≤2+t;linarith only [t0]
  have zt:z≤2*t:=by change 2+t≤2*t;linarith only [t4]
  let Q:ℝ:=((q+1:ℕ):ℝ)
  have Q0:0≤Q:=by dsimp [Q];positivity
  have paidWidth:Q*w⁻¹≤t/16:=by change (16*Q)*w⁻¹≤t at budget;linarith only [budget]
  have volume:Q*z/w≤t^2/8:=by
    have prod:=mul_le_mul paidWidth zt z0 (by linarith only [t0])
    rw [div_eq_mul_inv]
    nlinarith only [prod]
  have ceilB:(radius R.family q i:ℝ)≤Q*z/w+1:=
    (Nat.ceil_lt_add_one (show 0≤Q*z/w by exact div_nonneg (mul_nonneg Q0 z0) (width_pos R.family i).le)).le
  have physical:(R.family.path.rep N per i).p=R.alloy.B.a.budget i:=(R.makes.wilson.represents N per i live).vac
  have bulk:t^2≤(B:ℝ):=by dsimp only [B];rw [physical];exact Nat.le_ceil _
  have t2:16≤t^2:=by nlinarith only [mul_self_le_mul_self (by norm_num:0≤(4:ℝ)) t4]
  have enough:4*((radius R.family q i:ℝ)+1)≤(B:ℝ):=by linarith only [ceilB,volume,bulk,t2]
  have rad:4*(radius R.family q i+1)≤B:=by exact_mod_cast enough
  refine ⟨rad,?_⟩
  apply (Real.exp_le_exp.mpr ?_).trans (exponential R q N per i live)
  have natbound:2*radius R.family q i≤B-1:=by omega
  have en:2*(radius R.family q i:ℝ)≤((B-1:ℕ):ℝ):=by exact_mod_cast natbound
  have h:=mul_le_mul_of_nonneg_left en (width_pos R.family i).le
  dsimp [w] at *
  linarith only [h]

end YM.Integration.WilsonPhysicalProjectionHalo
