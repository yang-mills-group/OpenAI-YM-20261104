import YM.Integration.WilsonMixedTaggedMeasuredWindow
import YM.Integration.WilsonReportHarvestSourceReach
import YM.Integration.WilsonReportHarvestUpperAge

/-! The original frame and the first separating stop pay the change in
source scale. The comparison only uses the two original scale inequalities
and does not prescribe their order. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReportHarvestReadmittedCalendar
open Filter Lattice RG Wilson PhysicalNext.Repeat.Legato WilsonMeasuredAdmission WilsonReportHarvestSourceReach
open private paced from YM.Integration.WilsonMixedTaggedMeasuredWindow
open scoped Topology
variable {G:Gauge} (R:Run G)(simple:G.Simple)
local notation "A" => R.family.path.levels
local notation "S" => R.family.S
local notation "β" => (A).clock.hatBeta

theorem original (K:ℕ)(hk:0 < K)(level:ℝ→ℕ)
    (slow:∀j,((S).block j).val ≤ Real.log (RG05Readout.Lambda A j))
    (growing:Tendsto level (𝓝[>] (0:ℝ)) atTop)
    (near:∀ᶠr in 𝓝[>] (0:ℝ),(S).a (level r) ≤ r ∧ r ≤ (S).a (level r)*(β (level r))^2):
    ∀ᶠr in 𝓝[>] (0:ℝ),let m:=WilsonMeasuredWindow.stop A simple K r
      (S).a (level r)/(S).a m ≤ (mast A m)^(K+1) ∧
      β (level r) ≤ 2*β m ∧ 2 ≤ β m := by
  let c:=G.slopeConstant
  have cp:0<c:=G.slopeConstant_pos simple
  have hot:=Next.Rank.Station.hat_rate A simple
  have fhot:=hot.comp growing
  have mhot:=hot.comp (WilsonMeasuredWindow.stop_tendsto A simple K hk)
  have lower:=fhot.eventually (Real.isLittleO_log_id_atTop.bound (inv_pos.mpr (show 0<4*c by positivity)))
  have small:∀ᶠr in 𝓝[>] (0:ℝ),r < (S).a 0:=
    (eventually_lt_nhds ((S).a_pos 0)).filter_mono nhdsWithin_le_nhds
  filter_upwards [near,self_mem_nhdsWithin,small,lower,mhot.eventually_ge_atTop 2]
    with r frame rp rs tiny two m
  let m₀:=level r
  let b:=β m₀
  have one:1 ≤ b:=((A).fits.delayed m₀).le
  have bp:0<b:=zero_lt_one.trans_le one
  have z0:0 ≤ Real.log b:=Real.log_nonneg one
  have win:=WilsonMeasuredWindow.window A simple K (paced R slow) hk rp rs.le
  change (S).a m*(mast A m)^K ≤ r ∧ r ≤ (S).a m*(mast A m)^(K+1) at win
  refine ⟨(div_le_iff₀ ((S).a_pos m)).2 (by simpa only [mul_comm] using frame.1.trans win.2),?_,two⟩
  have down:(S).a m ≤ r:=(le_mul_of_one_le_right ((S).a_pos _).le
    (one_le_pow₀ (mast_gt_one A m).le)).trans win.1
  have ratio:(S).a m/(S).a m₀ ≤ b^2:=(div_le_iff₀ ((S).a_pos m₀)).2
    (by simpa only [m₀,b,mul_comm] using down.trans frame.2)
  have logratio:=Real.log_le_log (div_pos ((S).a_pos m) ((S).a_pos m₀)) ratio
  rw [←mesh,Real.log_exp,Real.log_pow] at logratio
  have clock:b-β m=c*elapsed S m m₀:=by
    unfold Calendar.hatBeta
    change _+_*((S).scale m₀)-(_+_*((S).scale m))=_*((S).scale m₀-(S).scale m)
    ring
  change |Real.log b| ≤ (4*c)⁻¹*|b| at tiny
  rw [abs_of_nonneg z0,abs_of_pos bp] at tiny
  have low:Real.log b*(4*c) ≤ b:=(le_div_iff₀ (by positivity:0<4*c)).mp
    (by simpa only [div_eq_mul_inv,mul_comm] using tiny)
  have difference:=mul_le_mul_of_nonneg_left logratio cp.le
  norm_num at difference
  change b ≤ 2*β m
  nlinarith only [clock,difference,low]

end YM.Integration.WilsonReportHarvestReadmittedCalendar
