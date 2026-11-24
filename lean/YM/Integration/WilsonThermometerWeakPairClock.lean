import YM.Integration.WilsonPhysicalCutoffCurrency
import YM.PhysMS.Foundation.Estimates
import YM.GapsContact.Earn.Stalls

/-! The actual coupling-powered detector window at the original stop. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakPairClock
open Filter Set Lattice Wilson RG PhysicalNext.Repeat.Legato Trace.Pilot PhysMS GapsContact.Ascent
open scoped Topology
variable {G:Gauge}(simple:G.Simple)(g:ℝ→ℝ)(hg:Coupling G g)
def scale (B:ℕ)(r:ℝ):ℝ:=r/(g r)^B

include hg simple
theorem small (B:ℕ): Tendsto (scale g B) trail trail:=by
  have p:∀ᶠ r in trail,0<scale g B r:=by
    filter_upwards [hg.positive,self_mem_nhdsWithin] with r h rpos
    exact div_pos rpos (pow_pos h _)
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_,p⟩
  apply Metric.tendsto_nhds.mpr
  intro ε ep
  filter_upwards [PhysMS.subpower_payment hg simple 1 1 zero_lt_one (ε/2) (half_pos ep) B,p,hg.positive] with r bill pos gp
  rw [Real.dist_eq,sub_zero,abs_of_pos pos]
  refine lt_of_le_of_lt ((div_le_iff₀ (pow_pos gp B)).mpr ?_) (half_lt_self ep)
  simpa only [Real.rpow_one,one_mul] using bill

theorem ordered (B:ℕ): ∀ᶠ r in trail, r ≤ scale g B r:=by
  filter_upwards [hg.positive,(hg.conforms simple).eventually (ge_mem_nhds zero_lt_one),self_mem_nhdsWithin] with r gp cap rp
  apply (le_div_iff₀ (pow_pos gp B)).mpr
  exact mul_le_of_le_one_right (le_of_lt rp) (pow_le_one₀ gp.le cap)

theorem on_stop (R:Run G)(pace:WilsonWindowReportingPace.Slow R.kit) {H:ℕ}(hp:0<H)(B:ℕ):
    let j:=WilsonMeasuredWindow.stop R.family.path.levels simple H
    ∀ᶠ r in trail, scale g B r ≤ r*(R.family.path.levels.clock.hatBeta (j r))^B:=by
  let j:=WilsonMeasuredWindow.stop R.family.path.levels simple H
  have sale:=WilsonPhysicalCutoffCurrency.temperature R simple pace hp g hg
  filter_upwards [sale.eventually (le_mem_nhds (by norm_num:(1/2:ℝ)<1)),
    (hg.conforms simple).eventually (ge_mem_nhds (by norm_num:(0:ℝ)<1/2)),hg.positive,self_mem_nhdsWithin] with r bill small gp rp
  let b:=R.family.path.levels.clock.hatBeta (j r)
  change (1/2:ℝ)≤b*(g r)^2 at bill
  have fitted : (g r)⁻¹≤b:=by
    apply (inv_le_iff_one_le_mul₀ gp).mpr
    have rel : (1:ℝ)*(g r)≤(b*g r)*(g r):=by nlinarith only [bill,small]
    exact le_of_mul_le_mul_right rel gp
  unfold scale
  rw [div_eq_mul_inv,←inv_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr gp.le) fitted _) (le_of_lt rp)

end YM.Integration.WilsonThermometerWeakPairClock
end
