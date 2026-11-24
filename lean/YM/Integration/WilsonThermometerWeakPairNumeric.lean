import YM.Integration.WilsonThermometerWeakPairClock

/-! Only running powers pay the logarithms; the extra detector delay is freely
chosen after the filed input and output grades. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakPairNumeric
open Filter Set Trace.Pilot PhysMS GapsContact.Ascent GapsContact.Seams
open WilsonThermometerWeakPairClock
open scoped Topology
variable {G:Gauge}(simple:G.Simple)(g:ℝ→ℝ)(hg:Coupling G g)
include hg simple

theorem tariff (K:ℕ):∃C:ℝ,0<C ∧ ∀ᶠ r in trail,dock r^K≤C/(g r)^(2*K):=by
  let F:=9+|G.slopeConstant⁻¹|
  refine ⟨F^K,pow_pos (by dsimp [F];positivity) _,?_⟩
  filter_upwards [hg.running.eventually (ge_mem_nhds (show G.slopeConstant⁻¹<G.slopeConstant⁻¹+1 by linarith)),hg.positive,
    (hg.conforms simple).eventually (ge_mem_nhds zero_lt_one),
    (ge_mem_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with r cost gp gone small rp
  have n:0≤dock r:=zero_le_one.trans (dock_valid r ⟨rp,small⟩)
  have base:dock r*(g r)^2≤F:=by
    unfold dock;dsimp [F]
    have sq:(g r)^2≤1:=pow_le_one₀ gp.le gone
    nlinarith only [sq,cost,le_abs_self G.slopeConstant⁻¹]
  apply (le_div_iff₀ (pow_pos gp _)).mpr
  simpa only [pow_mul,←mul_pow] using pow_le_pow_left₀ (mul_nonneg n (sq_nonneg _)) base K

theorem errors (B h:ℕ):
    ∀ᶠ r in trail, let t:=scale g B r
      t≤(r/t)^(h+1) ∧ r^((h:ℝ)+1-(1/4:ℝ))/t^((h:ℝ)+(1/4:ℝ))≤(r/t)^(h+1):=by
  filter_upwards [ordered simple g hg B,hg.positive,self_mem_nhdsWithin,
    subpower_payment hg simple 1 1 zero_lt_one 1 zero_lt_one (B*(h+2)),
    subpower_payment hg simple 1 (1/2:ℝ) (by norm_num) 1 zero_lt_one B]
    with r later gp rp micro tiny
  change 0<r at rp
  let t:=scale g B r
  have tp:0<t:=rp.trans_le later
  have gpow:0<(g r)^B:=pow_pos gp _
  have ratio:r/t=(g r)^B:=by dsimp [t,scale];field_simp [rp.ne',gp.ne']
  have m:r≤(g r)^(B*(h+2)):=by simpa only [one_mul,Real.rpow_one] using micro
  have n:r^(1/2:ℝ)≤(g r)^B:=by simpa only [one_mul] using tiny
  change t≤(r/t)^(h+1) ∧ _≤(r/t)^(h+1)
  constructor
  · rw [ratio]
    apply (div_le_iff₀ gpow).mpr
    simpa only [pow_mul,pow_succ] using m
  · have low:r^(1/4:ℝ)≤t^(1/4:ℝ):=Real.rpow_le_rpow rp.le later (by norm_num)
    have joint:r^((h:ℝ)+1-(1/4:ℝ))/t^((h:ℝ)+(1/4:ℝ))≤(r/t)^h*r^(1/2:ℝ):=by
      rw [show (h:ℝ)+1-(1/4:ℝ)=((h:ℝ)+(1/2:ℝ))+(1/4:ℝ) by ring,
        Real.rpow_add rp,Real.rpow_add rp,Real.rpow_add tp,Real.rpow_natCast,Real.rpow_natCast,div_pow]
      apply (div_le_iff₀ (mul_pos (pow_pos tp _) (Real.rpow_pos_of_pos tp _))).mpr
      calc
        _ ≤ (r^h*r^(1/2:ℝ))*t^(1/4:ℝ):=mul_le_mul_of_nonneg_left low (by positivity)
        _ = _:=by field_simp [tp.ne']
    refine joint.trans ?_
    rw [←ratio] at n
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_left n (pow_nonneg (div_nonneg rp.le tp.le) _)
end YM.Integration.WilsonThermometerWeakPairNumeric
end
