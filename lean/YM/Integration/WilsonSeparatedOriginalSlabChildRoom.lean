import YM.Integration.WilsonSeparatedOriginalSlabChildSites

/-! The translated parent cap and the earlier cell are admitted at every sufficiently large original period. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabChildRoom
open Filter Lattice Wilson RG Source Extraction
open WilsonSeparatedOriginalSlabChildSites
variable {G:Gauge}(C:Family G)

def Room (b J:ℕ)(r cap:ℝ)(per:ℕ):Prop:=
  let H:=limit (C.S.oneStep b per) J
  2*H<(C.side (b+1) per).val ∧ 2*(C.S.a (b+1)*(2*(H:ℝ)+1))<C.S.radius per ∧ r*cap+2*C.S.a b<C.S.radius per

theorem original (b J:ℕ)(r cap:ℝ):∀ᶠper:ℕ in atTop,Room C b J r cap per:=by
  let H:=(C.S.block b).val+2*J
  filter_upwards [C.S.radius_diverges.eventually_gt_atTop (2*(C.S.a (b+1)*(2*(H:ℝ)+1))),
    C.S.radius_diverges.eventually_gt_atTop (r*cap+2*C.S.a b)] with per paid earlier
  have pos:=C.S.a_pos (b+1)
  have span:=C.S.span_side (b+1) per
  have double:(C.S.period per).val=2*C.S.radius per:=by unfold Schedule.radius;ring
  have real: (2:ℝ)*(H:ℝ)<((C.side (b+1) per).val:ℝ):=by
    apply (mul_lt_mul_iff_right₀ pos).mp
    rw [show C.S.a (b+1)*((C.side (b+1) per).val:ℝ)=2*C.S.radius per by rw [span,double]]
    nlinarith [show (0:ℝ) ≤ (H:ℝ) by positivity,C.S.radius_pos per]
  exact ⟨by exact_mod_cast real,paid,earlier⟩

end YM.Integration.WilsonSeparatedOriginalSlabChildRoom
