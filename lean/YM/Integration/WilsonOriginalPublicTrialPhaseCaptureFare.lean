import YM.Integration.WilsonOriginalPublicTrialPhaseCapture
import YM.Integration.WilsonOriginalPublicTrialPhaseAward

/-! The last grouped capture costs one original per-date rent restoration. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseCaptureFare
open Finset Function MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof MergeProof.Accent MergeProof.Menu Marker Ac
open GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open RG05Readout RG05Readout.Address RG05Readout.Many RG05Readout.Pantry
open OPE.Therm Push.GridApprox PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign
open WilsonOriginalPublicTrialPhaseAccumulated WilsonOriginalPublicTrialPhaseRace
open WilsonOriginalPublicTrialPhaseRay WilsonOriginalPublicTrialPhaseCenterMenu
open scoped Topology ContDiff BigOperators Classical
open WilsonOriginalPublicTrialPhaseLanding

def reserve (f δ B:ℝ):ℝ:=(1+8*(f+2)*B)/min 1 δ

theorem price {f δ B w:ℝ}(hf:0≤f)(hd:0<δ)(hB:1≤B)(hw:0<w)(cash:1/w≤B):
    let a:=4*(1/w)
    let r:=reserve f δ B
    0<r ∧ f*a≤r ∧ (WilsonOriginalPublicTrialPhaseRay.unit*r)⁻¹≤δ*WilsonOriginalPublicTrialPhaseLanding.first w ((f+2)*a):=by
  intro a r
  let h:=1+8*(f+2)*B
  have bp:0<B:=zero_lt_one.trans_le hB
  have hp:0<h:=by dsimp [h];positivity
  have mp:0 < min 1 δ:=lt_min zero_lt_one hd
  have access:h≤r:=by
    change h≤h/min 1 δ
    exact (le_div_iff₀ mp).2 (mul_le_of_le_one_right hp.le (min_le_left ..))
  have inc:B≤h:=by
    dsimp [h]
    nlinarith [mul_nonneg hf bp.le]
  have ap:0<a:=by dsimp [a];positivity
  have ac:a≤4*B:=by dsimp [a];gcongr
  have cap:(f+2)*a≤4*(f+2)*B:=by nlinarith [mul_le_mul_of_nonneg_left ac (by linarith:0≤f+2)]
  have rp:=hp.trans_le access
  have g0:1/h≤w:=by
    apply (div_le_iff₀ hp).2
    calc 1≤B*w:=(div_le_iff₀ hw).mp cash
      _≤w*h:=by nlinarith [mul_le_mul_of_nonneg_right inc hw.le]
  have g1:1/h≤1/(1+2*|(f+2)*a|):=by
    rw [abs_of_nonneg (mul_nonneg (by linarith) ap.le)]
    apply one_div_le_one_div_of_le (by positivity)
    dsimp [h]
    nlinarith
  have gu:1≤WilsonOriginalPublicTrialPhaseRay.unit:=by unfold WilsonOriginalPublicTrialPhaseRay.unit;linarith [WilsonOriginalPublicTrialPhaseArrears.factor_pos]
  refine ⟨rp,?_,?_⟩
  · apply le_trans _ access
    change f*a≤1+8*(f+2)*B
    nlinarith [mul_nonneg hf bp.le]
  · calc (WilsonOriginalPublicTrialPhaseRay.unit*r)⁻¹ ≤ r⁻¹:=by
           apply (inv_le_inv₀ (mul_pos WilsonOriginalPublicTrialPhaseRay.unit_pos rp) rp).2
           simpa only [one_mul] using mul_le_mul_of_nonneg_right gu rp.le
         _ = (min 1 δ)/h:=by change (h/min 1 δ)⁻¹=_;rw [inv_div]
         _ ≤ δ*(1/h):=by rw [div_eq_mul_inv,one_div];gcongr;exact min_le_right .. 
         _ ≤ δ*WilsonOriginalPublicTrialPhaseLanding.first w ((f+2)*a):=mul_le_mul_of_nonneg_left (le_min g0 g1) hd.le

end YM.Integration.WilsonOriginalPublicTrialPhaseCaptureFare
end
