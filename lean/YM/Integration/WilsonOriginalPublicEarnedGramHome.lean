import YM.Integration.WilsonOriginalPublicEarnedGramWilsonTable
import YM.Integration.WilsonOriginalPublicRelativeGramNativePivot

/-! The physical reporting grid supplies the actual original kinetic bound at every finer top. At its own physical ruler it also places the independent held pair in the prescribed reflected neighborhood. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.WilsonOriginalPublicEarnedGramHome
open RG16 RG16.Literal RG16.Guarding OPE
open Filter Set Lattice Wilson RG Source Table Spec Climb Trace.Pilot PhysMS
open PhysicalNext.Repeat.Legato Extraction XSpace XSpace.Cirrus Pert.Asymptotics
open WilsonOriginalPublicRelativeGramFreePanel (pointsAt)
open WilsonOriginalPublicRelativeGramAddresses (shape)
open WilsonOriginalPublicRelativeGramNativeSites (bias light sample)
open WilsonPositionProgramPublicReflectedRead (lower)
open scoped Topology Classical
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    {F:Spec.Final R.family f S}{ℓ:Ultrafilter (ℕ×ℕ)}{h:ℕ}{g:ℝ→ℝ}
    (Γ:WilsonViewerReportingGrid.Grid (ℓ:=ℓ) F h g)
local notation "C₀" => R.family
local notation "hat" => (C₀).path.levels.clock.hatBeta

theorem thermal (simple:G.Simple)(heat:Coupling G g):
    ∀ᶠr in trail,∀{K N:ℕ}(per:ℕ),Γ.date r≤K→K≤N→|regulatorRun (C₀) N per K|≤8*g r:=by
  let c:=G.slopeConstant
  have cp:0<c:=G.slopeConstant_pos simple
  have start:=heat.running.const_mul c
  change Tendsto (fun r=>c*(LogV r*(g r)^2)) trail (𝓝 (c*c⁻¹)) at start
  rw [mul_inv_cancel₀ cp.ne'] at start
  filter_upwards [self_mem_nhdsWithin (a:=(0:ℝ)),Γ.upper,heat.positive,
    (heat.conforms simple).eventually_lt_const zero_lt_one,
    start.eventually_const_lt (show (1/2:ℝ)<1 by norm_num)] with r rp fine gp small room K N per before live
  have hot:(C₀).S.a (Γ.date r)≤r:=by
    have p:0<r:=rp
    have sq:(g r)^2≤1:=by
      nlinarith only [mul_nonneg (sub_nonneg.mpr small.le) (show 0≤1+g r by linarith only [gp])]
    simpa only [one_mul] using (div_le_iff₀ p).mp (fine.trans sq)
  have growing:LogV r≤(C₀).S.scale (Γ.date r):=by
    change Real.log r⁻¹≤Real.log ((C₀).S.a (Γ.date r))⁻¹
    exact Real.log_le_log (inv_pos.mpr rp) ((inv_le_inv₀ (show 0<r from rp) ((C₀).S.a_pos _)).mpr hot)
  have base:c*LogV r≤hat (Γ.date r):=(mul_le_mul_of_nonneg_left growing cp.le).trans
    (le_add_of_nonneg_left (C₀).path.levels.clock.bar_pos.le)
  have bp:0<(C₀).path.β N per K:=Overlay.beta_positive R.makes.wilson live
  have xp:0<hat (Γ.date r):=zero_lt_one.trans ((C₀).path.levels.fits.delayed _)
  have yp:0<hat K:=zero_lt_one.trans ((C₀).path.levels.fits.delayed _)
  have mono:hat (Γ.date r)≤hat K:=(Real.log_le_log_iff xp yp).mp
    (WilsonAdmissionScale.logarithm_monotone (C₀).path.levels simple before)
  have band:hat K/2≤(C₀).path.β N per K:= (R.makes.wilson.represents N per K live).band.1
  have raw:c*LogV r≤2*(C₀).path.β N per K:=by linarith only [base,mono,band]
  have fee:=mul_le_mul_of_nonneg_right raw (sq_nonneg (g r))
  have cap:(regulatorRun (C₀) N per K)^2*(C₀).path.β N per K=1:=cashable (C₀) R.makes live
  have pos:0<regulatorRun (C₀) N per K:=g_pos R.makes live
  rw [abs_of_pos pos]
  by_contra! no
  have higher:(8*g r)^2<(regulatorRun (C₀) N per K)^2:=by
    nlinarith only [mul_pos (sub_pos.mpr no) (show 0<regulatorRun (C₀) N per K+8*g r by positivity)]
  have excess:=mul_lt_mul_of_pos_right higher bp
  nlinarith only [fee,room,excess,cap]

theorem placement (a:Axis)(avoid:Finset E4)(simple:G.Simple)(heat:Coupling G g){rad:ℝ}(pos:0<rad):
    ∀ᶠr in trail,∀(M:Mesh){K:ℕ}(fk:Γ.date r≤K),(C₀).S.a K=r*M.spacing →
      dist (familiar (sample R avoid (pointsAt a) M fk r r)) (lower a)<rad:=by
  let δ:=fun r=>(C₀).S.a (Γ.date r)/r
  have positive:∀ᶠr in trail,0<r:=self_mem_nhdsWithin
  have dp:∀ᶠr in trail,0<δ r:=positive.mono fun r rp=>div_pos ((C₀).S.a_pos _) rp
  have fine:Tendsto δ trail (𝓝 0):=squeeze_zero' (dp.mono fun _ p=>p.le) Γ.upper
    (by simpa only [zero_pow (by decide:2≠0)] using (heat.conforms simple).pow 2)
  have positions:=WilsonOriginalPublicRelativeGramAddresses.limit avoid (pointsAt a) dp fine
  have reaches:=fine.mul_const ‖(light:Points 2)‖
  rw [zero_mul] at reaches
  filter_upwards [positive,dp,(Metric.tendsto_nhds.mp positions (rad/2) (half_pos pos)),
    reaches.eventually_lt_const (half_pos pos)] with r rp small seats slide M K fk metric
  rw [WilsonOriginalPublicRelativeGramNativeSites.coordinates R avoid (pointsAt a) M fk rp rp metric,
    div_self rp.ne',one_smul,WilsonPositionProgramPublicReflectedRead.placement]
  have paid:=WilsonOriginalPublicRelativeGramNativeSites.rent M small
  have size:|bias M (δ r)|≤δ r:=abs_le.mpr ⟨paid.1,paid.2.trans small.le⟩
  have move:dist (shape avoid (pointsAt a) (δ r)+bias M (δ r) • light) (shape avoid (pointsAt a) (δ r))
      ≤δ r*‖(light:Points 2)‖:=by
    rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right size (norm_nonneg _)
  have smallMove:=move.trans_lt slide
  have triangle:=dist_triangle (shape avoid (pointsAt a) (δ r)+bias M (δ r) • (light:Points 2))
    (shape avoid (pointsAt a) (δ r)) (pointsAt a)
  exact triangle.trans_lt (lt_of_lt_of_le (add_lt_add smallMove seats) (by linarith))

end YM.Integration.WilsonOriginalPublicEarnedGramHome
end
