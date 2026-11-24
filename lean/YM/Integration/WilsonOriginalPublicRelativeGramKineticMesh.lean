import YM.Integration.WilsonOriginalPublicRelativeGramMatched
import YM.Integration.WilsonPositionProgramTrialOpticalBand
import YM.Integration.WilsonMaxwellThermometerKineticCorridor

/-! The physical Wilson coupling and the declared finite optical collar meet
the two-sided mesh conditions of the independently normalized reflected Gram. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramKineticMesh
open Filter RG Lattice Wilson PhysicalNext.Repeat.Legato Pert.Asymptotics XSpace
open Table Spec Climb Trace.Pilot PhysMS Extraction
open WilsonPositionProgramTrialOpticalBand
open WilsonPositionProgramPublicReflectedRead
open scoped Topology Classical
variable {G:Gauge}(R:Run G)(simple:G.Simple)
local notation "hat" => R.family.path.levels.clock.hatBeta
local notation "basis" => R.family.path.levels
local notation "β" => R.family.path.β
local notation "g" => regulatorRun R.family

def thermal (m:ℕ):ℝ:=(Real.sqrt (hat m))⁻¹

include simple in
theorem original_gauge (m k N p:ℕ)(mk:m≤k)(live:k≤N) :
    |g N p k|≤8*thermal R m := by
  have hp:0<hat m:=zero_lt_one.trans (R.family.path.levels.fits.delayed m)
  have hk:0<hat k:=zero_lt_one.trans (R.family.path.levels.fits.delayed k)
  have bp:0<β N p k:=Overlay.beta_positive R.makes.wilson live (p:=p)
  have hm:hat m≤hat k:=(Real.log_le_log_iff hp hk).mp
    (WilsonAdmissionScale.logarithm_monotone basis simple mk)
  have raw:hat k/2≤β N p k:= (R.makes.wilson.represents N p k live).band.1
  have upper:hat m≤64*β N p k:=by linarith
  have root:=Real.sqrt_le_sqrt upper
  rw [Real.sqrt_mul (by norm_num:0≤(64:ℝ)),show Real.sqrt 64=8 by norm_num] at root
  change |(Real.sqrt (β N p k))⁻¹|≤8*(Real.sqrt (hat m))⁻¹
  rw [abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr bp)),←one_div,←div_eq_mul_inv,
    div_le_div_iff₀ (Real.sqrt_pos.mpr bp) (Real.sqrt_pos.mpr hp),one_mul]
  exact root

variable (D:XSpace.Run){K:ℕ→ℕ}{stage:ℕ}(B:Band R D K stage)

include simple in
theorem original {A:ℝ}(ap:0≤A)(cut:Bracket R K A)(n:ℝ→ℕ)(late:Tendsto n trail atTop) :
    (∀r:ℝ,0<thermal R (B.reporter+n r)) ∧ Tendsto (fun r:ℝ=>thermal R (B.reporter+n r)) trail (𝓝 0) ∧
    (∀ᶠr:ℝ in trail,2*(-Real.log (thermal R (B.reporter+n r)))≤ -Real.log (D.step (B.mesh (n r))).spacing ∧
       -Real.log (D.step (B.mesh (n r))).spacing≤(4*A)*(-Real.log (thermal R (B.reporter+n r)))) ∧
    (∀ᶠr:ℝ in trail,∀N p,K (B.reporter+n r)≤N → |g N p (K (B.reporter+n r))|≤8*thermal R (B.reporter+n r)) := by
  have up:Tendsto (fun r:ℝ=>B.reporter+n r) trail atTop:=tendsto_atTop_mono (fun r=>Nat.le_add_left (n r) B.reporter) late
  have hp:∀r:ℝ,0<hat (B.reporter+n r):=fun r=>zero_lt_one.trans (R.family.path.levels.fits.delayed _)
  have logtop: Tendsto (fun r:ℝ=>Real.log (hat (B.reporter+n r))) trail atTop:=
    (WilsonAdmissionScale.logarithm_tendsto basis simple).comp up
  have hightop:Tendsto (fun r:ℝ=>hat (B.reporter+n r)) trail atTop:=by
    apply (Real.tendsto_exp_atTop.comp logtop).congr'
    filter_upwards with r
    exact Real.exp_log (hp r)
  refine ⟨fun r=>inv_pos.mpr (Real.sqrt_pos.mpr (hp r)),
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hightop),?_,?_⟩
  · filter_upwards [up.eventually cut,logtop.eventually_ge_atTop 2] with r price large
    have mesh:-Real.log (D.step (B.mesh (n r))).spacing=Real.log (R.family.S.a (B.reporter+n r)/R.family.S.a (K (B.reporter+n r))):=by
      rw [←B.spacing (n r),←Real.log_inv,inv_div]
    have money:-Real.log (thermal R (B.reporter+n r))=Real.log (hat (B.reporter+n r))/2:=by
      rw [thermal,Real.log_inv,neg_neg,Real.log_sqrt (hp r).le]
    have left:=price.2.1
    have right:=price.2.2
    change 2+Real.log (hat (B.reporter+n r))≤_ at left
    change _≤A*(2+Real.log (hat (B.reporter+n r))) at right
    rw [mesh,money]
    constructor
    · linarith
    · nlinarith [mul_nonneg ap (sub_nonneg.mpr large)]
  · filter_upwards [up.eventually cut] with r price
    exact fun N p live=>original_gauge R simple _ _ N p price.1.le live

end YM.Integration.WilsonOriginalPublicRelativeGramKineticMesh
