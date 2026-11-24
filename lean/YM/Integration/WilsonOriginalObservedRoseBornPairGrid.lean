import YM.Integration.WilsonOriginalPublicEarnedGramHome
import YM.Integration.WilsonOriginalObservedRoseBornPairAperture
import YM.Integration.WilsonOriginalPublicEarnedGramWilsonTable
import YM.Integration.WilsonOriginalPublicRelativeGramNativePivot

/-! The physical reporting grid supplies the actual original kinetic bound at every finer top. At its own physical ruler it also places the independent held pair in the prescribed reflected neighborhood. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseBornPairGrid
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


open WilsonOriginalPublicRelativeGramKineticMesh (thermal)

theorem heat (simple:G.Simple)(temperature:Coupling G g):
    ∀ᶠr in trail,thermal R (Γ.date r) ≤ 2*g r:=by
  let c:=G.slopeConstant
  have cp:0<c:=G.slopeConstant_pos simple
  have start:=temperature.running.const_mul c
  change Tendsto (fun r=>c*(LogV r*(g r)^2)) trail (𝓝 (c*c⁻¹)) at start
  rw [mul_inv_cancel₀ cp.ne'] at start
  filter_upwards [self_mem_nhdsWithin (a:=(0:ℝ)),Γ.upper,temperature.positive,
    (temperature.conforms simple).eventually_lt_const zero_lt_one,
    start.eventually_const_lt (show (1/2:ℝ)<1 by norm_num)] with r rp fine gp small room
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

  have high:0<hat (Γ.date r):=zero_lt_one.trans ((C₀).path.levels.fits.delayed _)
  have ht:0<Real.sqrt (hat (Γ.date r)):=Real.sqrt_pos.2 high
  have loan:=mul_le_mul_of_nonneg_right base (sq_nonneg (g r))
  have native:(1/2:ℝ)≤(Real.sqrt (hat (Γ.date r))*g r)^2:=by
    rw [mul_pow,Real.sq_sqrt high.le]
    nlinarith only [room,loan]
  change (Real.sqrt (hat (Γ.date r)))⁻¹ ≤ 2*g r
  rw [←one_div,div_le_iff₀ ht]
  by_contra! bad
  have lt:Real.sqrt (hat (Γ.date r))*g r < 1/2:=by linarith only [bad]
  have under:=mul_self_lt_mul_self (mul_pos ht gp).le lt
  nlinarith only [under,native]

def depth (g:ℕ)(D out:ℕ):ℕ:=2*(2*g+2)+D+out

theorem original (simple:G.Simple)(temperature:Coupling G g)(D out:ℕ):
    let P:=depth Γ.stage D out
    ∃B:ℝ,0<B ∧ ∀ᶠr in trail,
      (r/(C₀).S.a (Γ.date r))^(1/8:ℝ)*(thermal R (Γ.date r))^P*((g r)⁻¹)^D ≤ B*(g r)^out:=by
  intro P
  let n:=2*(2*Γ.stage+2)
  let cap:=max 1 Γ.allowance
  refine ⟨cap*2^P,mul_pos (zero_lt_one.trans_le (le_max_left ..)) (pow_pos (by norm_num) _),?_⟩
  filter_upwards [heat Γ simple temperature,Γ.inverse,temperature.positive,
    (temperature.conforms simple).eventually_lt_const zero_lt_one,self_mem_nhdsWithin (a:=(0:ℝ))] with r fee inverse gt small rpos
  let Γr:=g r
  let y:=r/(C₀).S.a (Γ.date r)
  have gp:0<Γr:=gt
  have yp:0<y:=div_pos rpos ((C₀).S.a_pos _)
  have nn:0≤(Γr⁻¹)^n:=pow_nonneg (inv_pos.mpr gp).le _
  have room:y ≤ cap*(Γr⁻¹)^n:=by
    rw [inv_pow,←div_eq_mul_inv,le_div_iff₀ (pow_pos gp _)]
    exact inverse.trans (le_max_right ..)
  have cover:1≤cap*(Γr⁻¹)^n:=
    one_le_mul_of_one_le_of_one_le (le_max_left ..) (one_le_pow₀ (one_le_inv₀ gp |>.mpr small.le))
  have housing:y^(1/8:ℝ) ≤ cap*(Γr⁻¹)^n:=by
    by_cases short:y≤1
    · exact (Real.rpow_le_one yp.le short (by norm_num)).trans cover
    · apply le_trans _ room
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (le_of_not_ge short) (show (1/8:ℝ)≤1 by norm_num)
  have heat0:0≤thermal R (Γ.date r):=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have temp:(thermal R (Γ.date r))^P ≤ (2*Γr)^P:=pow_le_pow_left₀ heat0 fee _
  calc
    _ ≤ (cap*(Γr⁻¹)^n)*(2*Γr)^P*(Γr⁻¹)^D:=
      mul_le_mul_of_nonneg_right (mul_le_mul housing temp (pow_nonneg heat0 _)
        (mul_nonneg (zero_le_one.trans (le_max_left ..)) nn)) (pow_nonneg (inv_pos.mpr gp).le _)
    _ = _ :=by
      change cap*(Γr⁻¹)^n*(2*Γr)^(n+D+out)*(Γr⁻¹)^D=cap*2^(n+D+out)*Γr^out
      rw [mul_pow,pow_add Γr (n+D) out,pow_add Γr n D,inv_pow,inv_pow]
      field_simp [gp.ne']

end YM.Integration.WilsonOriginalObservedRoseBornPairGrid
