import YM.Integration.WilsonSeparatedPrefixMovingFiledFiscal
import YM.Integration.WilsonOriginalPublicRelativeGramKineticMesh
import YM.Integration.WilsonAddressedMixedOpticalMesh

/-! Compare the physical regulator at the measuring date with the continuum ruler. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointFourBookedCurrency
open RG16 RG16.Literal OPE Lattice Pert.Asymptotics PhysicalNext.Repeat.Legato
open WilsonOriginalPublicRelativeGramKineticMesh (thermal)
variable {G:Gauge}(R:Run G)
local notation "L" => R.family.path.levels
local notation "β" => (L).clock.hatBeta

theorem original (simple:G.Simple)(m K N per:ℕ)(mk:m≤K)(top:K≤N)(θ A:ℝ)(_hp:0<θ)(_ap:1≤A)
    (roof:β K*θ^2≤A)(cool:thermal R m ≤ 2*θ):
    let t:=regulatorRun R.family N per m
    0<t ∧ t≤4*θ ∧ θ ≤ (2*A+1)*t ∧ 0<regulatorRun R.family N per K:=by
  intro t
  let B:=R.family.path.β N per m
  have scalar:=R.makes.wilson.represents N per m (mk.trans top)
  have above:β m/2≤B:=scalar.band.1
  have below:B≤2*β m:=scalar.band.2
  have warm:1≤β m:=((L).fits.delayed m).le
  have positive:0<B:=lt_of_lt_of_le (half_pos (zero_lt_one.trans_le warm)) above
  have hm:0<Real.sqrt (β m):=Real.sqrt_pos.mpr (zero_lt_one.trans_le warm)
  have hB:0<Real.sqrt B:=Real.sqrt_pos.mpr positive
  have bsize:(Real.sqrt B)^2=B:=Real.sq_sqrt positive.le
  have hsize:(Real.sqrt (β m))^2=β m:=Real.sq_sqrt (zero_le_one.trans warm)
  have cmp:Real.sqrt (β m)≤2*Real.sqrt B:=by
    nlinarith only [above,bsize,hsize,hm,hB]
  have down:t≤2*thermal R m:=by
    change (Real.sqrt B)⁻¹ ≤ 2*(Real.sqrt (β m))⁻¹
    rw [←one_div,←div_eq_mul_inv,div_le_div_iff₀ hB hm,one_mul]
    exact cmp
  have mkp:β m≤β K:=WilsonStartup.Timing.hat_mono L (Gauge.slopeConstant_pos simple).le mk
  have dB:B*θ^2≤2*A:=calc
    _≤(2*β K)*θ^2:=mul_le_mul_of_nonneg_right (below.trans (by linarith only [mkp])) (sq_nonneg _)
    _=2*(β K*θ^2):=by ring
    _≤2*A:=by linarith only [roof]
  have posed:(θ*Real.sqrt B)^2≤2*A:=by rw [mul_pow,bsize,mul_comm];exact dB
  have wage:θ*Real.sqrt B≤2*A+1:=by nlinarith only [posed,sq_nonneg (θ*Real.sqrt B-1),_ap]
  constructor
  · exact inv_pos.mpr hB
  refine ⟨by linarith only [down,cool],?_,(WilsonSeparatedPrefixMovingFiledFiscal.heat R K N per top).1⟩
  change θ≤(2*A+1)*(Real.sqrt B)⁻¹
  rw [←div_eq_mul_inv,le_div_iff₀ hB]
  exact wage

theorem window (H δ θ t A:ℝ)(B:ℕ)(hp:0<θ)(hot:0<t)(hpos:0≤H)(ap:1≤A)
    (thin:δ≤θ^2)(thick:δ⁻¹≤H^B)(roof:H*θ^2≤A)(cash:t≤4*θ)(units:θ≤(2*A+1)*t)
    (low:(2*A+1)*θ≤1)(high:4*(16*A)^B*θ≤1):
    δ≤t ∧ δ⁻¹ ≤ t^(-(2*(B:ℝ)+1)):=by
  have tH:t^2≤16*θ^2:=by
    have sug:=pow_le_pow_left₀ hot.le cash 2
    nlinarith only [sug]
  have heat:H*t^2 ≤ 16*A:=calc
    _≤H*(16*θ^2):=mul_le_mul_of_nonneg_left tH hpos
    _=16*(H*θ^2):=by ring
    _≤16*A:=by linarith only [roof]
  have powers:=pow_le_pow_left₀ (mul_nonneg hpos (sq_nonneg t)) heat B
  have cold:(16*A)^B*t≤1:=calc
    _≤(16*A)^B*(4*θ):=mul_le_mul_of_nonneg_left cash (pow_nonneg (by linarith only [ap]) _)
    _≤1:=by linarith only [high]
  constructor
  · exact thin.trans (calc
      θ^2=θ*θ:=by ring
      _ ≤ θ*((2*A+1)*t):=mul_le_mul_of_nonneg_left units hp.le
      _=((2*A+1)*θ)*t:=by ring
      _≤1*t:=mul_le_mul_of_nonneg_right low hot.le
      _=t:=one_mul t)
  · have funded:H^B*(t^(2*B)*t)≤1:=calc
      _=(H*t^2)^B*t:=by rw [mul_pow,pow_mul];ring
      _≤(16*A)^B*t:=mul_le_mul_of_nonneg_right powers hot.le
      _≤1:=cold
    have priced:H^B≤(t^(2*B)*t)⁻¹:=by
      rw [←one_div,le_div_iff₀ (mul_pos (pow_pos hot _) hot)]
      exact funded
    apply thick.trans (priced.trans_eq ?_)
    have cast:2*(B:ℝ)+1=((2*B+1:ℕ):ℝ):=by norm_cast
    rw [Real.rpow_neg hot.le,cast,Real.rpow_natCast,pow_succ]

end YM.Integration.WilsonPositionProgramTrialPublicJointFourBookedCurrency
