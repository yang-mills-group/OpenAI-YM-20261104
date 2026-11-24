import YM.Integration.WilsonMacroscopicRichApertureClock
import YM.Integration.WilsonMacroscopicRichHeldLoss

/-! Engineering normalization of the actual captured output and the two sampled Wilson temperatures. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichReportingRate
open Filter Lattice Wilson RG OPE Spec RG16 RG16.Literal Pert.Asymptotics Real
open PhysicalNext.Repeat.Legato
open scoped Classical Topology
variable {G:Gauge} (R:Run G)

private theorem logs (s:G.Simple) (n:ℕ) {ε:ℝ}(he:0<ε) :
    ∀ᶠ m:ℕ in atTop,(Lambda R.family.path.levels m)^n≤ε*sqrt (R.family.path.levels.clock.hatBeta m):=by
  let A:=R.family.path.levels
  have grow:Tendsto A.clock.hatBeta atTop atTop:=tendsto_atTop_add_const_left _ _ (A.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos s))
  have dp:0<(3:ℝ)^n:=by positivity
  have small:=(isLittleO_log_rpow_rpow_atTop (n:ℝ) (s:=(1/2:ℝ)) (by norm_num)).bound (div_pos he dp)
  filter_upwards [grow.eventually small,(Real.tendsto_log_atTop.comp grow).eventually_ge_atTop (1:ℝ)] with m rate large
  let x:=A.clock.hatBeta m
  change 1≤log x at large
  have lp:0≤log x:=zero_le_one.trans large
  change ‖log x^(n:ℝ)‖≤ε/3^n*‖x^(1/2:ℝ)‖ at rate
  rw [Real.rpow_natCast,←Real.sqrt_eq_rpow,Real.norm_of_nonneg (pow_nonneg lp n),Real.norm_of_nonneg (sqrt_nonneg x)] at rate
  calc (Lambda A m)^n ≤ (3*log x)^n := pow_le_pow_left₀ (lambda_pos R.family m).le (by change 2+log x≤_;linarith) _
       _ = 3^n*(log x)^n := mul_pow ..
       _ ≤ 3^n*(ε/3^n*sqrt x) := mul_le_mul_of_nonneg_left rate dp.le
       _ = ε*sqrt x := by field_simp

/-- The reported and capture-adjacent couplings enter with their own original positive finite temperatures.
One extra coupling order buys the full engineering scale ratio at each fixed output height. -/
theorem original (simple:G.Simple)(pace:∀m,((R.family.S.block m).val:ℝ)≤log (Lambda R.family.path.levels m))
    (M B:ℝ)(hm:0<M)(hb:20<B)(h q:ℕ){ε:ℝ}(he:0<ε):∀ᶠ m:ℕ in atTop,
    let b:=port R.family (8*M) B (mul_pos (by norm_num) hm) m
    ∀N p,m≤N→(R.family.S.a b/R.family.S.a m)^h*(regulatorRun R.family N p (b+1))^(q+1)≤ε*(regulatorRun R.family N p m)^q:=by
  let S:=R.family.S
  let A:=R.family.path.levels
  let L:ℝ:=8*M
  have hl:0<L:=by dsimp [L];positivity
  let b:=port R.family L B hl
  let k:=⌈B+1⌉₊
  let n:=(k+2)*h
  let d:=L^h*2*4^q
  have dp:0<d:=by dsimp [d];positivity
  have depth:=(port_height R.family simple L B hl (by linarith only [hb]) pace).2.eventually (lt_mem_nhds (show (1/2:ℝ)<1 by norm_num))
  have raw:=logs R simple n (div_pos he dp)
  filter_upwards [depth,port_small R.family simple L B hl (by linarith only [hb]),
    outer_bound R.family simple L B hl (by linarith only [hb]) pace,S.divergent.eventually_gt_atTop 0,raw] with m farther earlier outer positive bill
  intro b' N p live
  have earlier' : b' + 1 < m := earlier
  have cut:b'+1≤N:=earlier'.le.trans live
  have half:(1/2:ℝ)*S.scale m≤S.scale b':=(le_div_iff₀ positive).mp farther.le
  let x:=A.clock.hatBeta m
  let β:=R.family.path.β N p (b'+1)
  let βm:=R.family.path.β N p m
  have mon:=WilsonStartup.Timing.hat_mono A (Gauge.slopeConstant_pos simple).le (Nat.le_succ b')
  have coarse:x≤2*A.clock.hatBeta (b'+1):=by
    have ab:x≤2*A.clock.hatBeta b':=by change A.clock.bar+G.slopeConstant*S.scale m≤2*(A.clock.bar+G.slopeConstant*S.scale b');nlinarith only [mul_le_mul_of_nonneg_left half (Gauge.slopeConstant_pos simple).le,A.clock.bar_pos]
    linarith only [ab,mon]
  have low:A.clock.hatBeta (b'+1)/2≤β:=(R.makes.wilson.represents N p (b'+1) cut).band.1
  have high:βm≤2*x:=(R.makes.wilson.represents N p m live).band.2
  have xp:0<x:=zero_lt_one.trans (A.fits.delayed m)
  have bp:0<β:=by linarith only [xp,coarse,low]
  have mp:0<βm:=RG02.Actual.coupling_pos R.makes.wilson live
  have bs:0<sqrt β:=sqrt_pos.2 bp
  have ms:0<sqrt βm:=sqrt_pos.2 mp
  have xs:0<sqrt x:=sqrt_pos.2 xp
  have bfirst:sqrt x≤2*sqrt β:=by
    have z:=sqrt_le_sqrt (show x≤4*β by linarith only [coarse,low]);rw [sqrt_mul (by norm_num : (0:ℝ)≤4)] at z;norm_num at z ⊢;exact z
  have bsecond:sqrt βm≤4*sqrt β:=by
    have z:=sqrt_le_sqrt (show βm≤16*β by linarith only [high,coarse,low,bp]);rw [sqrt_mul (by norm_num : (0:ℝ)≤16)] at z;norm_num at z ⊢;exact z
  let gb:=regulatorRun R.family N p (b'+1)
  let gm:=regulatorRun R.family N p m
  have gp:0≤gb:=inv_nonneg.mpr (sqrt_nonneg β)
  have gmpos:0≤gm:=inv_nonneg.mpr (sqrt_nonneg βm)
  have gx:gb≤2/sqrt x:=by have h':1/sqrt β≤2/sqrt x:=(div_le_div_iff₀ bs xs).2 (by simpa using bfirst);simpa [gb,β,regulatorRun,div_eq_mul_inv] using h'
  have gg:gb≤4*gm:=by have h':1/sqrt β≤4/sqrt βm:=(div_le_div_iff₀ bs ms).2 (by simpa using bsecond);simpa [gb,gm,β,βm,regulatorRun,div_eq_mul_inv] using h'
  let l:=Lambda A m
  have lp:1≤l:=le_of_lt ((by norm_num : (1:ℝ)<2).trans (lambda_up R.family m))
  have hpow:l^(B+1)≤l^k:=by simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le lp (Nat.le_ceil (B+1))
  have aperture:S.a b'/S.a m≤L*l^(k+2):=by
    apply outer.trans;change L*l^(B+1)*l^2≤_;rw [pow_add,←mul_assoc];gcongr
  have engineering:(S.a b'/S.a m)^h≤L^h*l^n:=by
    simpa [n,mul_pow,←pow_mul] using pow_le_pow_left₀ (div_pos (S.a_pos b') (S.a_pos m)).le aperture h
  change l^n≤ε/d*sqrt x at bill
  calc (S.a b'/S.a m)^h*gb^(q+1) = (S.a b'/S.a m)^h*gb*gb^q := by ring
       _ ≤ (L^h*(ε/d*sqrt x))*(2/sqrt x)*(4*gm)^q := by gcongr;exact engineering.trans (mul_le_mul_of_nonneg_left bill (pow_nonneg hl.le h))
       _ = ε*gm^q := by dsimp [d];rw [mul_pow];field_simp [xs.ne',hl.ne'];ring

end YM.Integration.WilsonMacroscopicRichReportingRate
