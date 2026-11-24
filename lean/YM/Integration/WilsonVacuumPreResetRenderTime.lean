import YM.Integration.WilsonVacuumPreResetRenderIncome
import YM.RG01Estimate.Reserves

/-! On the same elected course the reciprocal time fee is paid before the
fine physical coupling is raised to the retained power. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetRenderTime
open Filter RG Wilson WilsonStartup Pert.Asymptotics PhysicalNext.Repeat.Legato
open AnalyticBridge VerifiedReset RG01Estimate WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Physical WilsonCoeffUV.Bank.Mosaic WilsonLimitConstruction
open scoped Topology
variable {G:Gauge}

private theorem transfer {b g:ℝ}(bp:0<b)(gp:0<g)(charged:b≤2*(g^2)⁻¹):
    g≤2*(Real.sqrt b)⁻¹:=by
  have h:b*g^2≤2:=(le_div_iff₀ (by positivity : 0<g^2)).mp (by simpa [div_eq_mul_inv] using charged)
  have hs:(Real.sqrt b*g)^2≤(2:ℝ)^2:=by rw [mul_pow,Real.sq_sqrt bp.le];linarith
  have line:Real.sqrt b*g≤2:=(sq_le_sq₀ (by positivity) (by norm_num)).mp hs
  rw [←div_eq_mul_inv]
  exact (le_div_iff₀ (Real.sqrt_pos.mpr bp)).2 (by simpa [mul_comm] using line)

theorem original (R:Run G)(simple:G.Simple)(bar:RG01Estimate.Chart.Barrier R.alloy
    (fun _ i=>((i:ℝ)+1)⁻¹))(K:ℝ)(kp:0≤K){ε:ℝ}(ep:0<ε):
    let V:=R.family.path.levels
    ∀ᶠ m:ℕ in atTop,∀N per:ℕ,m<N→
      K*(regulatorRun R.family N per (m+1))^(11/4:ℝ)≤ε*Time.forecastE V m:=by
  intro V
  let s:ℝ:=11/4
  let t:ℝ:=1/16
  let excess:ℝ:=17/80
  have growth:=tendsto_rpow_atTop (show 0<excess by norm_num [excess])
  have deep:=V.fits.deep.eventually_ge_atTop 16
  filter_upwards [deep,(growth.comp (RG01.Physical.hats simple V)).eventually_ge_atTop
    (128*K*(2:ℝ)^s/ε),
    WilsonVacuumPreResetRenderIncome.original R simple (⟨2,1,le_rfl⟩:Credit) (by norm_num :(0:ℝ)<1)] with m stage wealthy income
  intro N per later
  let b:=V.clock.hatBeta m
  let g:=regulatorRun R.family N per (m+1)
  let T:=Time.base G (V.params m)
  have bp:1<b:=V.fits.delayed m
  obtain ⟨gp,_,_,_,charged⟩:=income N per later
  have cash:T≤b^t:=by
    apply (bar.base m).trans
    apply Real.rpow_le_rpow_of_exponent_le bp.le
    have h:(16:ℝ)≤V.clock.J m:=by exact_mod_cast stage
    change (((V.clock.J m:ℕ):ℝ)+1)⁻¹ ≤ (1:ℝ)/16
    rw [one_div]
    exact inv_anti₀ (by norm_num) (by linarith)
  have base:1+T≤2*b^t:=by
    have lo:1≤b^t:=Real.one_le_rpow bp.le (by norm_num [t])
    linarith
  have price:128*K*(2:ℝ)^s≤b^excess*ε:=(div_le_iff₀ ep).mp wealthy
  have look: (Real.sqrt b)⁻¹=b^(-(1/2:ℝ)):=by rw [Real.rpow_neg (zero_le_one.trans bp.le),Real.sqrt_eq_rpow]
  have fee:g^s≤(2:ℝ)^s*b^(-(1/2:ℝ)*s):=calc
    g^s≤(2*(Real.sqrt b)⁻¹)^s:=Real.rpow_le_rpow gp.le (transfer (zero_lt_one.trans bp) gp charged) (by norm_num [s])
    _=_:=by rw [look,Real.mul_rpow (by norm_num) (by positivity),←Real.rpow_mul (zero_le_one.trans bp.le)]
  have sc:K*g^s*(64*(1+T))≤ε*b^(-(1/2:ℝ)*(11/5)):=calc
    _≤ (128*K*(2:ℝ)^s)*(b^(-(1/2:ℝ)*s)*b^t):=by
      have h:=mul_le_mul (mul_le_mul_of_nonneg_left fee kp) (mul_le_mul_of_nonneg_left base (by norm_num :(0:ℝ)≤64))
        (mul_nonneg (by norm_num) (by linarith [Time.base_nonneg G (V.params m)] : 0≤1+T)) (by positivity)
      calc
        _≤(K*((2:ℝ)^s*b^(-(1/2:ℝ)*s)))*(64*(2*b^t)):=h
        _=_:=by ring
    _≤(b^excess*ε)*(b^(-(1/2:ℝ)*s)*b^t):=mul_le_mul_of_nonneg_right price (by positivity)
    _=ε*b^(-(1/2:ℝ)*(11/5)):=by
      rw [←Real.rpow_add (zero_lt_one.trans bp)]
      rw [show b^excess*ε*b^(-(1/2:ℝ)*s+t)=ε*(b^excess*b^(-(1/2:ℝ)*s+t)) by ring,←Real.rpow_add (zero_lt_one.trans bp)]
      norm_num [s,t,excess]
  have tpos:0≤T:=(Time.base_nonneg G (V.params m)).1
  have den:0<64*(1+T):=mul_pos (by norm_num) (by linarith)
  have result:K*g^s≤(ε*b^(-(1/2:ℝ)*(11/5)))/(64*(1+T)):=(le_div_iff₀ den).2 sc
  change K*g^s≤ε*((64:ℝ)⁻¹*(1+T)⁻¹*((Real.sqrt b)⁻¹)^(11/5:ℝ))
  rw [look,←Real.rpow_mul (zero_le_one.trans bp.le)]
  apply result.trans_eq
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

end YM.Integration.WilsonVacuumPreResetRenderTime
