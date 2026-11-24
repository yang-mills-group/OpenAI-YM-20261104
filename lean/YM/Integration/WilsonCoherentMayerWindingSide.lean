import YM.Integration.WilsonCoherentMayerWindingTemperature

/-! Period decay of the actual polynomial support count in the deposited winding bill. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerWindingSide
open Filter Real
open scoped Topology

def fee (n e j:ℕ)(B a sigma:ℝ):ℝ:= B*(n:ℝ)^e*Real.exp (-(sigma*n))*
  ((n:ℝ)^4*((((n:ℝ)+n+1)^4*a+1)^j*Real.exp 1))

private theorem damp (t:ℕ)(sigma:ℝ)(hs:0<sigma):
    Tendsto (fun n:ℕ=>(n:ℝ)^t*Real.exp (-(sigma*n))) atTop (𝓝 0):=by
  have scaled:Tendsto (fun n:ℕ=>sigma*(n:ℝ)) atTop atTop:=tendsto_natCast_atTop_atTop.const_mul_atTop hs
  have stock:=(Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero t).comp scaled
  have earn:=stock.const_mul ((sigma^t)⁻¹)
  convert earn using 1
  · funext n
    simp [mul_pow,←mul_assoc,hs.ne']
  · simp

theorem purchased (e k:ℕ)(B cap sigma:ℝ)(hB:0≤B)(hcap:0≤cap)(hs:0<sigma)
    (ε:ℝ)(hε:0<ε):
    ∀ᶠ n:ℕ in atTop, ∀ j, j≤k → ∀ a, 0≤a → a≤cap → fee n e j B a sigma ≤ ε:=by
  let c:ℝ:=B*((3:ℝ)^4*cap+1)^k*Real.exp 1
  have stock:Tendsto (fun n:ℕ=>c*((n:ℝ)^(e+4+4*k)*Real.exp (-(sigma*n)))) atTop (𝓝 0):=by
    simpa using (damp (e+4+4*k) sigma hs).const_mul c
  filter_upwards [eventually_ge_atTop (1:ℕ),stock.eventually_lt_const hε] with n hn earned
  intro j hj a ha hja
  have n1:(1:ℝ)≤n:=by exact_mod_cast hn
  have n4:(1:ℝ)≤(n:ℝ)^4:=one_le_pow₀ n1
  have left:((n:ℝ)+n+1)^4*a+1≤((3:ℝ)^4*cap+1)*n^4:=by
    calc
      _ ≤ (3*(n:ℝ))^4*cap+n^4:=by gcongr; linarith
      _ = _ :=by ring
  have right:1≤((3:ℝ)^4*cap+1)*n^4:=
    one_le_mul_of_one_le_of_one_le (by nlinarith) n4
  have charge:(((n:ℝ)+n+1)^4*a+1)^j≤(((3:ℝ)^4*cap+1)*n^4)^k:=
    (pow_le_pow_left₀ (by positivity) left j).trans (pow_le_pow_right₀ right hj)
  refine le_trans ?_ earned.le
  unfold fee
  calc
    _≤B*(n:ℝ)^e*Real.exp (-(sigma*n))*
        ((n:ℝ)^4*((((3:ℝ)^4*cap+1)*n^4)^k*Real.exp 1)):=by gcongr
    _=c*((n:ℝ)^(e+4+4*k)*Real.exp (-(sigma*n))):=by simp [c,pow_add,pow_mul,mul_pow]; ring

end YM.Integration.WilsonCoherentMayerWindingSide
