import YM.Integration.WilsonIndependentCollarOriginalDose

/-! Restore one genuine upper coupling and one optical engineering factor
per external grade. The exponent is chosen before any internal Taylor order. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarEngineeringClock
open Filter Function Finset Lattice RG Wilson Precision PhysicalNext PhysicalNext.Repeat Legato
open WilsonCoeffUV Pert.Asymptotics Real
open scoped Classical BigOperators Topology
variable {G:Gauge}

theorem original (R:Run G)(simple:G.Simple)(A:ℕ):
    ∃C:ℝ,0≤C ∧ ∀m K N per:ℕ,K≤N → m+1≤N →
      let L:=R.family.path.levels
      let H:=L.clock.hatBeta (m+1)
      let β:=R.family.path.β N per (m+1)
      L.S.scale K-L.S.scale m≤(A:ℝ)*(1+Real.log H) →
      (L.S.a m/L.S.a K)/regulatorRun R.family N per K ≤ C*(Real.sqrt β)^(2*A+1):=by
  let slope:=G.slopeConstant
  let M:=1+2*slope*(A:ℝ)
  have s:0<slope:=Gauge.slopeConstant_pos simple
  have M1:1≤M:=le_add_of_nonneg_right (mul_nonneg (mul_nonneg (by norm_num) s.le) (Nat.cast_nonneg A))
  refine ⟨Real.exp (A:ℝ)*2^A*(4*M),by positivity,?_⟩
  intro m K N per top base L H β span
  let βK:=R.family.path.β N per K
  have h1:1≤H:=(L.fits.delayed _).le
  have hp:0<H:=zero_lt_one.trans_le h1
  have beta0:0<β:=Overlay.beta_positive R.makes.wilson base
  have betaK:βK≤2*L.clock.hatBeta K:=(R.makes.wilson.represents N per K top).band.2
  have lower:H/2≤β:=(R.makes.wilson.represents N per (m+1) base).band.1
  have hit:H≤2*β:=by linarith only [lower]
  have drift:L.clock.hatBeta K=L.clock.hatBeta m+slope*(L.S.scale K-L.S.scale m):=by
    change _+_*L.S.scale K=(_+_*L.S.scale m)+_*(L.S.scale K-L.S.scale m);ring
  have forward:L.clock.hatBeta m≤H:=by
    change _+_*L.S.scale m≤_+_*L.S.scale (m+1)
    exact add_le_add_right (mul_le_mul_of_nonneg_left ((OPE.scale_mono R.family.S).monotone (Nat.le_succ m)) s.le) _
  have slow:1+Real.log H≤2*H:=by linarith only [Real.log_le_self hp.le,h1]
  have temperature:βK≤(4*M)*β:=calc
    _≤2*L.clock.hatBeta K:=betaK
    _≤2*(H+slope*((A:ℝ)*(2*H))):=by
      rw [drift]
      exact mul_le_mul_of_nonneg_left (add_le_add forward (mul_le_mul_of_nonneg_left
        (span.trans (mul_le_mul_of_nonneg_left slow (Nat.cast_nonneg A))) s.le)) (by norm_num)
    _=2*M*H:=by dsimp [M];ring
    _≤2*M*(2*β):=mul_le_mul_of_nonneg_left hit (by positivity)
    _=_:=by ring
  have hot:Real.sqrt βK≤(4*M)*Real.sqrt β:=calc
    _≤Real.sqrt ((4*M)*β):=Real.sqrt_le_sqrt temperature
    _=Real.sqrt (4*M)*Real.sqrt β:=Real.sqrt_mul (by positivity) _
    _≤_:=mul_le_mul_of_nonneg_right ((Real.sqrt_le_left (by positivity)).2 (by nlinarith [sq_nonneg (M-1)])) (Real.sqrt_nonneg _)
  have sizes:L.S.a m/L.S.a K=Real.exp (L.S.scale K-L.S.scale m):=by
    rw [Schedule.scale,Schedule.scale,Real.exp_sub,Real.exp_log (inv_pos.mpr (L.S.a_pos K)),
      Real.exp_log (inv_pos.mpr (L.S.a_pos m)),inv_div_inv]
  have length:L.S.a m/L.S.a K≤Real.exp (A:ℝ)*(2*β)^A:=calc
    _≤Real.exp ((A:ℝ)*(1+Real.log H)):=sizes.trans_le (Real.exp_monotone span)
    _=Real.exp (A:ℝ)*H^A:=by rw [mul_add,mul_one,Real.exp_add,Real.exp_nat_mul,Real.exp_log hp]
    _≤_:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp.le hit _) (Real.exp_pos _).le
  have power:β^A=(Real.sqrt β)^(2*A):=by rw [pow_mul,Real.sq_sqrt beta0.le]
  calc
    _=(L.S.a m/L.S.a K)*Real.sqrt βK:=by simp [regulatorRun,βK,div_eq_mul_inv]
    _≤(Real.exp (A:ℝ)*(2*β)^A)*((4*M)*Real.sqrt β):=mul_le_mul length hot (Real.sqrt_nonneg _) (by positivity)
    _=_:=by rw [mul_pow,power,pow_succ];ring

end YM.Integration.WilsonIndependentCollarEngineeringClock
end
