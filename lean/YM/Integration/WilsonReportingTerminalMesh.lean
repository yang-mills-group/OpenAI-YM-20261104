import YM.Integration.WilsonReportingTerminalShiftConditional

/-! One last-block spatial mesh pays every prescribed power of the actual
ultraviolet Wilson coupling, uniformly in the finite period. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportingTerminalMesh
open Function Filter Lattice RG Source RG05Readout PhysicalNext.Repeat.Legato Pert.Asymptotics
open scoped Topology Classical
variable {G:Gauge} (R:Run G)

theorem decay (q:ℕ) :
    Tendsto (fun N=>R.family.S.a N*(R.family.path.levels.clock.hatBeta N)^q) atTop (𝓝 0) := by
  let S:=R.family.S
  let c:=R.family.path.levels.clock.bar
  let h:=G.slopeConstant
  let B:=|c|+|h|
  have pos:0≤B:=add_nonneg (abs_nonneg _) (abs_nonneg _)
  have raw:=((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (n:=q)).comp S.divergent).const_mul (B^q)
  rw [mul_zero] at raw
  refine squeeze_zero' (.of_forall fun N=>mul_nonneg (S.a_pos _).le (pow_nonneg (zero_le_one.trans (R.family.path.levels.fits.delayed N).le) _)) ?_ raw
  filter_upwards [S.divergent.eventually_ge_atTop 1] with N large
  have base:0≤S.scale N:=zero_le_one.trans large
  have temp:R.family.path.levels.clock.hatBeta N≤B*S.scale N:=by
    change c+h*S.scale N≤(|c|+|h|)*S.scale N
    have h1: c ≤ |c| * S.scale N:=(le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) large)
    rw [add_mul]
    exact add_le_add h1 (mul_le_mul_of_nonneg_right (le_abs_self _) base)
  have mesh:S.a N=Real.exp (-S.scale N):=by
    rw [Real.exp_neg,Schedule.scale,Real.exp_log (inv_pos.mpr (S.a_pos _)),inv_inv]
  change S.a N*(R.family.path.levels.clock.hatBeta N)^q≤B^q*(S.scale N^q*Real.exp (-S.scale N))
  calc _≤S.a N*(B*S.scale N)^q:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans (R.family.path.levels.fits.delayed N).le) temp _) (S.a_pos _).le
       _=_:=by rw [mesh,mul_pow];ring

theorem original (simple:G.Simple)
    (slow:∀j,((R.family.S.block j).val:ℝ)≤Real.log (Lambda R.family.path.levels j))
    (q:ℕ) {C ε:ℝ} (c0:0≤C) (ep:0<ε) :
    ∀ᶠt:ℕ in atTop,∀per:ℕ,C*R.family.S.a t≤ε*regulatorRun R.family (t+1) per (t+1)^q := by
  let A:=R.family.path.levels
  let B:=C*(2:ℝ)^(q+1)
  have limit:=((decay R (q+1)).comp (tendsto_add_atTop_nat 1)).const_mul B
  rw [mul_zero] at limit
  filter_upwards [limit.eventually (ge_mem_nhds ep)] with t tiny per
  let β:=A.clock.hatBeta (t+1)
  let h:=A.clock.hatBeta t
  let b:=R.family.path.β (t+1) per (t+1)
  let ℓ:ℝ:=(R.family.S.block t).val
  have hp:1≤h:=(A.fits.delayed _).le
  have old:1≤β:=(A.fits.delayed _).le
  have bp:0<b:=RG02.Actual.coupling_pos R.makes.wilson le_rfl
  have cap:b≤2*β:=(R.makes.wilson.represents (t+1) per (t+1) le_rfl).band.2
  have current:h≤β:=WilsonStartup.Timing.hat_mono A (Gauge.slopeConstant_pos simple).le t.le_succ
  have hlog:Real.log h≤h-1:=Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hp)
  have more:Real.log (2+Real.log h)≤2+Real.log h-1:=Real.log_le_sub_one_of_pos (by have z:=Real.log_nonneg hp;linarith)
  have step:ℓ≤Real.log (2+Real.log h):=slow t
  have block:ℓ≤2*β:=by linarith only [hp,current,step,hlog,more]
  have root:Real.sqrt b≤2*β:=(Real.sqrt_le_left (by linarith only [old])).2 (by nlinarith [sq_nonneg (2*β-1)])
  have a:R.family.S.a t=ℓ*R.family.S.a (t+1):=by
    rw [Schedule.a_step];dsimp only [ℓ];field_simp
  change B*(R.family.S.a (t+1)*β^(q+1))≤ε at tiny
  have paid:C*R.family.S.a t*(Real.sqrt b)^q≤ε:=calc
    _ = C*(ℓ*R.family.S.a (t+1))*(Real.sqrt b)^q:=by rw [←a]
    _ ≤ C*((2*β)*R.family.S.a (t+1))*(2*β)^q:=mul_le_mul
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right block (R.family.S.a_pos _).le) c0)
      (pow_le_pow_left₀ (Real.sqrt_nonneg _) root _) (pow_nonneg (Real.sqrt_nonneg _) _) (mul_nonneg c0 (mul_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans old)) (R.family.S.a_pos _).le))
    _ = B*(R.family.S.a (t+1)*β^(q+1)):=by unfold B;rw [mul_pow,pow_succ,pow_succ];ring
    _ ≤ ε:=tiny
  change _≤ε*(Real.sqrt b)⁻¹^q
  rw [inv_pow,←div_eq_mul_inv,le_div_iff₀ (pow_pos (Real.sqrt_pos.mpr bp) _)]
  exact paid

end YM.Integration.WilsonReportingTerminalMesh
