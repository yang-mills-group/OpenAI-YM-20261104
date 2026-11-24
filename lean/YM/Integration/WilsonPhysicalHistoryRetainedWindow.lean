import YM.Integration.WilsonPhysicalHistoryRetainedGrant
import YM.RG01.Slack

/-! Both real adjacent clocks of the inherited old representation on the
existing physical run, before the cutoff, the torus, and the saved hard tests. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Function Filter Lattice RG Wilson Pressure PhysicalNext.Repeat.Legato
open scoped Topology Classical
variable {G : Gauge}

private theorem twice {x y : ℝ} (logx : 4≤Real.log x) (hx : 0<x) (hy : 1≤y) (h : y≤2*x) :
    radiusB y ≤ 2*radiusB x := by
  have ll : Real.log y≤Real.log x+1 := by
    refine (Real.log_le_log (zero_lt_one.trans_le hy) h).trans ?_
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hx.ne']
    linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have a : (radiusB y:ℝ) ≤ (Real.log y)^2+1 :=
    (Nat.ceil_lt_add_one (sq_nonneg (Real.log y))).le
  have b : (Real.log x)^2≤(radiusB x:ℝ) := Nat.le_ceil _
  have square := pow_le_pow_left₀ (Real.log_nonneg hy) ll 2
  have prop : (radiusB y:ℝ) ≤ 2*(radiusB x:ℝ) := by
    nlinarith only [square,a,b,mul_nonneg (sub_nonneg.mpr logx) (show 0≤Real.log x+2 by linarith)]
  exact_mod_cast prop

theorem physical_window (R : Run G) (simple : G.Simple) :
    ∀ᶠ m : ℕ in atTop, ∀ (N n : ℕ), m+1<N →
      let A:=R.alloy.B.a.clock
      (0<radiusB (A.hatBeta m)) ∧
      (R.family.path.rep N n (m+1)).p.B≤2*radiusB (A.hatBeta m) ∧
      ∀ d : ℕ,(Real.sqrt 2*Pert.Asymptotics.regulatorRun R.family N n (m+2))^(d+1) ≤ 1 := by
  let T:=R.alloy.B.a
  have rise:=RG01.Physical.hats simple T
  have large:= (Real.tendsto_log_atTop.comp rise).eventually_ge_atTop (4:ℝ)
  have width:= (Work.E01.radiusB_tendsto.comp rise).eventually_ge_atTop 1
  filter_upwards [large,width,rise.eventually_gt_atTop 0,(rise.comp (tendsto_add_atTop_nat 1)).eventually_ge_atTop 1,
    (rise.comp (tendsto_add_atTop_nat 2)).eventually_ge_atTop 4,RG01.Physical.nextHat simple T] with m logx wide hot one four step
  intro N n below
  have rep:=(R.makes.wilson.represents N n (m+1) (by omega)).vac
  have bank: (R.family.path.rep N n (m+1)).p.B=radiusB (T.clock.hatBeta (m+1)) := by
    change (R.family.path.rep N n (m+1)).p=R.family.path.levels.budget (m+1) at rep
    rw [rep]
    rfl
  refine ⟨wide,bank.trans_le (twice logx hot one step),?_⟩
  intro d
  have bud := (R.makes.wilson.represents N n (m+2) (by omega)).band.1
  change T.clock.hatBeta (m+2)/2 ≤ (R.family.path.rep N n (m+2)).beta at bud
  have genuine : 2 ≤ (R.family.path.rep N n (m+2)).beta := by
    change 4≤T.clock.hatBeta (m+2) at four
    linarith
  let g:=Real.sqrt (R.family.path.rep N n (m+2)).beta
  have hg:0<g:=Real.sqrt_pos.mpr (by linarith)
  change (Real.sqrt 2*g⁻¹)^(d+1) ≤ 1
  apply pow_le_one₀ (mul_nonneg (Real.sqrt_nonneg _) (inv_nonneg.mpr hg.le))
  rw [←div_eq_mul_inv]
  exact (div_le_one hg).mpr (Real.sqrt_le_sqrt genuine)

end YM.Integration.OriginalMarkedRunAction
