import YM.Integration.WilsonMacroscopicRichApertureGeometry
import YM.Integration.WilsonLimitConstruction.FundedOriginalRun

/-! The selected terminal window is polynomial in this original physical inverse coupling before every torus and upper cutoff. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichApertureClock
open Filter Lattice Wilson RG OPE OPE.Orbits Spec RG16 RG16.Literal
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonMacroscopicRichApertureGeometry
open scoped Classical Topology
universe u
variable {G:Gauge} (R:Run G)

theorem original {T:Campaign R} (W:Campaign.Pillars R T) (simple:G.Simple) {δ:ℝ}
    (fund:FundedOriginalProperties.{u} simple δ W)
    (pace:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda R.family.path.levels m))
    (M B:ℝ)(hM:0<M)(hB:20<B)(h:ℕ)(s : ℝ) (hs : 0 ≤ s) : ∃ c : ℝ, 0 < c ∧ ∀ᶠ m:ℕ in atTop,
    let b:=port R.family (8*M) B (mul_pos (by norm_num) hM) m
    ∀N p:ℕ,b≤N →
    let x:=R.family.path.levels.clock.hatBeta (b+1)
    let L:=WilsonMacroscopicRichAperture.size R N p b m s
    (radius R N p b h L:ℝ)≤c*x^3 :=by
  let S:=R.family.S
  let A:=R.family.path.levels
  let γ:=G.slopeConstant
  have γp:0<γ:=Gauge.slopeConstant_pos simple
  let k:ℝ:=2*(s+2)/γ+1
  have kp:0<k:=by dsimp [k];positivity
  refine ⟨10*k+4+stencil R h,by positivity,?_⟩
  let b:=port R.family (8*M) B (mul_pos (by norm_num) hM)
  have height:=port_height R.family simple (8*M) B (mul_pos (by norm_num) hM) (by linarith only [hB]) pace
  have deep:=height.2.eventually (lt_mem_nhds (show (1/2:ℝ)<1 by norm_num))
  have low:=height.1.eventually (S.divergent.eventually_ge_atTop γ⁻¹)
  filter_upwards [deep,low,S.divergent.eventually_gt_atTop 0] with m depth level positive
  intro b' N p live x L
  have bm:b'=b m:=rfl
  have half:(1/2:ℝ)*S.scale m≤S.scale b':=(le_div_iff₀ positive).mp depth.le
  let y:=A.clock.hatBeta b'
  have expr:y=A.clock.bar+γ*S.scale b':=rfl
  have bar:=A.clock.bar_pos
  have oneY:1≤y:=by rw [expr];nlinarith only [bar,mul_le_mul_of_nonneg_left level γp.le,mul_inv_cancel₀ γp.ne']
  have spread:y≤x:=WilsonStartup.Timing.hat_mono A γp.le (Nat.le_succ b')
  have xp:1≤x:=oneY.trans spread
  have x0:0≤x:=zero_le_one.trans xp
  have tm:S.scale m≤2*x/γ:=by apply (le_div_iff₀ γp).mpr;nlinarith only [mul_le_mul_of_nonneg_left half γp.le,spread,expr,bar]
  let P:=R.family.path.rep N p b'
  have same: P.p=A.budget b':=(R.makes.wilson.represents N p b' live).vac
  have expn:P.p.supportExponent=100:=(congrArg BudgetPoint.supportExponent same).trans (fund.2.1.paid.fixed b')
  have len:(L:ℝ)≤k*x:=by
    change (⌈((s+2)*S.scale m)/P.p.supportExponent⌉₊:ℝ)≤k*x
    rw [expn]
    apply (Nat.ceil_lt_add_one (by positivity)).le.trans
    calc (s+2)*S.scale m/100+1 ≤ (s+2)*S.scale m+1:=by nlinarith only [mul_nonneg (show 0≤ s+2 by linarith) positive.le]
         _ ≤ (s+2)*(2*x/γ)+x := add_le_add (mul_le_mul_of_nonneg_left tm (by linarith)) xp
         _ = k*x := by unfold k;ring
  have lg:Real.log y≤x:=(Real.log_le_sub_one_of_pos (zero_lt_one.trans_le oneY)).trans (by linarith only [spread])
  have bb:(P.p.B:ℝ)≤2*x^2:=by
    rw [show P.p.B=(A.budget b').B from congrArg BudgetPoint.B same]
    change (⌈(Real.log y)^2⌉₊:ℝ)≤_
    apply (Nat.ceil_lt_add_one (sq_nonneg _)).le.trans
    nlinarith only [pow_le_pow_left₀ (Real.log_nonneg oneY) lg 2,one_le_pow₀ xp (n:=2)]
  have xx:x^2≤x^3:=pow_le_pow_right₀ xp (by decide)
  have xxx:1≤x^3:=one_le_pow₀ xp
  unfold radius
  push_cast
  apply max_le
  · calc (L:ℝ)*(4*(P.p.B:ℝ)+2)+2*P.p.B ≤ (k*x)*(10*x^2)+4*x^2 := by
          apply add_le_add (mul_le_mul len _ (by positivity) (mul_nonneg kp.le x0)) _
          · nlinarith only [bb,one_le_pow₀ xp (n:=2)]
          · linarith only [bb]
         _ ≤ (10*k+4+stencil R h)*x^3 :=by nlinarith only [xx,mul_nonneg (Nat.cast_nonneg (stencil R h):0≤(stencil R h:ℝ)) (pow_nonneg x0 3)]
  · exact (le_mul_of_one_le_right (Nat.cast_nonneg _ :0≤(stencil R h:ℝ)) xxx).trans (mul_le_mul_of_nonneg_right (by linarith only [kp]) (pow_nonneg x0 3))

end YM.Integration.WilsonMacroscopicRichApertureClock
