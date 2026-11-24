import YM.Integration.WilsonCoherentMayerCourseRate
import YM.Integration.WilsonCoherentMayerWindingGeometry

/-! Income of the signed change of coupling at the original marked order. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerMutationRate
open Filter Lattice RG Push QuadraticLocal QuadraticLocal.Earn ConnectedActivityE6 PhysicalNext.Repeat.Legato
open scoped Topology

/-- Both original earnings, the outgoing invoice and the production fee, can be
paid at the same declared Laurent order and on the actual physical temperature. -/
theorem purchased {G:Gauge} (R:Run G) (simple:G.Simple) (p:ℕ) {η ε:ℝ}
    (positive:0<η) (unit:η≤1) (allow:0<ε):
    ∀ᶠ i:ℕ in atTop, ∀ N per, i<N → ∀ Ω:ℝ, 0≤Ω →
      Ω≤MintClock.Page.reward (R.alloy.B.a.clock.hatBeta (i+1))
        (Beaming.grain (R.alloy.B.a.clock.J i)) →
      (R.alloy.B.a.clock.hatBeta (i+1))^Mentor.Tuition.need p (Mentor.Tolerance (R.alloy.B.a.clock.J i))*Ω^2 ≤
        ε*(Coat.gStep (R.family.path.rep N per (i+1)).beta)^((p:ℝ)+1-η):=by
  let A:=R.alloy.B.a
  let e:=((p:ℝ)+1-η)/2
  have c0:0<(2:ℝ)^e:=Real.rpow_pos_of_pos (by norm_num) e
  have rise:Tendsto A.clock.hatBeta atTop atTop:=
    tendsto_atTop_add_const_left _ _ (A.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  have heights:Tendsto (fun i:ℕ=>(A.clock.J i:ℝ)) atTop atTop:=
    (tendsto_natCast_atTop_atTop (R:=ℝ)).comp A.fits.deep
  filter_upwards [heights.eventually_ge_atTop (12/η),
    ((tendsto_rpow_atTop (show 0<η/4 by positivity)).comp (rise.comp (tendsto_add_atTop_nat 1))).eventually_ge_atTop
      ((2:ℝ)^e/ε)] with i high enough N per before Ω omega earned
  let x:=A.clock.hatBeta (i+1)
  have one:1≤x:=(A.fits.delayed (i+1)).le
  have xp:0<x:=zero_lt_one.trans_le one
  let t:=Beaming.grain (A.clock.J i)
  have paid:Ω≤x^t:=earned.trans (min_le_right ..)
  have tol:Mentor.Tolerance (A.clock.J i)=t:=by unfold t Mentor.Tolerance Beaming.grain;push_cast;rfl
  have thin:3*t≤η/4:=by
    change 3*(1/((A.clock.J i:ℝ)+1))≤η/4
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity)).2
    have h:12≤(A.clock.J i:ℝ)*η:=(div_le_iff₀ positive).1 high
    nlinarith only [h,positive]
  have small:x^(-(η/4))≤ε/(2:ℝ)^e:=by
    rw [Real.rpow_neg xp.le]
    calc
      (x^(η/4))⁻¹≤((2:ℝ)^e/ε)⁻¹:=inv_anti₀ (div_pos c0 allow) enough
      _=ε/(2:ℝ)^e:=inv_div ..
  let g:=Coat.gStep (R.family.path.rep N per (i+1)).beta
  have low:=WilsonCoherentMayerWindingGeometry.lower R N per (i+1) before
  have floor:((2*x)^(-e:ℝ))≤g^((p:ℝ)+1-η):=by
    have H:=Real.rpow_le_rpow low.1.le low.2 (show 0≤(p:ℝ)+1-η by linarith only [unit,Nat.cast_nonneg (α:=ℝ) p])
    change ((Real.sqrt (2*x))⁻¹)^((p:ℝ)+1-η)≤_ at H
    rw [Real.inv_rpow (Real.sqrt_nonneg _),Real.sqrt_eq_rpow,←Real.rpow_mul (by positivity : 0≤2*x),
      ←Real.rpow_neg (by positivity : 0≤2*x)] at H
    convert H using 2; dsimp [e]; ring
  calc
    x^Mentor.Tuition.need p (Mentor.Tolerance (A.clock.J i))*Ω^2
      ≤ x^Mentor.Tuition.need p t*(x^t)^2:=by
        rw [tol];exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ omega paid 2) (Real.rpow_nonneg xp.le _)
    _=x^(Mentor.Tuition.need p t+t*2):=by
      rw [←Real.rpow_mul_natCast xp.le t 2,←Real.rpow_add xp];norm_num
    _≤x^(-e+(-(η/4))):=by
      apply Real.rpow_le_rpow_of_exponent_le one
      unfold Mentor.Tuition.need AllOrder.Catch.graded
      dsimp [e];push_cast;linarith only [thin]
    _≤x^(-e)*(ε/(2:ℝ)^e):=by rw [Real.rpow_add xp];exact mul_le_mul_of_nonneg_left small (Real.rpow_nonneg xp.le _)
    _=ε*(2*x)^(-e):=by
      rw [Real.mul_rpow (by norm_num : 0≤(2:ℝ)) xp.le,Real.rpow_neg (by norm_num : 0≤(2:ℝ))]
      ring
    _≤ε*g^((p:ℝ)+1-η):=mul_le_mul_of_nonneg_left floor allow.le

/-- The complete joined old mark is billed against its own submitted input mass. -/
theorem tested {G:Gauge} (R:Run G) (simple:G.Simple) (p:ℕ) {η ε:ℝ}
    (positive:0<η) (unit:η≤1) (allow:0<ε):
    ∀ᶠ i:ℕ in atTop, ∀ N per, i<N → ∀ E:Earnings, ∀ L:Side, ∀ P P':BudgetPoint, ∀ Ω W h c:ℝ,
      E.Cashier G L P P' Ω W h → Ω≤MintClock.Page.reward (R.alloy.B.a.clock.hatBeta (i+1)) (Beaming.grain (R.alloy.B.a.clock.J i)) → 0≤c →
      E.fidelity=(R.alloy.B.a.clock.hatBeta (i+1))^Mentor.Tuition.need p (Mentor.Tolerance (R.alloy.B.a.clock.J i)) →
      E.fidelity*E.outFee G P'*(E.produce L*c) ≤
        ε*(Coat.gStep (R.family.path.rep N per (i+1)).beta)^((p:ℝ)+1-η)*c:=by
  filter_upwards [purchased R simple p positive unit allow] with i income N per before E L P P' Ω W h c cash fee c0 grade
  have parts:E.outFee G P'*(E.produce L*c)≤Ω^2*c:=calc
    _≤E.outFee G P'*(Ω*c):=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right cash.earns c0) cash.minted.le
    _≤Ω*(Ω*c):=mul_le_mul_of_nonneg_right cash.quote (mul_nonneg cash.paysAbove.le c0)
    _=Ω^2*c:=by ring
  calc
    E.fidelity*E.outFee G P'*(E.produce L*c)=E.fidelity*(E.outFee G P'*(E.produce L*c)):=by ring
    _≤E.fidelity*(Ω^2*c):=mul_le_mul_of_nonneg_left parts cash.bloom.le
    _=((R.alloy.B.a.clock.hatBeta (i+1))^Mentor.Tuition.need p (Mentor.Tolerance (R.alloy.B.a.clock.J i))*Ω^2)*c:=by rw [grade]; ring
    _≤_:=mul_le_mul_of_nonneg_right (income N per before Ω cash.paysAbove.le fee) c0

end YM.Integration.WilsonCoherentMayerMutationRate
