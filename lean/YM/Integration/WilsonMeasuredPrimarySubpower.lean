import YM.Integration.WilsonMeasuredPrimaryWindow
import YM.Integration.WilsonOriginalOffsetRoomCost
import YM.Integration.WilsonOriginalAdjacentMicroscopicPrice

/-! The signed one-date projection expense is funded before the ultraviolet
cutoff and period. Both the original derivative factorial and the finite
section price have subpower growth on the enrolled schedule. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredPrimarySubpower
open Function Filter Set Lattice Wilson RG Source Labels Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Extra.Histories
open Push.PriceCompiler ThroughLaunch Roof Push.Local Graces Planned.GuardedAtom
open WilsonLimitConstruction WilsonReportLampForecast
open scoped Topology BigOperators Classical
universe u

private theorem factorial_paid (P:BudgetPoint) :
    (P.order.factorial:ℝ) ≤ WilsonRetainedMarkedInletRegular.cost P := by
  have idx:P.order≤P.power*P.order:=by
    simpa only [one_mul] using Nat.mul_le_mul_right P.order (show 1≤P.power by have h:=P.power_ge;omega)
  have fac:(P.order.factorial:ℝ)≤(P.power*P.order).factorial:=by exact_mod_cast Nat.factorial_le idx
  have base:1≤(6*(P.B:ℝ)+3)^(P.power*P.order):=
    one_le_pow₀ (by linarith only [show 0≤(P.B:ℝ) by positivity])
  have e:1≤Real.exp 1:=Real.one_le_exp (by norm_num)
  refine fac.trans ?_
  unfold WilsonRetainedMarkedInletRegular.cost
  nlinarith only [mul_le_mul_of_nonneg_right base
    (show 0≤((P.power*P.order).factorial:ℝ) by positivity),
    mul_le_mul_of_nonneg_left e
      (show 0≤(6*(P.B:ℝ)+3)^(P.power*P.order)*((P.power*P.order).factorial:ℝ) by positivity)]

private theorem width {G:Gauge} (R:Run G) (simple:G.Simple) (slow:WilsonWindowReportingPace.Slow R.kit)
    (i:ℕ) (nonzeroDate : 1 ≤ i) :
    authors R.alloy.B.a i ≤ 2+Real.log (R.alloy.B.a.clock.hatBeta i) := by
  obtain ⟨m,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (show i≠0 by omega)
  let A:=R.alloy.B.a
  have one:1≤A.clock.hatBeta m:=(A.fits.delayed m).le
  have pos:0<RG16.Lambda A m:=by dsimp [RG16.Lambda];linarith only [Real.log_nonneg one]
  calc
    _ ≤ (A.params (m+1)).columns := R.b.clock.sectionBudget _
    _ ≤ ((A.S.block m).val:ℝ) :=RG12.Commission.column_priced _ _
    _ ≤ Real.log (RG16.Lambda A m) := slow.2 m
    _ ≤ RG16.Lambda A m := (Real.log_le_sub_one_of_pos pos).trans (by linarith)
    _ ≤ RG16.Lambda A (m+1) := (RG16.Literal.lambda_mono R.family simple).monotone m.le_succ

theorem original {G:Gauge} (R:Run G) (simple:G.Simple) {T:Campaign R} (W:Campaign.Pillars R T)
    {δ:ℝ} (fund:FundedOriginalProperties.{u} simple δ W) (slow:WilsonWindowReportingPace.Slow R.kit)
    (room:Ready R.family.path.levels) (d:ℕ) {η:ℝ} (gain:0<η) :
    ∃ K:ℝ, 0<K ∧ ∀ᶠ i in atTop, ∀ {n:Side} (o:Site n),
      let C:=R.family
      let P:=R.alloy.B.a.budget i
      let x:=R.alloy.B.a.clock.hatBeta i
      let w:=Next.Foundations.price G (max P.order P.power)
      WilsonMeasuredPrimaryTariff.allowance P C.params (C.localSection d) o w ≤ K*x^η ∧
        WilsonMeasuredPrimaryTariff.cost P C.params (C.localSection d) o w ≤ K*x^η := by
  obtain ⟨j,hj⟩:=exists_nat_gt (2/η)
  have exponent:part j≤η/2:=by
    apply (div_le_iff₀ (by positivity:0<(j:ℝ)+1)).mpr
    have gap:2<(j:ℝ)*η:=(div_lt_iff₀ gain).mp hj
    nlinarith only [gap,gain]
  let C:=R.family
  let sec:=C.localSection d
  let A:=R.alloy.B.a
  let a:=η/4
  have ap:0<a:=by dsimp [a];positivity
  let h:=3+1/a
  have hp:0<h:=by dsimp [h];positivity
  let k:=WilsonMeasuredPrimaryWindow.bound C.params sec
  have kp:0<k:=by
    have fee:0≤readPrice C.params (C.labels.level d):=(by norm_num: (0:ℝ)≤1).trans (readPrice_pos ..)
    dsimp [k,WilsonMeasuredPrimaryWindow.bound]
    positivity
  refine ⟨k*h^2*Real.exp 1,by positivity,?_⟩
  filter_upwards [WilsonOriginalOffsetRoomCost.original R simple room j,eventually_ge_atTop 1]
    with i covered nonzeroDate n o
  let P:=A.budget i
  let x:=A.clock.hatBeta i
  let w:=Next.Foundations.price G (max P.order P.power)
  let y:=x^a
  have x1:1≤x:=(A.fits.delayed i).le
  have xp:0<x:=zero_lt_one.trans_le x1
  have y1:1≤y:=Real.one_le_rpow x1 ap.le
  have w0:0≤w:=zero_le_one.trans (Next.Foundations.price_one_le G _)
  have wx:w≤2+Real.log x:=width R simple slow i nonzeroDate
  have lb:Real.log x≤y/a:=Real.log_le_rpow_div xp.le ap
  have wm:1+w≤h*y:=by
    dsimp only [h];rw [add_mul];ring_nf at lb ⊢;linarith only [wx,lb,y1]
  have wt:(1+w)^2≤(h*y)^2:=pow_le_pow_left₀ (by linarith) wm 2
  have origin:(R.family.path.rep i 0 i).p=P:=(R.makes.wilson.represents i 0 i le_rfl).vac
  have f:(P.order.factorial:ℝ)≤Real.exp 1*x^(η/2):=by
    have small:=covered i 0 le_rfl
    rw [origin] at small
    exact (factorial_paid P).trans (small.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le x1 exponent) (Real.exp_pos _).le))
  have ex:y^2*x^(η/2)=x^η:=by
    change (x^a)^2*x^(η/2)=x^η
    rw [pow_two,←Real.rpow_add xp,←Real.rpow_add xp]
    congr 1
    dsimp [a];ring
  have price:k*((1+w)^2*(P.order.factorial:ℝ))≤k*h^2*Real.exp 1*x^η:=by
    calc
      _ ≤ k*((h*y)^2*(Real.exp 1*x^(η/2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul wt f (by positivity) (by positivity)) kp.le
      _ = k*h^2*Real.exp 1*(y^2*x^(η/2)) := by ring
      _ = _ := by rw [ex]
  obtain ⟨regular,signed⟩:=WilsonMeasuredPrimaryWindow.budget P C.params sec o w w0
    (fund.2.1.paid.fixed i)
  exact ⟨regular.trans price,signed.trans price⟩

end YM.Integration.WilsonMeasuredPrimarySubpower
end
