import YM.Integration.WilsonOriginalRadialSpringTariff
import YM.Integration.WilsonOriginalPhysicalRadialDerivative

/-! Uniform cutoff and period price on the genuine cropped decoder. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalRadialDerivativeCalendar
open Function Finset Filter Set Labels Lattice Wilson RG Source Next.Foundations Push.Local
open PhysicalNext.Repeat.Legato Pert.Asymptotics WilsonFirstReceivedRadialStencil
open WilsonCapturedPrimaryAngles WilsonCapturedPrimaryPaid WilsonCapturedPrimaryCollar
open WilsonOriginalRadialSpringTariff WilsonOriginalPhysicalRadialDerivative
open scoped Classical Topology
variable {G:Gauge}(R:Run G)
local notation "H" => R.family.path
local notation "A" => R.family.params
private theorem fact_nonnegative {d:ℕ}(a:Probe G d)(k:ℕ):0≤WilsonOriginalRadialSpringTariff.factor H A a k:=by
  have pc:0≤pay G k:=sum_nonneg fun _ _=>abs_nonneg _
  unfold WilsonOriginalRadialSpringTariff.factor;positivity

/-- The order and field are fixed before the regulator tail. Its constant is independent
of the physical sample mesh exponent and all microscopic dates and periods. -/
theorem original (simple:G.Simple) {d:ℕ} (a:Probe G d)(target k:ℕ):
    ∀ᶠ i:ℕ in atTop,∀{N per:ℕ}(_live:i<N),
      let B:=(H).levels.budget i
      let g:=regulatorRun R.family N per (i+1)
      let r:=radiusAt R (N:=N) (per:=per) (i:=i) d target
      1≤B.supportExponent → 0<g ∧ g≤1 ∧ g^gap target 1*wallet A a r≤1 ∧
      B.threshold*(1+(r:ℝ))^2≤1 ∧ ∀(M:ℝ),0≤M →
        WilsonOriginalRadialSpringRemainder.bill H (N:=N) (p:=per) (i:=i) A B 0 r a k M*g^(2*k+1)
        ≤WilsonOriginalRadialSpringTariff.factor H A a k*M:=by
  let C:=1+|panelFee A a|
  have cp:1≤C:=le_add_of_nonneg_right (abs_nonneg _)
  let power:=max d ((d+4)*k)
  filter_upwards [WilsonCapturedPrimaryCourse.original R simple (grade target d 1) power
    (zero_le_one.trans cp) (by norm_num:0<(1:ℝ))] with i room
  intro N per live B g r fee
  have get:=room N per (Nat.succ_le_of_lt live) fee
  let u:=1+(r:ℝ)
  let β:=(H).β N per (i+1)
  have gp:0<g:=get.1
  have gc:g≤1:=get.2.1.trans (by norm_num)
  have width:B.threshold*u^2≤1:=get.2.2.2.1
  have price:C*g*u^power≤1:=get.2.2.2.2
  have up:1≤u:=le_add_of_nonneg_right (Nat.cast_nonneg _)
  have unity:0<gap target 1:=by unfold gap;omega
  have tg:g^gap target 1≤g:=by simpa only [pow_one] using pow_le_pow_of_le_one gp.le gc unity
  have wd:wallet A a r≤C*u^d:=by
    change 1+panelFee A a*u^d≤_
    dsimp [C]
    nlinarith only [one_le_pow₀ up (n:=d),mul_le_mul_of_nonneg_right (le_abs_self (panelFee A a))
      (pow_nonneg (zero_le_one.trans up) d)]
  have short:g^gap target 1*wallet A a r≤1:=by
    calc _ ≤ g*(C*u^d):=mul_le_mul tg wd (zero_le_one.trans (wallet_one ..)) gp.le
         _ ≤ C*g*u^power:=by rw [mul_left_comm g C,←mul_assoc]
                             gcongr
                             exact le_max_left ..
         _ ≤ 1:=price
  have use:g*u^((d+4)*k)≤1:=by
    calc _ ≤ (C*g)*u^power:=mul_le_mul (le_mul_of_one_le_left gp.le cp)
                                (pow_le_pow_right₀ up (le_max_right ..))
                                (pow_nonneg (zero_le_one.trans up) _) (mul_nonneg (zero_le_one.trans cp) gp.le)
         _ ≤ 1:=price
  refine ⟨gp,gc,short,width,?_⟩
  intro M mp
  have bp:0<β:=Overlay.beta_positive R.makes.wilson live
  have bal:β*g^2=1:=by
    change β*((Real.sqrt β)⁻¹)^2=1
    rw [inv_pow,Real.sq_sqrt bp.le,mul_inv_cancel₀ bp.ne']
  have beta:1≤β:=by nlinarith only [bal,mul_le_of_le_one_right bp.le (pow_le_one₀ gp.le gc (n:=2))]
  have sold:=WilsonOriginalRadialSpringTariff.bill H (N:=N) A B (0:Site (R.family.side i per)) r a k mp width beta
  calc _ ≤ (WilsonOriginalRadialSpringTariff.factor H A a k*β^k*u^((d+4)*k)*M)*g^(2*k+1):=mul_le_mul_of_nonneg_right sold (pow_nonneg gp.le _)
       _ = (WilsonOriginalRadialSpringTariff.factor H A a k*(β*g^2)^k*M)*(g*u^((d+4)*k)):=by rw [pow_succ,mul_pow,←pow_mul];ring
       _ ≤ _:=by
         rw [bal,one_pow,mul_one]
         exact mul_le_of_le_one_right (mul_nonneg (fact_nonnegative R a k) mp) use

theorem panel (simple:G.Simple) {d:ℕ}(F:Labels.Frame G d)(target k:ℕ):
    ∀ᶠ i:ℕ in atTop,∀a∈tests F,∀{N per:ℕ}(_live:i<N),
      let B:=(H).levels.budget i
      let g:=regulatorRun R.family N per (i+1)
      let r:=radiusAt R (N:=N) (per:=per) (i:=i) d target
      1≤B.supportExponent → 0<g ∧ g≤1 ∧ g^gap target 1*wallet A a r≤1 ∧
      B.threshold*(1+(r:ℝ))^2≤1 ∧ ∀(M:ℝ),0≤M →
        WilsonOriginalRadialSpringRemainder.bill H (N:=N) (p:=per) (i:=i) A B 0 r a k M*g^(2*k+1)
        ≤WilsonOriginalRadialSpringTariff.factor H A a k*M:=
  (Filter.eventually_all_finset (tests F)).2 fun a _=>original R simple a target k

end YM.Integration.WilsonOriginalRadialDerivativeCalendar
