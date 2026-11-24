import YM.Integration.WilsonOlderSignedOneMarkPlant
import YM.Push.LOCAL_SPLITTING.Delay

/-! The original divided quiet allowance pays the all-group fees of a fixed
finite mark before either regulator. The support and source radius enter in
the same units as the planted word. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOlderSignedOneMarkRate
open Filter RG Wilson Lattice OPE OPE.Therm PhysicalNext.Repeat.Legato Pert.Asymptotics
open Push.Local Corona Source Labels
open scoped Topology

open private YM.Push.Local.power_delay YM.Push.Local.gasRate from YM.Push.LOCAL_SPLITTING.Delay

private theorem sites {G:Gauge} (C : Family G) (i : ℕ) :
    hitWidth (C.path.levels.budget i) ≤ 5^4*C.path.levels.clock.hatBeta i^8 := by
  let x := C.path.levels.clock.hatBeta i
  have one : 1≤x:=(C.path.levels.fits.delayed i).le
  have xp := zero_lt_one.trans_le one
  have bp : ((C.path.levels.budget i).B:ℝ) ≤ 2*x^2 := by
    change (⌈(Real.log x)^2⌉₊:ℝ) ≤ 2*x^2
    have bound:Real.log x≤x:=(Real.log_le_sub_one_of_pos xp).trans (by linarith)
    linarith only [(Nat.ceil_lt_add_one (sq_nonneg (Real.log x))).le,
      pow_le_pow_left₀ (Real.log_nonneg one) bound 2,one_le_pow₀ one (n:=2)]
  unfold hitWidth
  push_cast
  calc
    _ ≤ (5*x^2)^4 := pow_le_pow_left₀ (by positivity)
      (by linarith only [bp,one_le_pow₀ one (n:=2)]) _
    _ = 5^4*x^8 := by ring

theorem paid {G : Gauge} (R : Run G) (simple : G.Simple) (n q : ℕ) {C ε : ℝ}
    (hc : 0<C) (ep : 0<ε) :
    ∀ᶠ i : ℕ in atTop, ∀ N per, i≤N → ∀ m ≤ i, ∀ b : ℝ, 0≤b →
      b ≤ C * R.family.path.levels.clock.hatBeta i^n →
      (hitWidth (R.family.path.levels.budget i)*R.family.path.levels.clock.forcedAllowance i)*b/
        LocalComparison.forcedDivisor R.family i ≤ ε*(regulatorRun R.family N per m)^q := by
  let A:=R.family.path.levels
  have rise : Tendsto A.clock.hatBeta atTop atTop :=
    tendsto_atTop_add_const_left _ _ (A.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  let D := (5:ℝ)^4*C*2^q
  have dp : 0<D:=by dsimp [D];positivity
  filter_upwards [rise.eventually (YM.Push.Local.power_delay (D/ε) (8+n+q))] with i small
  intro N per cut m hm b b₀ bound
  let x := A.clock.hatBeta i
  let v := A.clock.forcedAllowance i
  have hκ : 0<Real.sqrt v:=Real.sqrt_pos.mpr (allowance_pos A.clock i)
  have xp : 1≤x:=(A.fits.delayed i).le
  have xn : 0<x:=zero_lt_one.trans_le xp
  have hx : 0<2*x := mul_pos zero_lt_two xn
  have fixed : (D/ε)*x^(8+n+q)*Real.sqrt v≤1:=small
  have small' : D*x^(8+n+q)*Real.sqrt v≤ε := by
    have he : (D*x^(8+n+q)*Real.sqrt v)/ε = (D/ε)*x^(8+n+q)*Real.sqrt v := by ring
    exact (div_le_one ep).mp (he.trans_le fixed)
  let β:=(R.family.path.rep N per m).beta
  have betapos : 0<β:=Overlay.beta_positive R.makes.wilson (hm.trans cut)
  have old : A.clock.hatBeta m≤x:=WilsonStartup.Timing.hat_mono A (Gauge.slopeConstant_pos simple).le hm
  have ceiling : β≤2*x := ((R.makes.wilson.represents N per m (hm.trans cut)).band.2).trans
    (mul_le_mul_of_nonneg_left old zero_le_two)
  have h1 : 1≤2*x:=by linarith only [xp]
  have link : (2*x)⁻¹≤regulatorRun R.family N per m :=
    inv_anti₀ (Real.sqrt_pos.mpr betapos) ((Real.sqrt_le_left hx.le).mpr
      (ceiling.trans (by rw [pow_two];exact le_mul_of_one_le_right hx.le h1)))
  have head : (hitWidth (A.budget i)*v)*b/Real.sqrt v = (hitWidth (A.budget i)*b)*Real.sqrt v := by
    apply (div_eq_iff hκ.ne').mpr
    calc
      _ = (hitWidth (A.budget i)*b)*(Real.sqrt v * Real.sqrt v) := by
        rw [Real.mul_self_sqrt (show 0≤v from (allowance_pos A.clock i).le)]
        ring
      _ = _ := by ring
  change (hitWidth (A.budget i)*v)*b/Real.sqrt v≤_
  rw [head]
  have all: ((5^4*x^8)*(C*x^n)*Real.sqrt v)*(2*x)^q ≤ ε := by
    calc
      _ = D*x^(8+n+q)*Real.sqrt v := by dsimp [D]; rw [mul_pow,pow_add,pow_add]; ring
      _ ≤ ε := small'
  have invoice := (le_div_iff₀ (pow_pos hx q)).mpr all
  calc
    (hitWidth (A.budget i)*b)*Real.sqrt v ≤ ((5^4*x^8)*(C*x^n))*Real.sqrt v :=
      mul_le_mul_of_nonneg_right (mul_le_mul (sites R.family i) bound b₀ (by positivity)) hκ.le
    _ ≤ ε/(2*x)^q := invoice
    _ ≤ ε*(regulatorRun R.family N per m)^q := by
      rw [div_eq_mul_inv,←inv_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr hx.le) link _) ep.le

end YM.Integration.WilsonOlderSignedOneMarkRate
