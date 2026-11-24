import YM.Integration.WilsonPhysicalHistoryRetainedSpringTariff
import YM.Integration.WilsonFundedMeasuredWindow
import YM.Integration.ActualRunAdmissionScales

/-! A uniform polynomial price for the previous independently prescribed action
at a single genuine site of the physical torus. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Filter Lattice Wilson RG Precision Comparison.RG02 Comparison.RG02.Assembly
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Physical WilsonLimitConstruction
open scoped Topology BigOperators Classical
variable {G : Gauge}

private theorem credits (A : Levels G) (simple : G.Simple) (T W : Credit) :
    ∀ᶠ j : ℕ in atTop, T.buy (zz A j) ≤ A.clock.hatBeta j ∧
      W.buy (zz A j)+zz A j*A.clock.loopCap j ≤ 3*A.clock.hatBeta j := by
  let square : Credit:=⟨2,1,le_rfl⟩
  filter_upwards [exp_at_band T A simple 2 (by norm_num),exp_at_band square A simple 2 (by norm_num),
    (stamp_lim A simple).eventually_ge_atTop 1,retaining_expense simple A W Credit.leanC 1 (by norm_num)] with j hT hS large error
  let x:=A.clock.hatBeta j
  have pos : 0<x:=zero_lt_one.trans (A.fits.delayed j)
  have band : A.clock.hatBeta j/2≤x:=by change x/2≤x; linarith
  have temp : ((Real.sqrt x)⁻¹)^(-(2:ℝ))=x:=by
    rw [Real.rpow_neg (by positivity),Real.rpow_two,inv_pow,inv_inv,Real.sq_sqrt pos.le]
  constructor
  · linarith only [Real.add_one_le_exp (T.buy (zz A j)),(hT x band).trans temp.le]
  · have mono : A.clock.monitor j ≤ x := by
      rw [time_change]
      apply le_trans _ ((hS x band).trans temp.le)
      apply Real.exp_le_exp.mpr
      change (zz A j-1)^2 ≤ 1*(zz A j)^2
      nlinarith only [large]
    have spin : W.buy (zz A j)+zz A j*A.clock.loopCap j ≤ 3*A.clock.monitor j := by
      simpa [Credit.leanC,Credit.buy,Real.rpow_one] using error
    linarith only [spin,mono]

def springGrowth (r : ℕ) : ℝ :=
  2*(Fintype.card PlaqAxes:ℝ)+36+9*(meterPre (r+1):ℝ)*2^(r+2)

theorem growth (R : Run G) (simple : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit)
    (T W : Credit) (r : ℕ) :
    ∀ᶠ m : ℕ in atTop,
      let A:=R.family.path.levels
      let j:=m+1
      springAllowance R T j r (W.buy (zz A j)+zz A j*A.clock.loopCap j) ≤
        springGrowth r*(A.clock.hatBeta j)^2 := by
  let A:=R.family.path.levels
  filter_upwards [(tendsto_add_atTop_nat 1).eventually (credits A simple T W)] with m spend
  let j:=m+1
  let x:=A.clock.hatBeta j
  let D:=A.params j
  have one : 1≤x:=(A.fits.delayed j).le
  have hot : 0≤x:=zero_le_one.trans one
  have paths:=D.paths_pos.le
  have extent : D.paths ≤ x := calc
    _ ≤ ActualRunAdmissionScales.profileCost A j := (ActualRunAdmissionScales.profileCost_components A j).2.1
    _ ≤ ((A.S.block m).val:ℝ) := ActualRunAdmissionScales.profileCost_le_block A m
    _ ≤ Real.log (A.clock.hatBeta m) := WilsonFundedMeasuredWindow.paced R slow m
    _ ≤ A.clock.hatBeta m := Real.log_le_self (zero_lt_one.trans (A.fits.delayed m)).le
    _ ≤ x := Push.Corrected.Last.band_le A simple (Nat.le_succ m)
  have direct : |D.clip.direct| ≤ 1 := by
    rw [abs_of_pos D.clip.quadratic_pos]
    exact Push.PriceCompiler.Canonical.direct_le_one (R.alloy.B.support.cap j j le_rfl).metric
  let a:ℝ:=Fintype.card PlaqAxes
  have ac : 0≤a:=Nat.cast_nonneg _
  have q : quadraticBill D.clip D.paths ≤ a*(2+(x*2)^2/2) := by
    unfold quadraticBill
    apply mul_le_mul_of_nonneg_left _ ac
    apply add_le_add ((mul_le_mul_of_nonneg_right direct (show (0:ℝ)≤2 by norm_num)).trans (by norm_num))
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact pow_le_pow_left₀ (by positivity) (by linarith only [extent]) _
  have h1:=mul_le_mul_of_nonneg_left (add_le_add q (mul_le_mul_of_nonneg_left extent (show (0:ℝ)≤24 by norm_num))) (show (0:ℝ)≤1/2 by norm_num)
  have h2:=mul_le_mul spend.1 (mul_le_mul_of_nonneg_left extent (show (0:ℝ)≤24 by norm_num))
    (show 0≤24*D.paths by positivity) hot
  let k:ℝ:=meterPre (r+1)
  let b:ℝ:=2^(r+2)
  have hk : 0≤k:=Nat.cast_nonneg _
  have hb : 0≤b:=by dsimp [b]; positivity
  have h3:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right spend.2 hb) hk) (show 0≤3*x by positivity)
  change (1/2:ℝ)*(quadraticBill D.clip D.paths+24*D.paths)+T.buy (zz A j)*(24*D.paths)+
    (3*x)*(k*((W.buy (zz A j)+zz A j*A.clock.loopCap j)*b)) ≤
    (2*a+36+9*k*b)*x^2
  have sq : 1≤x^2:=one_le_pow₀ one
  have xs : x≤x^2:=by nlinarith only [mul_nonneg hot (sub_nonneg.mpr one)]
  nlinarith only [h1,h2,h3,mul_nonneg ac (sub_nonneg.mpr sq),xs]

end YM.Integration.OriginalMarkedRunAction
