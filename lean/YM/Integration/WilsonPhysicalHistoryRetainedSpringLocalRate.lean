import YM.Integration.WilsonPhysicalHistoryRetainedSpringLocalCourse
import YM.Integration.WilsonAxialRates

/-! The original 11/5 thermal allowance pays the support bill at a true
positive quadratic power even when the earlier period has already been fixed. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.OriginalMarkedRunAction
open AnalyticBridge VerifiedReset Collection Quotes
open Filter Finset Lattice RG Wilson RG.Supply Push.GridApprox.Attach OPE.Therm
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato Pert.Asymptotics
open scoped Classical Topology BigOperators
variable {G:Gauge}

private theorem local_clock (V:Levels G)(simple:G.Simple){v:ℝ}(hv:0<v):
    ∀ᶠ j:ℕ in atTop,hitConstant (((V.budget j).B+1)*OriginalMarkedLocalPurchase.width V)/
      (V.clock.hatBeta j)^(1/10:ℝ)≤v:=by
  let r:=OriginalMarkedLocalPurchase.width V
  let C:=∑'i:ℕ,polyExp i
  have hc:0≤C:=tsum_nonneg fun i=>(polyExp_pos i).le
  let k:=12*r+5
  have lim:=(WilsonAxialRates.controlled V simple k 1 4 0 (s:=1/10) (by norm_num)).const_mul C
  rw [mul_zero] at lim
  filter_upwards [lim.eventually (ge_mem_nhds hv)] with j pay
  let b:=(V.budget j).B
  let Y:=1+(WilsonAxialReach.reach V k 1 j:ℝ)
  have size:(((leg ((b+1)*r)*2+1:ℕ):ℝ))≤Y:=by
    dsimp [Y,WilsonAxialReach.reach,k,leg];push_cast
    nlinarith only [show 0≤(b:ℝ) by positivity]
  have K:hitConstant ((b+1)*r)≤Y^4*C:=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) size _) hc
  have pos:0≤(V.clock.hatBeta j)^(1/10:ℝ):=Real.rpow_nonneg (zero_lt_one.trans (V.fits.delayed j)).le (1/10)
  refine (div_le_div_of_nonneg_right K pos).trans ?_
  calc Y^4*C/(V.clock.hatBeta j)^(1/10:ℝ)=
       C*(Y^4*(sigmaU V j)^0/(V.clock.hatBeta j)^(1/10:ℝ)):=by rw [pow_zero,mul_one];ring
       _≤v:=pay

private theorem allow (V:Levels G)(j:ℕ):
    V.clock.allowance j=(V.clock.hatCoupling j)^2/(V.clock.hatBeta j)^(1/10:ℝ):=by
  let b:=V.clock.hatBeta j
  have bp:0<b:=zero_lt_one.trans (V.fits.delayed j)
  change ((Real.sqrt b)⁻¹)^((11:ℝ)/5)=((Real.sqrt b)⁻¹)^2/b^(1/10:ℝ)
  rw [Real.sqrt_eq_rpow,←Real.rpow_neg bp.le,←Real.rpow_mul bp.le,
    ←Real.rpow_natCast ((b^(-(1/2:ℝ))):ℝ) 2,←Real.rpow_mul bp.le,←Real.rpow_sub bp]
  norm_num

theorem spring_local_rate (R:Run G)(simple:G.Simple){ε:ℝ}(ep:0<ε):
    let V:=R.family.path.levels
    ∀ᶠj:ℕ in atTop,∀N per,j≤N→∀S:Support (R.family.side j per),∀b≤Time.forecastE V j,
      2*Real.exp 2*OriginalMarkedLocalPurchase.fee V j S (V.clock.allowance j+b)≤
       ε*S.card*(regulatorRun R.family N per j)^2:=by
  intro V
  let c:ℝ:=32*Real.exp 2*17^4
  have cp:0<c:=by dsimp [c];positivity
  filter_upwards [local_clock V simple (div_pos ep cp)] with j sub N per live S b paid
  let g:=regulatorRun R.family N per j
  let h:=V.clock.hatCoupling j
  let k:=hitConstant (((V.budget j).B+1)*OriginalMarkedLocalPurchase.width V)
  let β:=V.clock.hatBeta j
  have bp:0<β:=zero_lt_one.trans (V.fits.delayed j)
  have kn:0≤k:=by unfold k hitConstant;exact mul_nonneg (by positivity) (tsum_nonneg fun i=>(polyExp_pos i).le)
  have hn:0≤h:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have gn:=IterationFour.Currency.g_pos R.makes N per j live
  have gc:h≤2*g:=(IterationFour.Currency.hat_g R.makes N per j live).1
  have sq:h^2≤4*g^2:=by nlinarith [mul_self_le_mul_self hn gc]
  have an:0≤V.clock.allowance j:=Real.rpow_nonneg hn _
  have a:b≤V.clock.allowance j:=paid.trans ((mul_le_mul_of_nonneg_right
    ((Time.authorized G (V.params j)).1.trans (by norm_num:((64:ℝ)⁻¹)≤1)) an).trans_eq (one_mul _))
  have hw:c*(k/β^(1/10:ℝ))≤ε:=by
    rw [mul_comm];exact (le_div_iff₀ cp).mp sub
  have f:0≤2*Real.exp 2*(2*((S.card:ℝ)*17^4*k)):=by positivity
  change 2*Real.exp 2*(2*((S.card:ℝ)*17^4*(k*(V.clock.allowance j+b))))≤ε*S.card*g^2
  calc
    _=(2*Real.exp 2*(2*((S.card:ℝ)*17^4*k)))*(V.clock.allowance j+b):=by ring
    _≤(2*Real.exp 2*(2*((S.card:ℝ)*17^4*k)))*(2*V.clock.allowance j):=
      mul_le_mul_of_nonneg_left (by linarith only [a]) f
    _=(c*(k/β^(1/10:ℝ)))*(S.card:ℝ)*h^2/4:=by rw [allow V];dsimp [c,h,β];ring
    _≤ε*S.card*g^2:=by

      have product:=mul_le_mul (mul_le_mul_of_nonneg_right hw (by positivity:(0:ℝ)≤S.card))
        sq (sq_nonneg h) (mul_nonneg ep.le (by positivity))
      linarith only [product]

end YM.Integration.OriginalMarkedRunAction
