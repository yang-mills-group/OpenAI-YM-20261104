import YM.Integration.WilsonReportRetainedRadius
import YM.Integration.WilsonWindowJointPurchase
import YM.Push.PRICE_COMPILER.Scene

/-! Prepay the varying angular order and directional power of the original
reporting schedule, before choosing its Wilson run. The retained-support
root price is sharpened to a subpower of the actual stage temperature,
uniformly before every period and cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportLampForecast
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Tree Pressure
open Extra.Iteration PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open ThroughLaunch Next.Foundations Push.PriceCompiler RG.Supply Input Next.Scheduling
open WilsonLimitConstruction.FundedCompanySelection WilsonReportRetainedAnchor
open scoped Classical BigOperators Topology
variable {G:Gauge}

def charge (v:Stage) (x:ℝ) : ℝ := (1+2*(radiusB x:ℝ))^(2*(v.power*v.order))
def part (j:ℕ):ℝ:=1/((j:ℝ)+1)

private theorem radial (v:Stage) (j:ℕ):
    ∀ᶠ x:ℝ in atTop,charge v x≤x^(part j) := by
  let n:=2*(v.power*v.order)
  have pos:0<part j:=by dsimp [part];positivity
  have small:=(isLittleO_log_rpow_rpow_atTop ((2*n:ℕ):ℝ) pos).def
    (show 0<(5^n:ℝ)⁻¹ by positivity)
  filter_upwards [small,Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_gt_atTop (1:ℝ)] with x h logx hx
  have logpos:0≤Real.log x:=by linarith
  have hpow:(Real.log x)^(2*n)≤(5^n:ℝ)⁻¹ * x^(part j):=by
    change ‖Real.log x^((2*n:ℕ):ℝ)‖≤(5^n:ℝ)⁻¹*‖x^(part j)‖ at h
    simpa only [Real.rpow_natCast,Real.norm_of_nonneg (pow_nonneg logpos _),
      Real.norm_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hx.le) _)] using h
  have ceil:(radiusB x:ℝ)≤(Real.log x)^2+1:=(Nat.ceil_lt_add_one (sq_nonneg _)).le
  have span:1+2*(radiusB x:ℝ)≤5*(Real.log x)^2:=by nlinarith [sq_nonneg (Real.log x-1)]
  calc
    charge v x ≤ (5*(Real.log x)^2)^n := pow_le_pow_left₀ (by positivity) span _
    _ = 5^n*(Real.log x)^(2*n) := by rw [mul_pow,←pow_mul]
    _ ≤ 5^n*((5^n:ℝ)⁻¹*x^(part j)) := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by rw [←mul_assoc,mul_inv_cancel₀ (by positivity),one_mul]

private theorem literal (a:Levels G) (k:ℕ) :
    reprice (a.budget k) (a.budget k).B=charge (a.params k) (a.clock.hatBeta k) := by
  let b:=radiusB (a.clock.hatBeta k)
  change ((1+((b*(4*b+2)+2*b:ℕ):ℝ))^(a.params k).power)^(a.params k).order=
    (1+2*(b:ℝ))^(2*((a.params k).power*(a.params k).order))
  push_cast
  rw [show 1+((b:ℝ)*(4*b+2)+2*b)=(1+2*(b:ℝ))^2 by ring,←pow_mul,←pow_mul]

def Ready (a:Levels G) : Prop := ∀ j:ℕ, ∀ᶠ k:ℕ in atTop,
    reprice (a.budget k) (a.budget k).B≤(a.clock.hatBeta k)^(part j)

def Eligible : Prediction G := fun {_} {_} {A} _=>Ready A.B.a

theorem prepaid (s:Sheet G) (price:MapPrices): WilsonFundedWindowMenu.Prepared (@Eligible G) s price := by
  intro C E flags programs wages baton
  refine ⟨0,?_⟩
  intro l hl D w u Z post scouts pocket θ stages P menu V quarter
  let F (n:ℕ) (x:ℝ):Prop:=∀i:Fin (n+1),∀j:Fin (n+1),charge (s.profile i) x≤x^(part j)
  have enough (n:ℕ):∀ᶠ x:ℝ in atTop,F n x:=by
    apply eventually_all.mpr;intro i
    apply eventually_all.mpr;intro j
    apply radial
  obtain ⟨W,hVW,_,grant⟩:=delay_extra V F (fun _ _ _=>True) enough (fun _ _=>by simp)
  refine ⟨W,hVW,?_⟩
  intro U hWU table wait priced B archive origins rank
  dsimp only
  intro η q exchange aux rider booth sheltered works divides j
  filter_upwards [B.a.fits.deep.eventually_ge_atTop j] with k later
  rw [literal,params_eq B.valid k]
  exact (grant U hWU).1 (B.a.clock.J (k+1)) (B.a.clock.hatBeta k) (B.valid.pays k)
    ⟨B.a.clock.J k,Nat.lt_succ_of_le (B.a.fits.mono (Nat.le_succ k))⟩
    ⟨j,Nat.lt_succ_of_le (later.trans (B.a.fits.mono (Nat.le_succ k)))⟩

theorem allPrices : WilsonFundedWindowMenu.AllPrices (@Eligible G):=
  fun s price=>prepaid s (ThroughLaunch.raging s price)

end YM.Integration.WilsonReportLampForecast
end

