import YM.Integration.WilsonOriginalCompactRafflePrice
import YM.Integration.WilsonOriginalOccupiedOptical

/-! The unmarked renderer at the actual posted support price uses the native regular budget, without the all-field Taylor factor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalOccupiedRaffleIndependent
open ConnectedActivityE6 RG Pressure Lattice PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Transit AllOrder.Transit.WheelP
open QuadraticLocal QuadraticLocal.Earn Mentor MintClock Push.PriceCompiler Org

open Filter
theorem halo {G:Gauge} (R:Run G)(simple:G.Simple):
    ∀ᶠ f:ℕ in atTop,(Willow.haloSlack (Pressure.radiusB (R.alloy.B.a.clock.hatBeta f)))⁻¹ ≤ R.alloy.B.a.clock.hatBeta f:=by
  have all:∀ᶠ t:ℝ in atTop,(Willow.haloSlack (Pressure.radiusB t))⁻¹ ≤ t:=by
    filter_upwards [Page.tender G 1 (by norm_num:0<(1:ℝ)) _ (Page.season G 1)] with x held
    rw [Burn.hat_this] at held
    exact held.trans ((min_le_right ..).trans_eq (Real.rpow_one _))
  exact (RG01.Physical.hats simple R.alloy.B.a).eventually all

theorem original {G:Gauge} (R:Run G) {φ:ℕ→ℕ}
    {D:PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel}
    (simple:G.Simple)(warm:Spill.Raffle.Warm G D R.alloy.delay φ)
    {m f N per k jet order shelf seats:ℕ} {π:ℕ→Layout G} {Γ:ℕ→Pace.Coin}
    {Ψ:(j:ℕ)→RG.Rep G (R.family.side j per)}
    (history:Concourse R.alloy R.kit R.T π Γ m N per k Ψ) (start:m ≤ f) (cut:f ≤ N)
    (level:jet ≤ R.alloy.B.a.clock.J f) (depth:order ≤ R.alloy.B.a.clock.J f)
    (use:shelf ≤ R.alloy.B.a.clock.J f) (count:seats ≤ R.alloy.B.a.clock.J f) (d:ℕ)
    (late:(eventually_atTop.mp (halo R simple)).choose ≤ f) :
    let P:=Ψ f
    let x:=R.alloy.B.a.clock.hatBeta f
    let σ:=Poetry.Agenda.seed D φ jet (R.alloy.B.a.clock.J f)
    let U:=Page.temperature G 1 x
    let g:=Coat.gStep P.beta
    let expense:=WilsonOriginalThreeCompactWallet.fee G P.p U g (σ/4) order seats shelf d
    Invoice.Supports P.p U (P.p.supportExponent+1) g σ (σ/4) ∧
      |expense|/Willow.haloSlack P.p.B ≤ 2^(order+shelf+1+d)*x^(d+2) := by
  intro P x σ U g expense
  let h:=order+shelf+1
  let halo:=Willow.haloSlack P.p.B
  let cash:=Invoice.price P.p U h seats (P.p.supportExponent+1) (σ/4) G
  have entry:=history.1.walk f start cut
  obtain ⟨fund,_⟩:=WilsonMovingMentorRaffleCourse.measured R warm history start level depth use count cut
  have tuning:Spes.Market.tuning (R.metals.p.profile (R.alloy.B.a.clock.J f)) P.p x:=by
    rw [entry.truep.point,←params_eq R.alloy.B.valid f]
    exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  have fixed:cash=Spill.Raffle.fundsOne G (R.metals.p.profile (R.alloy.B.a.clock.J f)) σ order shelf seats x:=
    Spill.Raffle.regular G _ σ order shelf seats P.p x tuning.2.2 tuning.2.1
  have fp:0 ≤ cash:=(Invoice.positive P.p U h fund.2.2.1 seats fund.2.2.2.2.2.2.1 G).le
  have hp:0<halo:=Willow.spare_pos _
  have one:1 ≤ x:=(R.alloy.B.a.fits.delayed f).le
  have prize:=warm _ _ (step_paid R.alloy.B.a f) _ (R.alloy.B.valid.pays f) jet level order depth shelf use seats count
  have tol:Mentor.Tolerance (R.alloy.B.a.clock.J f) ≤ 1:=by
    unfold Mentor.Tolerance
    exact (div_le_iff₀ (by positivity)).mpr (by rw [one_mul]; exact_mod_cast Nat.le_add_left 1 _)
  have cf:cash ≤ x:=by
    rw [fixed]
    exact prize.limit.trans ((min_le_right ..).trans ((Real.rpow_le_rpow_of_exponent_le one tol).trans_eq (Real.rpow_one _)))
  have haloFee:halo⁻¹ ≤ x:=by
    change (Willow.haloSlack P.p.B)⁻¹ ≤ x
    rw [tuning.2.1]
    exact (eventually_atTop.mp (YM.Integration.WilsonOriginalOccupiedRaffleIndependent.halo R simple)).choose_spec f late
  have money:cash/halo ≤ x^2:=by
    rw [div_eq_mul_inv,pow_two]
    exact mul_le_mul cf haloFee (inv_nonneg.mpr hp.le) (zero_le_one.trans one)
  have high:P.beta ≤ 2*x:=by
    rw [entry.beta]
    exact (R.makes.wilson.represents N per f cut).band.2
  have inv:g⁻¹ ≤ 2*x:=by
    change (Real.sqrt P.beta)⁻¹⁻¹ ≤ 2*x
    rw [inv_inv]
    apply (Real.sqrt_le_left (by linarith)).mpr
    have ext:0 ≤ (2*x)*(2*x-1):=mul_nonneg (by linarith) (by linarith)
    nlinarith
  have gp:0<g:=fund.1
  have ep:0 ≤ expense:=mul_nonneg (div_nonneg (by positivity) (pow_nonneg gp.le _)) fp
  refine ⟨fund,?_⟩
  calc
    |expense|/halo=(2:ℝ)^h*(g⁻¹)^d*(cash/halo):=by
      rw [abs_of_nonneg ep]
      dsimp only [expense,WilsonOriginalThreeCompactWallet.fee,cash,h,halo]
      simp only [inv_pow,div_eq_mul_inv]
      ring
    _ ≤ 2^h*(2*x)^d*x^2:=
      mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr gp.le) inv d) (by positivity))
        money (div_nonneg fp hp.le) (mul_nonneg (by positivity) (pow_nonneg (by linarith) _))
    _=2^(order+shelf+1+d)*x^(d+2):=by
      dsimp only [h]
      rw [pow_add,pow_add,mul_pow]
      ring

end YM.Integration.WilsonOriginalOccupiedRaffleIndependent
