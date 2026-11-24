import YM.Integration.WilsonOriginalCompactRafflePrice
import YM.Integration.WilsonThermometerSameWalkBirthCurrency

/-! Use the first, unmasked conclusion of the original raffle at the actual
opened three-source wallet. The coupling power depends only on its pole. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedOpeningRaffle
open ConnectedActivityE6 RG Pressure Lattice PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Transit AllOrder.Transit.WheelP
open QuadraticLocal QuadraticLocal.Earn Mentor MintClock Push.PriceCompiler Org

theorem original {G:Gauge} (R:Run G) {φ:ℕ→ℕ}
    {D:PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel}
    (warm:Spill.Raffle.Warm G D R.alloy.delay φ)
    {m f N per k jet order shelf seats:ℕ} {π:ℕ→Layout G} {Γ:ℕ→Pace.Coin}
    {Ψ:(j:ℕ)→RG.Rep G (R.family.side j per)}
    (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ) (start:m≤f) (cut:f≤N)
    (level:jet≤R.alloy.B.a.clock.J f) (depth:order≤R.alloy.B.a.clock.J f)
    (shelfFit:shelf≤R.alloy.B.a.clock.J f) (slots:seats≤R.alloy.B.a.clock.J f) (d:ℕ):
    let P:=Ψ f
    let x:=R.alloy.B.a.clock.hatBeta f
    let σ:=Poetry.Agenda.seed D φ jet (R.alloy.B.a.clock.J f)
    let U:=Page.temperature G 1 x
    let g:=Coat.gStep P.beta
    let expense:=WilsonOriginalThreeCompactWallet.fee G P.p U g (σ/4) order seats shelf d
    |expense|/Willow.haloSlack P.p.B ≤ 10000*2^(order+shelf+1+d)*x^(d+9):=by
  intro P x σ U g expense
  let y:=R.alloy.B.a.clock.J f
  let H:=order+shelf+1
  let cash:=Invoice.price P.p U H seats (P.p.supportExponent+1) (σ/4) G
  have entry:=course.1.walk f start cut
  obtain ⟨fund,_⟩:=WilsonMovingMentorRaffleCourse.measured R warm course start level depth shelfFit slots cut
  have paid:=warm _ _ (step_paid R.alloy.B.a f) _ (R.alloy.B.valid.pays f)
    jet level order depth shelf shelfFit seats slots
  have tune:Spes.Market.tuning (R.metals.p.profile y) P.p x:=by
    rw [entry.truep.point,←params_eq R.alloy.B.valid f]
    exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  have issued:cash=Spill.Raffle.fundsOne G (R.metals.p.profile y) σ order shelf seats x:=
    Spill.Raffle.regular G _ _ order shelf seats P.p x tune.2.2 tune.2.1
  have x1:1≤x:=(R.alloy.B.a.fits.delayed f).le
  have x0:0≤x:=zero_le_one.trans x1
  have tol:Mentor.Tolerance y≤1:=by
    unfold Mentor.Tolerance
    exact (div_le_iff₀ (by positivity)).mpr (by rw [one_mul];exact_mod_cast Nat.le_add_left 1 y)
  have got:cash≤x:=by
    rw [issued]
    exact paid.limit.trans ((min_le_right ..).trans ((Real.rpow_le_rpow_of_exponent_le x1 tol).trans_eq (Real.rpow_one x)))
  have cp:0≤cash:=(Invoice.positive P.p U H fund.2.2.1 seats fund.2.2.2.2.2.2.1 G).le
  have ap:(Willow.haloSlack P.p.B)⁻¹≤10000*x^8:=by
    rw [entry.truep.point]
    exact WilsonThermometerSameWalkBirthCurrency.aperture R f
  have high:P.beta≤2*x:=by
    rw [entry.beta]; exact (R.makes.wilson.represents N per f cut).band.2
  have inv:g⁻¹≤2*x:=by
    change (Real.sqrt P.beta)⁻¹⁻¹≤2*x
    rw [inv_inv]
    apply (Real.sqrt_le_left (by linarith)).mpr
    nlinarith only [high,mul_nonneg (by linarith only [x1]:0≤2*x) (by linarith only [x1]:0≤2*x-1)]
  have ep:0≤expense:=mul_nonneg (div_nonneg (by positivity) (pow_nonneg fund.1.le _)) cp
  calc
    |expense|/Willow.haloSlack P.p.B=2^H*(g⁻¹)^d*cash*(Willow.haloSlack P.p.B)⁻¹:=by
      rw [abs_of_nonneg ep]
      dsimp only [expense,WilsonOriginalThreeCompactWallet.fee,H,cash]
      simp only [div_eq_mul_inv,inv_pow]
    _ ≤ 2^H*(2*x)^d*x*(10000*x^8):=by
      apply mul_le_mul _ ap (inv_nonneg.mpr (Willow.spare_pos _).le) (by positivity)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr fund.1.le) inv _) (by positivity)) got cp (by positivity)
    _ = 10000*2^(order+shelf+1+d)*x^(d+9):=by
      dsimp only [H];rw [pow_add,pow_add,mul_pow];ring

end YM.Integration.WilsonCapturedOpeningRaffle
