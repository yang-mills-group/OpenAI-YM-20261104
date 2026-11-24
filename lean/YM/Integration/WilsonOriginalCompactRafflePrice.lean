import YM.Integration.WilsonOriginalThreeCompactWallet
import YM.Integration.WilsonThermometerPrecontactInvoice

/-! The genuine original raffle finances the complete restored compact wallet at every period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCompactRafflePrice
open ConnectedActivityE6 RG Pressure Lattice PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Transit AllOrder.Transit.WheelP
open QuadraticLocal QuadraticLocal.Earn Mentor MintClock Push.PriceCompiler Org

theorem original {G:Gauge} (R:Run G) {φ:ℕ→ℕ}
    {D:PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel}
    (warm:Spill.Raffle.Warm G D R.alloy.delay φ)
    {m f N per k jet order shelf seats:ℕ} {π:ℕ→Layout G} {Γ:ℕ→Pace.Coin}
    {Ψ:(j:ℕ)→RG.Rep G (R.family.side j per)}
    (history:Concourse R.alloy R.kit R.T π Γ m N per k Ψ) (start:m ≤ f) (cut:f ≤ N)
    (level:jet ≤ R.alloy.B.a.clock.J f) (depth:order ≤ R.alloy.B.a.clock.J f)
    (use:shelf ≤ R.alloy.B.a.clock.J f) (count:seats ≤ R.alloy.B.a.clock.J f) (d:ℕ) :
    let P:=Ψ f
    let x:=R.alloy.B.a.clock.hatBeta f
    let σ:=Poetry.Agenda.seed D φ jet (R.alloy.B.a.clock.J f)
    let U:=Page.temperature G 1 x
    let g:=Coat.gStep P.beta
    let expense:=WilsonOriginalThreeCompactWallet.fee G P.p U g (σ/4) order seats shelf d
    Invoice.Supports P.p U (P.p.supportExponent+1) g σ (σ/4) ∧
      |expense|/Willow.haloSlack P.p.B ≤ 2^(order+shelf+1+d)*x^(d+Spill.Raffle.pad (order+shelf+1)) := by
  intro P x σ U g expense
  let h:=order+shelf+1
  let halo:=Willow.haloSlack P.p.B
  let cash:=Invoice.price P.p U h seats (P.p.supportExponent+1) (σ/4) G
  have entry:=history.1.walk f start cut
  obtain ⟨fund,raw⟩:=WilsonMovingMentorRaffleCourse.measured R warm history start level depth use count cut
  have tuning:Spes.Market.tuning (R.metals.p.profile (R.alloy.B.a.clock.J f)) P.p x:=by
    rw [entry.truep.point,←params_eq R.alloy.B.valid f]
    exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  have fixed:cash=Spill.Raffle.fundsOne G (R.metals.p.profile (R.alloy.B.a.clock.J f)) σ order shelf seats x:=
    Spill.Raffle.regular G _ σ order shelf seats P.p x tuning.2.2 tuning.2.1
  have fp:0 ≤ cash:=(Invoice.positive P.p U h fund.2.2.1 seats fund.2.2.2.2.2.2.1 G).le
  have hp:0<halo:=Willow.spare_pos _
  have money:cash/halo ≤ x^(Spill.Raffle.pad h):=by
    apply (div_le_iff₀ hp).mpr
    have usable:cash ≤ (Spill.allOver P.p)^h*cash:=
      le_mul_of_one_le_left fp (one_le_pow₀ (Spill.allOver_ge _))
    rw [fixed] at usable ⊢
    exact usable.trans raw
  have one:1 ≤ x:=(R.alloy.B.a.fits.delayed f).le
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
    _ ≤ 2^h*(2*x)^d*x^(Spill.Raffle.pad h):=
      mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr gp.le) inv d) (by positivity))
        money (div_nonneg fp hp.le) (mul_nonneg (by positivity) (pow_nonneg (by linarith) _))
    _=2^(order+shelf+1+d)*x^(d+Spill.Raffle.pad (order+shelf+1)):=by
      dsimp only [h]
      rw [pow_add,pow_add,mul_pow]
      ring

end YM.Integration.WilsonOriginalCompactRafflePrice
