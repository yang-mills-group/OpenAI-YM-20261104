import YM.Integration.WilsonMovingMentorRaffleCourse
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerPrecontactInvoice
open ConnectedActivityE6
open RG Pressure Lattice PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Transit AllOrder.Transit.WheelP
open QuadraticLocal QuadraticLocal.Earn Mentor MintClock Push.PriceCompiler Org

theorem original {G : Gauge} (R : Run G) {ψ : ℕ → ℕ}
    {r : PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel}
    (posted : Spill.Raffle.Warm G r R.alloy.delay ψ)
    {lo m N per seed i q v k : ℕ} {π : ℕ → Layout G} {Γ : ℕ → Pace.Coin}
    {H : (t : ℕ) → RG.Rep G (R.alloy.B.a.S.side t per)}
    (history : Concourse R.alloy R.kit R.T π Γ lo N per seed H) (start : lo ≤ m) (hi : i≤R.alloy.B.a.clock.J m) (hq : q≤R.alloy.B.a.clock.J m)
    (hv : v≤R.alloy.B.a.clock.J m) (hk : k≤R.alloy.B.a.clock.J m) (hm : m ≤ N) :
    let y := R.alloy.B.a.clock.J m
    let x := R.alloy.B.a.clock.hatBeta m
    let σ := Poetry.Agenda.seed r ψ i y
    let P := H m
    let L : Side := 1
    let cash:=Invoice.price P.p (Page.temperature G L x) (q+v+1) k (P.p.supportExponent+1) (σ/4) G
    0 ≤ cash ∧ cash ≤ x^(Spill.Raffle.pad (q+v+1)):=by
  let y:=R.alloy.B.a.clock.J m
  let x:=R.alloy.B.a.clock.hatBeta m
  let σ:=Poetry.Agenda.seed r ψ i y
  let B:BudgetPoint:=(H m).p
  have enrollment:=history.1.walk m start hm
  have tune:Spes.Market.tuning (R.metals.p.profile y) B x:=by
    change Spes.Market.tuning (R.metals.p.profile (R.alloy.B.a.clock.J m)) (H m).p
      (R.alloy.B.a.clock.hatBeta m)
    rw [enrollment.truep.point,←params_eq R.alloy.B.valid m]
    exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  obtain ⟨window,wage⟩:=WilsonMovingMentorRaffleCourse.measured R posted history start hi hq hv hk hm
  let F:=Invoice.price B (Page.temperature G (1:Side) x) (q+v+1) k (B.supportExponent+1) (σ/4) G
  have pass: F = Spill.Raffle.fundsOne G (R.metals.p.profile y) σ q v k x:=
    Spill.Raffle.regular G (R.metals.p.profile y) σ q v k B x tune.2.2 tune.2.1
  have fp:0≤F:=(Invoice.positive B _ _ window.2.2.1 k window.2.2.2.2.2.2.1 G).le
  have xp:0<x:=zero_lt_one.trans ((R.alloy.B.a).fits.delayed m)
  have A:1≤Willow.area B.B:=Willow.area_ge_one _
  have slack:Willow.haloSlack B.B≤1:=by
    unfold Willow.haloSlack
    exact (div_le_one (by linarith only [A])).mpr (by linarith only [A])
  refine ⟨fp,?_⟩
  calc
    F ≤ (Spill.allOver B)^(q+v+1)*F:=le_mul_of_one_le_left fp (one_le_pow₀ (Spill.allOver_ge _))
    _ ≤ x^(Spill.Raffle.pad (q+v+1))*Willow.haloSlack B.B:=by rw [pass];exact wage
    _ ≤ x^(Spill.Raffle.pad (q+v+1)):=mul_le_of_le_one_right (pow_nonneg xp.le _) slack

end YM.Integration.WilsonThermometerPrecontactInvoice
end
