import YM.QuadraticLocal.Class.Raffle
import YM.Integration.WilsonMovingMentorHardTemperature
import YM.Integration.WilsonMovingMentorTravelAtDate

/-! The authenticated hard allowance of the represented Wilson input at its own date. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingMentorRafflePrice
open ConnectedActivityE6 RG Pressure Lattice PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder AllOrder.Floe.Step QuadraticLocal QuadraticLocal.Earn Mentor MintClock Push.PriceCompiler Org

theorem measured {G : Gauge} (R : Run G) {ψ : ℕ → ℕ}
    {r : PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel}
    (posted : Spill.Raffle.Warm G r R.alloy.delay ψ)
    {m N i q v k : ℕ} (hi : i≤R.alloy.B.a.clock.J m) (hq : q≤R.alloy.B.a.clock.J m)
    (hv : v≤R.alloy.B.a.clock.J m) (hk : k≤R.alloy.B.a.clock.J m) (hm : m≤N) (per : ℕ) :
    let y := R.alloy.B.a.clock.J m
    let x := R.alloy.B.a.clock.hatBeta m
    let σ := Poetry.Agenda.seed r ψ i y
    let P := R.family.path.rep N per m
    let L : Side := 1
    Invoice.Supports P.p (Page.temperature G L x) (P.p.supportExponent+1) (Coat.gStep P.beta) σ (σ/4) ∧
      (Spill.allOver P.p)^(q+v+1) * Spill.Raffle.fundsOne G (R.metals.p.profile y) σ q v k x ≤
        x^(Spill.Raffle.pad (q+v+1)) * Willow.haloSlack P.p.B := by
  have paid := posted _ _ (step_paid R.alloy.B.a m) _ (R.alloy.B.valid.pays m) i hi q hq v hv k hk
  have owner := R.makes.wilson.represents N per m hm
  have tuned : Spes.Market.tuning (R.metals.p.profile (R.alloy.B.a.clock.J m))
      (R.family.path.rep N per m).p (R.alloy.B.a.clock.hatBeta m) := by
    rw [show (R.family.path.rep N per m).p = R.alloy.B.a.budget m from owner.vac]
    rw [← params_eq R.alloy.B.valid m]
    exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  apply paid.allowance _ tuned
  obtain ⟨lo,up⟩ := owner.band
  change R.alloy.B.a.clock.hatBeta m/2 ≤ (R.family.path.rep N per m).beta at lo
  change (R.family.path.rep N per m).beta ≤ 2*R.alloy.B.a.clock.hatBeta m at up
  change _/4 ≤ _ ∧ _ ≤ 4*_
  constructor <;> linarith only [lo,up]

theorem repaid {G : Gauge} (R : Run G) {ψ : ℕ → ℕ}
    {r : PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel}
    (posted : Spill.Raffle.Warm G r R.alloy.delay ψ)
    {m N i q v k : ℕ} (hi : i≤R.alloy.B.a.clock.J m) (hq : q≤R.alloy.B.a.clock.J m)
    (hv : v≤R.alloy.B.a.clock.J m) (hk : k≤R.alloy.B.a.clock.J m) (hm : m≤N) (per p : ℕ) :
    let y := R.alloy.B.a.clock.J m
    let x := R.alloy.B.a.clock.hatBeta m
    let σ := Poetry.Agenda.seed r ψ i y
    let P := R.family.path.rep N per m
    let a := Spill.Raffle.pad (q+v+1)
    let g := Coat.gStep P.beta
    g^(p+2*a)*((Spill.allOver P.p)^(q+v+1)*Spill.Raffle.fundsOne G (R.metals.p.profile y) σ q v k x) ≤
      g^p*2^a*Willow.haloSlack P.p.B := by
  let P := R.family.path.rep N per m
  let g := Coat.gStep P.beta
  let a := Spill.Raffle.pad (q+v+1)
  have priced := (measured R posted hi hq hv hk hm per).2
  have gp : 0≤g := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have slack : 0 ≤ Willow.haloSlack P.p.B := by
    unfold Willow.haloSlack Willow.area
    positivity
  calc
    _ ≤ g^(p+2*a)*((R.alloy.B.a.clock.hatBeta m)^a*Willow.haloSlack P.p.B) :=
      mul_le_mul_of_nonneg_left priced (pow_nonneg gp _)
    _ = (g^(p+2*a)*(R.alloy.B.a.clock.hatBeta m)^a)*Willow.haloSlack P.p.B := (mul_assoc ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (WilsonMovingMentorHardTemperature.measured R hm per a p) slack

end YM.Integration.WilsonMovingMentorRafflePrice
end
