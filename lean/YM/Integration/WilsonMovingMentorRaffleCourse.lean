import YM.Integration.WilsonMovingMentorRafflePrice
import YM.Integration.WilsonMovingMentorTerrace

/-! The hard allowance at every previously enrolled representative of the same history. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingMentorRaffleCourse
open ConnectedActivityE6
open RG Pressure Lattice PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Transit AllOrder.Transit.WheelP
open QuadraticLocal QuadraticLocal.Earn Mentor MintClock Push.PriceCompiler Org

theorem measured {G : Gauge} (R : Run G) {ψ : ℕ → ℕ}
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
    Invoice.Supports P.p (Page.temperature G L x) (P.p.supportExponent+1) (Coat.gStep P.beta) σ (σ/4) ∧
      (Spill.allOver P.p)^(q+v+1) * Spill.Raffle.fundsOne G (R.metals.p.profile y) σ q v k x ≤
        x^(Spill.Raffle.pad (q+v+1)) * Willow.haloSlack P.p.B := by
  have entry := history.1.walk m start hm
  have temp : (H m).beta=(R.family.path.rep N per m).beta := entry.beta
  have budget : (H m).p=(R.family.path.rep N per m).p :=
    entry.truep.point.trans (R.makes.wilson.represents N per m hm).vac.symm
  dsimp only
  rw [temp,budget]
  exact WilsonMovingMentorRafflePrice.measured R posted hi hq hv hk hm per

theorem repaid {G : Gauge} (R : Run G) {ψ : ℕ → ℕ}
    {r : PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel}
    (posted : Spill.Raffle.Warm G r R.alloy.delay ψ)
    {lo m N per seed i q v k : ℕ} {π : ℕ → Layout G} {Γ : ℕ → Pace.Coin}
    {H : (t : ℕ) → RG.Rep G (R.alloy.B.a.S.side t per)}
    (history : Concourse R.alloy R.kit R.T π Γ lo N per seed H) (start : lo ≤ m) (hi : i≤R.alloy.B.a.clock.J m) (hq : q≤R.alloy.B.a.clock.J m)
    (hv : v≤R.alloy.B.a.clock.J m) (hk : k≤R.alloy.B.a.clock.J m) (hm : m ≤ N) (p : ℕ) :
    let y := R.alloy.B.a.clock.J m
    let x := R.alloy.B.a.clock.hatBeta m
    let σ := Poetry.Agenda.seed r ψ i y
    let P := H m
    let a := Spill.Raffle.pad (q+v+1)
    let g := Coat.gStep P.beta
    g^(p+2*a)*((Spill.allOver P.p)^(q+v+1)*Spill.Raffle.fundsOne G (R.metals.p.profile y) σ q v k x) ≤
      g^p*2^a*Willow.haloSlack P.p.B := by
  have entry := history.1.walk m start hm
  have temp : (H m).beta=(R.family.path.rep N per m).beta := entry.beta
  have budget : (H m).p=(R.family.path.rep N per m).p :=
    entry.truep.point.trans (R.makes.wilson.represents N per m hm).vac.symm
  dsimp only
  rw [temp,budget]
  exact WilsonMovingMentorRafflePrice.repaid R posted hi hq hv hk hm per p

end YM.Integration.WilsonMovingMentorRaffleCourse
end
