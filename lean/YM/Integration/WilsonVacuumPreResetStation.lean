import YM.Integration.WilsonLimitConstruction.FundedCensusVacuum

/-! One original pre-reset listing and its absolute hard income at the
measured temperature, before making any regular model substitution. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetStation
open Function Filter Set Lattice RG Pressure Wilson Precision Push Shoot
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Extra.Iteration
open PriceCompiler Org Input Supply Pressure.Testing Time Source Push.SectorMeasure
open PhysicalNext PhysicalNext.Repeat Roost Opera Match Legato
open ConnectedActivityE6.Coat RG01Estimate RG01Estimate.CensusStep
open WilsonLimitConstruction.FundedCensusVacuum
open scoped Classical Topology
variable {G:Gauge}(R:Run G)
local notation "T" => R.alloy.B.a

theorem hard {N per m:ℕ}(S:Station R N per m):
    hardCost R.kit m≤(1/8:ℝ)*Time.forecastK T m R.kit.scout (R.family.path.β N per (m+1)):=by
  let j:=(T).clock.J (m+1)
  let i:=(T).clock.J m
  let β:=R.family.path.β N per (m+1)
  let y:=betaF G ((T).clock.hatBeta m) (R.rolls.L j)
  have eq:(T).clock.hatBeta (m+1)=y:=PriceCompiler.beta_eq R.alloy.B.valid m
  have h:=R.kit.pledging.conducts.income.earns j i (step_paid T m) ((T).clock.hatBeta m) (R.alloy.B.valid.pays m) β
    (show inBand y β from eq ▸ trial_in S.band)
  change hardCost R.kit m≤(1/8:ℝ)*(R.kit.scout j i).pair.strong y β at h
  rw [←eq] at h
  exact h

theorem actual (simple:G.Simple)(r:ℕ):
    ∀ᶠm:ℕ in atTop,∀N per,∀hm:m<N,let S:=station R N per m hm
    let Y:=R.family.path.rep N per (m+1)
    let V:=R.family.path.rep N per m
    let X:=ledger R.kit S.guide
    let d:=vacuum R.kit S.guide S.guide S.identity
    let a₀:=kept R.kit S.guide S.guide S.identity r
    let e₀:=discarded R.kit S.guide S.guide S.identity r
    let ε₀:=Opera.earlyFee (p:=R.kit.expense) R.alloy.B N m Y.beta
    let μ₀:=(2*gStep Y.beta)^(r+1)
    let β:=Y.beta
    let w:=Time.forecastK T m R.kit.scout β
    Local X ((T).budget m) d ε₀ w ∧ Local X ((T).budget m) a₀ ε₀ w ∧
    Local X ((T).budget m) e₀ μ₀ w ∧ e₀.logRead=d.logRead-a₀.logRead ∧
    a₀.hardRead=d.hardRead ∧ e₀.hardRead=d.hardRead ∧
    ∀ O : Tree.Forest ((T).clock.op m per).ratio,
      V.eval = earlyValue X (R.alloy.B.kin.path N m) ((T).params m).clip ((T).budget m) d β
        (Song.weighty S.guide Chi.canonical O) (R.alloy.B.kin.alpha N m):=by
  filter_upwards [paid R simple r] with m found
  intro N per hm S Y V X d a₀ e₀ ε₀ μ₀ β w
  have h:=found N per hm
  have hw:0≤w:=mul_nonneg (by exact le_trans zero_le_one (le_max_left ..)) (Real.exp_nonneg _)
  have access:hardCost R.kit m≤(1/8:ℝ)*w:=hard R S
  have fits:hardCost R.kit m≤w:=by linarith only [hw,access]
  refine ⟨VacuumListing.relax ((T).budget m) h.fullSize le_rfl fits,
    VacuumListing.relax ((T).budget m) h.low le_rfl fits,
    VacuumListing.relax ((T).budget m) h.high le_rfl fits,?_,rfl,rfl,?_⟩
  · have row:d.logRead=a₀.logRead+e₀.logRead:=h.recorded
    rw [row,add_sub_cancel_left]
  · intro O;funext W
    exact (congrFun (R.makes.wilson.steps N per m hm).1 W).trans (h.integral O W)

end YM.Integration.WilsonVacuumPreResetStation
