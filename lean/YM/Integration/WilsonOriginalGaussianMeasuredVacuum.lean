import YM.Integration.WilsonOriginalGaussianDatedVacuum

/-! On the original measured course, the complete unmarked group phase
has a polynomial field bound before the cutoff or the period is specified. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalGaussianMeasuredVacuum
open Function Filter Finset Lattice Laurent Bloch Wilson RG Precision Exterior Tree Matrix PowerSeries
open PhysicalNext.Repeat.Legato Comparison.RG02 FreeResolvent WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Winding WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank.Mosaic FVA1Physical.TwoReset
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Ker
open PhysicalNext PhysicalNext.Repeat ThroughLaunch Pane Next.Foundations
open WilsonVacuumPreResetTorusSeason WilsonVacuumPreResetTorusDeposit
open WilsonVacuumPreResetStationaryChange
open WilsonLimitConstruction.FundedCompanySelection Pressure Gauge WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Embroider
open Primitives.TwoWave.RealSlice
open AllOrder.Floe.Step.PlanV
open scoped BigOperators Classical Topology
variable {G:Gauge}

theorem original (R:Run G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)
    (rows:FundedMarkedCoverRows.prices v R.kit)(paths:FundedOriginalVacuumPaths.prices R.kit)(e:ℕ):
    ∀ᶠ m:ℕ in atTop,∀j≥m,∃C:ℝ,0≤C ∧ ∀N≥j,
      ∀(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)
      (π:ℕ→Layout G)(Γ:ℕ→Pace.Coin),PlanV.Path D R.alloy Q e N m π Γ→
        PlanV.Spec D Q R.alloy R.kit→∀t≤e+2,∀n:Side,∀x y:rule (Coarse G) n,
      |massJets R N j e (π j) t n x-massJets R N j e (π j) t n y|
        ≤ C * WilsonOriginalGaussianDatedVacuum.size x y^(e+4):=by
  obtain ⟨W,trained⟩:=WilsonVacuumPreResetMeasuredCoin.original R simple v rows paths e
  obtain ⟨b,buy⟩:=eventually_atTop.1 (WilsonOriginalGaussianAngularWallet.entries R simple v rows e (e+4))
  filter_upwards [trained,eventually_ge_atTop b] with m ready active
  intro j jm
  obtain ⟨B,nn,wallet⟩:=buy j (active.trans jm)
  refine ⟨2*(e+4:ℕ)*B,by positivity,?_⟩
  intro N jN D Q π Γ flying actual t ht n x y
  obtain ⟨Z,bill,_,authorized⟩:=ready N (jm.trans jN)
  obtain ⟨σ,_,_,issued⟩:=bill j jm jN
  have equality:=(authorized D Q π Γ flying actual).jets j jm jN t ht
  rw [equality]
  exact WilsonOriginalGaussianDatedVacuum.receipt R issued nn (wallet N jN) ht n x y

end YM.Integration.WilsonOriginalGaussianMeasuredVacuum
end
