import YM.Integration.WilsonLimitConstruction.FundedCoverKineticMeasurement
import YM.Integration.WilsonLimitConstruction.FundedSignedPurchase
import YM.Integration.PhysicalWilsonSignedCoefficient

/-! An exact signed finite output has zero discrepancy against its own Plan.
A separately prescribed cover continues to carry its own cutoff invoice. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedExactKineticContact
open Lattice Wilson RG Precision Exterior Marker
open PhysicalNext.Repeat.Legato IterationFour IterationFour.Vacuum
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric Comparison.RG02 Comparison.RG02.Assembly
open PhysicalWilsonActionConvention FundedCoverKineticMeasurement

variable {G : Gauge} (T : Run G)
    {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {J : Request V} {A : NumericSchedule T.family J} {d : LocalFormal.Datum T.family R}
    {caps : Handoff.OutputCapacities} {Y : Bulk.Chain T.family.path} {K : NumericPrices A}
    {F : AnalyticInput J A d} (M : SignedAnalyticOutput caps Y K F)

theorem zero (x : TestSpace J.tests) (e : ℕ) (he : e≤J.order-2)
    (B : fieldDir G (T.family.side d.level d.period) 1) :
    difference T Y F (FundedPhysicalCatalogue.ofSigned M) x e B=0 := by
  have here := FundedCoverKineticMeasurement.position T Y F (FundedPhysicalCatalogue.ofSigned M) x e he B
  have exactFinite := PhysicalWilsonSignedCoefficient.green T M x e he B
  have h := here.symm.trans exactFinite
  let p := FundedCoefficientPrior.centered T M.plan d.level e B
  have negGround :
      Symmetry.Orbit.ground (d.kernel Y) (RG08.Line.green (T.family.path.levels.clock.op d.level d.period))
        d.tag (F.colors x) J.order (e+2) 0 -
      Symmetry.Orbit.ground (d.kernel Y) (RG08.Line.green (T.family.path.levels.clock.op d.level d.period))
        d.tag (F.colors x) J.order (e+2) B = -ground T Y F x e B := by
    unfold ground
    abel
  rw [negGround] at h
  change (-ground T Y F x e B-p)-difference T Y F (FundedPhysicalCatalogue.ofSigned M) x e B=
    -ground T Y F x e B-p at h
  exact sub_eq_self.mp h

theorem tested (hG : G.Simple) (x : TestSpace J.tests) :
    Tested T Y F (FundedPhysicalCatalogue.ofSigned M) hG x := by
  intro e he
  rw [zero T M x e he,norm_zero]
  exact zero_le_one

end YM.Integration.WilsonLimitConstruction.FundedExactKineticContact
end
