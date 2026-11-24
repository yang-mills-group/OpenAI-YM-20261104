import YM.Integration.WilsonPhysicalStationThermalPortfolio

/-! Apply the original reflected test to the entire nominated right
field, with the original cutoff-dependent coefficients on both sides. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationThermalNominated
open Function Filter Finset Lattice RG Wilson Cells Labels Source Next.Rank Next.Rank.East Next.Rank.Price
open MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East
open PhysicalNext.Repeat.Legato Trace.Physical.GermGraph Maxwell.Free
open Further.CorrectedLift (ladder)
open WilsonPhysicalPositionReflectedReturn (ports)
open WilsonPhysicalStationThermalRanks (probe)
open WilsonPhysicalStationThermalPair (cell raw)
open scoped BigOperators Classical
open WilsonPhysicalStationThermalPortfolio (residual scalar)
variable {G:Gauge}
variable (R:Run G){f:Extraction.Order}{H:(Bel R.family.book).Hierarchy}
    {D:ℕ}(V:Vane R.family D)(rank:Fin (D+1)){N p:ℕ}
    (checked:V.checked f H D)(top:V.k<N)
    (j:ℕ)(o:Fin 2 → Cover)(y:Points 2)(x:R.family.label rank)


theorem original (w:(Cells.standard R.family).Field rank)(s:Signed)(e:Fin 2):
    residual R V rank (p:=p) checked top j o y x (ports (C:=R.family) w s e)=
      ∑i,scalar e (ladder R.family rank w i) *
         residual R V rank (p:=p) checked top j o y x (probe R.family i s e):=by
  rw [WilsonPhysicalStationThermalPortfolio.turned R.family w s e]
  exact WilsonPhysicalStationThermalPortfolio.original R V rank checked top j o y x _ _

end YM.Integration.WilsonPhysicalStationThermalNominated
end
