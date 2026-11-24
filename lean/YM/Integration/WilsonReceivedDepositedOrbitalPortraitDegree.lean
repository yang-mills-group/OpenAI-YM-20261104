import YM.Integration.WilsonReceivedDepositedOrbitalFieldDegree
import YM.Integration.WilsonOriginalCensusFinitePortrait
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedDepositedOrbitalPortraitDegree
open Function Finset Lattice Laurent Wilson RG RG.Supply Precision Tree Exterior Bloch Matrix PowerSeries
open PhysicalNext.Repeat.Legato Comparison.RG02 FreeResolvent WilsonCoeffUV
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue WilsonCoeffUV.Mer
open WilsonCoeffUV.Winding WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open FormalBulk08 Flat Reef Orb Series Jets Shore Lava Wine Gorge Lotus Mesa
open Next.Free AnalyticNext.QuarticMatch.Sheets Stationary
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedGeometric
open scoped BigOperators Matrix Classical
variable {G:Gauge}
open WilsonNeutralTwoPrintPathCalendar (spent)
open WilsonVacuumPreResetOriginalOutput (covered)
open WilsonReceivedCompactVerseEntrance (submit)
open WilsonCoeffUV.Wheel Mark WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Carp
variable {I:Type}[Fintype I][DecidableEq I]{h:I → ℕ}

open WilsonNeutralTwoPrintPathJet (diagonal)
open WilsonOriginalRawQReversion (coordinates)
open WilsonNeutralSignedPolynomialRate (read)
open WilsonReceivedCanonicalSocketMist WilsonCoeffUV.Embroider
open WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Wheel.Flooring
open WilsonReceivedCompactVerseEntrance (CoverBill)
variable (R:Run G)(N i per:ℕ)(hi:i<N)(k:I→ℕ)(t:Case h)
local notation "V" => R.family.path.levels
local notation "S" => WilsonVacuumPreResetStationaryChange.step R i per
local notation "P" => loose (V) i
local notation "c" => coarse R i per
local notation "F" => repeatF (S)
local notation "calendar" => ratioHigh (V) R.metals.O N i
local notation "physical" M:max C:max J:max => mist (S) (F) (upper R N i) (prediction R N i per) R.metals.O (covered R N i per) M C k J

include hi in
omit [Fintype I] in
theorem original (simple:G.Simple)(M:family G h)(paid:Eu k M)(C:Cost)(J:Finset I)(d:ℕ):
    Comparison.RG02.Valence.Level ((mass k J+d:ℕ):ℤ)
      (fun v:Stationary.Link G (c)=>read (coordinates G (c)) (flash (pPly t J (physical M C J))) d v):=by
  let L:=coordinates G (c)
  let held (r:ℕ)(z:Fin r→Woods G (c)):=touch t J ((physical M C J) d r z)
  have equality:(fun v=>read L (flash (pPly t J (physical M C J))) d v)=
      fun v=>(diagonal (mass k J+d) held (L v):ℂ):=
    funext (WilsonOriginalCensusFinitePortrait.original R N i per hi k t simple M paid C J d)
  exact equality.symm ▸ WilsonReceivedDepositedOrbitalFieldDegree.original L (mass k J+d) held

end YM.Integration.WilsonReceivedDepositedOrbitalPortraitDegree
end
