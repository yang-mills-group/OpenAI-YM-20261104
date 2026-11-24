import YM.Integration.WilsonOriginalCensusFiniteForest
import YM.Integration.WilsonOriginalCensusFaceSheet
import YM.Integration.WilsonReceivedDepositedOrbitalDatedGraph
import YM.Integration.WilsonNeutralTwoPrintPathCalendar
import YM.Integration.WilsonOriginalFoldedMarkedRightColumn
import YM.Integration.WilsonMarkedIndependentFoldedIntegral

/-! Read the entire normalized finite marked scalar at its actual physical direction. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusFinitePortrait
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
theorem original (simple:G.Simple)(M:family G h)(paid:Eu k M)(C:Cost)(J:Finset I)
    (d:ℕ)(v:Stationary.Link G (c)):
    read (coordinates G (c)) (flash (pPly t J (physical M C J))) d v=
      Complex.ofReal (diagonal (mass k J+d) (fun r z=>touch t J ((physical M C J) d r z))
        ((coordinates G (c)) v)):=by
  have cap:shellK (mass k J) (physical M C J):=(steaks (S) (F) (upper R N i)
    (prediction R N i per) R.metals.O (covered R N i per) M C
    (emera_far (V) simple R.alloy.B.ratio hi (fine R i per)).1 R.alloy.B.ratio paid J).1
  have shape:shellK (mass k J) (pPly t J (physical M C J)):=ply_shell (touch t J).toLinearMap cap
  have support:still ((pPly t J (physical M C J)) d) (mass k J+d+1):=fun r huge=>shape d r (by omega)
  unfold WilsonNeutralSignedPolynomialRate.read
  rw [Blue.flash,coeff_mk,Blue.visible support,map_sum]
  rfl

include hi in
theorem submitted (simple:G.Simple)(q:ℕ)(old:Outerm G h)(well:Wellness k old)
    {σ B:ℝ}(width:0<σ)(one:1≤B)(bill:CoverBill old q σ B)(y:I → Lattice.Cover)(cell:I → Site (P).L)
    (J:Finset I)(d:ℕ)(v:Stationary.Link G (c)):
    let M:=submit old k q (chartIn (P) y cell)
    read (coordinates G (c)) (flash (pPly t J (physical M (calendar) J))) d v=
      Complex.ofReal (diagonal (mass k J+d) (fun r z=>touch t J ((spent R k N i q (c) old y cell J) d r z))
        ((coordinates G (c)) v)):=by
  intro M
  have help:Wellness k (submit old k q):=(WilsonReceivedCompactVerseEntrance.original old well width one bill).2.1
  rw [original R N i per hi k t simple M (help.level' _) (calendar) J d v]
  rw [WilsonOriginalCensusFiniteForest.filed]

end YM.Integration.WilsonOriginalCensusFinitePortrait
end
