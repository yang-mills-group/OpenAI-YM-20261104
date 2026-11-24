import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerTolerance
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceNativeLowerGauge
open Function Filter Finset Set Lattice Wilson RG Source Cells GapsContact.Seams Trace.Terrace
open PhysicalNext.Repeat.Legato Extraction RG17 Spec Table Table.Pairing Climb Trace.Pilot PhysMS PhysMS.Frame
open Maxwell Maxwell.Wick XSpace XSpace.Normalize XSpace.Structure1
open MS MS.Land MS.Menus MS.Theater Local.Physical
open WilsonOriginalPublicRelativeGramFreePanel (named pointsAt incidence)
open WilsonPositionProgramPublicWickGram (reading nodes)
open WilsonPhysicalStationGradedLowerPanel (left right frame)
open WilsonMeasuredPublicEntranceNativeLowerMoment (free)
open WilsonMeasuredPublicEntranceNativeLowerLeft (ears coefficients representative)
open WilsonMeasuredPublicEntranceNativeLowerFrame (panel row pivot vote)
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    (B:Deck G)(e:ℕ)(a:Axis)
local notation "I" => Glyph B e
local notation "D" => Table.Field (Bel R.family.book)

open WilsonMeasuredPublicEntranceNativeLowerTolerance (Meter)
open WilsonMeasuredPublicEntranceNativeLowerPayoff (Earned)
open WilsonMeasuredPublicEntranceNativeLowerSignal (difference)
open WilsonPhysicalStationGradedLowerPanel (charge cross right left frame)
open WilsonPhysicalStationLowerReceiver (ear)
theorem transfer {d q Q:ℕ}(le:e≤d){U V:tower S}(same:U e=V e)(x:Points 2)
    (L:S.Field d→ₗ[ℂ]ℂ)(X:S.Field d)(tol:ℝ):
    Meter R F B e a le U x q Q L X tol ↔ Meter R F B e a le V x q Q L X tol:=by
  have matrix:WilsonPhysicalStationGradedLowerPanel.frame R U B e a x=WilsonPhysicalStationGradedLowerPanel.frame R V B e a x:=by
    funext i j
    simp only [WilsonPhysicalStationGradedLowerPanel.frame,WilsonPhysicalStationGradedLowerPanel.right,WilsonPhysicalStationGradedLowerPanel.left,same]
  have rows (T:ℝ)(r:ℕ)(A:S.Field e→ₗ[ℂ]ℂ):WilsonPhysicalStationGradedLowerPanel.cross R U B e a T r A=WilsonPhysicalStationGradedLowerPanel.cross R V B e a T r A:=by
    funext i
    simp only [WilsonPhysicalStationGradedLowerPanel.cross,WilsonPhysicalStationGradedLowerPanel.left,same]
  simp only [Meter,WilsonMeasuredPublicEntranceNativeLowerPayoff.Earned,WilsonPhysicalStationGradedLowerPanel.charge,matrix,rows,WilsonPhysicalStationGradedLowerPanel.right,same]
theorem filed {d q Q:ℕ}(le:e≤d)(U:ℝ→tower S)(r t c:ℝ)(V W:tower S)
    (low:U r e=V e)(high:U r d=V d)(fine:U (t*r) d=W d)
    (x z:Points 2)(v p:D d)(tol:ℝ)
    (paid:Meter R F B e a le V x q Q (ear R z (V d p)) (W d v-(c:ℂ) • V d v) tol):
    Meter R F B e a le (U r) x q Q (ear R z (U r d p)) (difference R U r t c v) tol:=by
  apply (transfer R F B e a le low _ _ _ _).mpr
  simpa only [difference,high,fine] using paid

end YM.Integration.WilsonMeasuredPublicEntranceNativeLowerGauge
end
