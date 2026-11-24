import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerHorizon
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceNativeLowerSame
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

theorem original (J:ℝ→tower S){d:ℕ}(v:D d)(r t:ℝ)(p:0<t)(same:t=1):
    PhysMS.Frame.cocycle d J r t p v=v:=by
  subst t
  have neutral (w:D d):Pert.Scale.gear R.family.labels d 1 w=w:=by
    let B:=Extra.FD.recorded R.family.labels d
    rw [←B.b.sum_repr w,map_sum]
    simp_rw [map_smul,Pert.Scale.rare]
    simp
  apply (J r d).injective
  simpa only [neutral,one_mul] using PhysMS.Frame.cocycle_value d J v 1 r p

end YM.Integration.WilsonMeasuredPublicEntranceNativeLowerSame
end
