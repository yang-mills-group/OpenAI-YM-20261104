import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerEntry
import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerPayoff
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceNativeLowerVote
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

open WilsonMeasuredPublicEntranceRecordedPortfolio (cell)
open WilsonMeasuredPublicEntranceNativeLowerMoment (free ports)
open WilsonOriginalBlissMixedGram (grades)
open Extra.FD
theorem raw (R:Run G){d:ℕ}(x y:E4)(z:(Bel R.family.book).Field d)(a:(R.family.labels.level d).Index):
    free R (couple x y) z ((Bel R.family.book).project d (Pi.single a 1))=cell x y z a:=by
  let T:=Bel R.family.book
  let v:T.Field d:=T.project d (Pi.single a 1)
  change T.useAt T (couple x y) (fun i=>⟨grades d d i,ports R z v i⟩)=
    T.useAt T (couple x y) (fun i=>⟨d,(![z,v]:Fin 2→T.Field d) i⟩)
  congr 1
  funext i
  fin_cases i <;> rfl

end YM.Integration.WilsonMeasuredPublicEntranceNativeLowerVote
end
