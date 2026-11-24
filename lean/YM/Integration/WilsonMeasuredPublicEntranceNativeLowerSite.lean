import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerTicket
import YM.Integration.WilsonPhysicalStationMixedWickSolvent
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceNativeLowerSite
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

open Extra.FD
open WilsonPhysicalStationLowerReceiver (ear)
open WilsonPhysicalStationMixedWickSolvent (Room)
open WilsonMeasuredPublicEntranceNativeLowerSignal (difference)
open WilsonMeasuredPublicEntranceNativeLowerTolerance (Meter)
open WilsonMeasuredPublicEntranceNativeLowerTicket (Ticket)
theorem original {A:Type*}{l:Filter A}{U:ℝ→tower S}{r t c:A→ℝ}{s p:ℝ}{d q Q:ℕ}(v:D d)
    (room:Room R (S:=S) B e a)(le:e≤d)(low:e<d)(hc:Tendsto c l (𝓝 (p*s^d)))
    {x:A→Points 2}(hx:Tendsto x l (𝓝 room.ξ))
    (issuer:∀j:(R.family.labels.level d).Index,((R.family.labels.level d).grades j).2=Q→
      ∀tol:ℝ,0<tol→∀ᶠi in l,Meter R F B e a le (U (r i)) (r i • x i) q Q
        (ear R (r i • x i) (U (r i) d ((Bel R.family.book).project d (Pi.single j 1))))
        (difference R U (r i) (t i) (c i) v) tol):
    Ticket R F l U r t s d v q Q p:=by
  have same:couple (room.ξ 0) (room.ξ 1)=room.ξ:=by
    ext i
    fin_cases i <;> rfl
  have clear:=generic_conf 2 room.generic
  have apart:room.ξ 0≠room.ξ 1:=fun h=>Fin.zero_ne_one (clear h)
  refine ⟨B,e,a,le,low,c,hc,x,room.ξ,hx,clear,room.rank _ (mem_of_mem_nhds room.neighborhood),
    x,room.ξ 0,room.ξ 1,apart,?_,?_,issuer⟩
  · simpa only [same] using hx
  · simpa only [same] using clear

end YM.Integration.WilsonMeasuredPublicEntranceNativeLowerSite
end
