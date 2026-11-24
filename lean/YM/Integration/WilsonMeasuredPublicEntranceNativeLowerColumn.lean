import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerTolerance
import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerVote
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceNativeLowerColumn
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
open WilsonMeasuredPublicEntranceNativeLowerSignal (difference velocity)
open WilsonPhysicalStationLowerReceiver (ear)
open Extra.FD

theorem original {U J:ℝ→tower S}(lead:Leading F J)(aligned:localCost trail U J){A:Type*}{l:Filter A}[NeBot l]
    {r t c:A→ℝ}{s g:ℝ}(hr:Tendsto r l trail)(ht:Tendsto t l (𝓝 s))(hp:0<s)(pos:∀i,0<t i)
    (hc:Tendsto c l (𝓝 g)){d:ℕ}(le:e≤d)(Z:Module.End ℂ (D d))
    (target:∀v,Tendsto (fun i=>PhysMS.Frame.cocycle d J (r i) (t i) (pos i) v) l (𝓝 (Z v)))
    (P:RStage R.family.labels d)(out src:Fin (P.m+1))(above:e<(P.w out).1)(up:(P.w src).2≤(P.w out).2)
    {x:A→Points 2}{y:Points 2}(hx:Tendsto x l (𝓝 y))(hy:y∈conf 2)(rank:IsUnit (panel R B e a y).det)
    {z:A→Points 2}(left right:E4)(apart:left≠right)(hz:Tendsto z l (𝓝 (couple left right)))(hw:couple left right∈conf 2)
    (actual:∀j:(R.family.labels.level d).Index,((R.family.labels.level d).grades j).2=(P.w out).2→
      ∀tol:ℝ,0<tol→∀ᶠi in l,Meter R F B e a le (U (r i)) (r i • x i) (P.w src).2 (P.w out).2
        (ear R (r i • z i) (U (r i) d ((Bel R.family.book).project d (Pi.single j 1))))
        (difference R U (r i) (t i) (c i) (P.b src)) tol):
    P.b.coord out (Z (P.b src)-((g/s^(P.w out).1:ℝ):ℂ) • P.b src)=0:=by
  let v:=velocity R s g Z (P.b src)
  let old:=WilsonMeasuredPublicEntranceNativeLowerLimit.lower R B e a y v
  apply WilsonMeasuredPublicEntranceNativeLowerEntry.original le P left right apart out src above s g hp Z old
  intro j hj
  rw [←WilsonMeasuredPublicEntranceNativeLowerVote.raw R]
  exact WilsonMeasuredPublicEntranceNativeLowerTolerance.original R F B e a lead aligned hr ht pos hc le Z target (P.b src)
    hx hy rank hz hw ((Bel R.family.book).project d (Pi.single j 1)) (P.w src).2 (P.w out).2 up (actual j hj)

end YM.Integration.WilsonMeasuredPublicEntranceNativeLowerColumn
end
