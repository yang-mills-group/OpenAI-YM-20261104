import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerColumn
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceNativeLowerTicket
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
open WilsonMeasuredPublicEntranceNativeLowerSignal (difference)
open WilsonMeasuredPublicEntranceNativeLowerTolerance (Meter)
open WilsonMeasuredPublicEntranceBranchGap (watches)
variable {A:Type*}

def Ticket (l:Filter A)(U:ℝ→tower S)(r t:A→ℝ)(s:ℝ)(d:ℕ)(v:D d)(q Q:ℕ)(price:ℝ):Prop:=
  ∃(B:Deck G)(e:ℕ)(a:Axis)(le:e≤d), e<d ∧ ∃c:A→ℝ,Tendsto c l (𝓝 (price*s^d)) ∧
    ∃(x:A→Points 2)(y:Points 2),Tendsto x l (𝓝 y) ∧ y∈conf 2 ∧ IsUnit (panel R B e a y).det ∧
    ∃(z:A→Points 2)(left right:E4),left≠right ∧ Tendsto z l (𝓝 (couple left right)) ∧ couple left right∈conf 2 ∧
      ∀j:(R.family.labels.level d).Index,((R.family.labels.level d).grades j).2=Q→
      ∀tol:ℝ,0<tol→∀ᶠi in l,Meter R F B e a le (U (r i)) (r i • x i) q Q
        (ear R (r i • z i) (U (r i) d ((Bel R.family.book).project d (Pi.single j 1))))
        (difference R U (r i) (t i) (c i) v) tol

theorem entered {l:Filter A}[NeBot l]{U J:ℝ→tower S}(lead:Leading F J)(aligned:localCost trail U J)
    {r t:A→ℝ}{s:ℝ}(hr:Tendsto r l trail)(ht:Tendsto t l (𝓝 s))(hs:0<s)(pos:∀i,0<t i)
    {d:ℕ}(Z:Module.End ℂ (D d))(heard:∀v,Tendsto (fun i=>PhysMS.Frame.cocycle d J (r i) (t i) (pos i) v) l (𝓝 (Z v)))
    (P:RStage R.family.labels d)(out src:Fin (P.m+1))(top:(P.w out).1=d)(up:(P.w src).2≤(P.w out).2)
    {price:ℝ}(ticket:Ticket R F l U r t s d (P.b src) (P.w src).2 (P.w out).2 price):
    P.b.coord out (Z (P.b src)-(price:ℂ) • P.b src)=0:=by
  obtain ⟨book,e,axis,le,below,c,hc,x,y,hx,hy,rank,z,left,right,apart,hz,clear,paid⟩:=ticket
  have eq:price*s^d/s^(P.w out).1=price:=by rw [top];field_simp [ne_of_gt hs]
  have sale:=WilsonMeasuredPublicEntranceNativeLowerColumn.original R F book e axis lead aligned hr ht hs pos hc le Z heard
    P out src (by simpa only [top] using below) up hx hy rank left right apart hz clear paid
  rwa [eq] at sale

end YM.Integration.WilsonMeasuredPublicEntranceNativeLowerTicket
end
