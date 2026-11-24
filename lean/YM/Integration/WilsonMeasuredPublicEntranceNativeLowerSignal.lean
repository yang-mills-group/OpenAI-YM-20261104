import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerLimit

/-! The signed two-home difference after the common lower subtraction. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceNativeLowerSignal
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

def difference (U:ℝ→tower S)(r t:ℝ){d:ℕ}(c:ℝ)(v:D d):S.Field d:=
  U (t*r) d v-(c:ℂ) • U r d v

def velocity {d:ℕ}(s c:ℝ)(Z:Module.End ℂ (D d))(v:D d):D d:=
  Pert.Scale.gear R.family.labels d s (Z v)-(c:ℂ) • v

theorem incoming {U J:ℝ→tower S}(aligned:localCost trail U J){T:Type*}{l:Filter T}
    {r t c:T→ℝ}{s g:ℝ}(hr:Tendsto r l trail)(ht:Tendsto t l (𝓝 s))(pos:∀i,0<t i)
    (hc:Tendsto c l (𝓝 g)){d:ℕ}(Z:Module.End ℂ (D d))
    (target:∀w,Tendsto (fun i=>PhysMS.Frame.cocycle d J (r i) (t i) (pos i) w) l (𝓝 (Z w)))
    (v:D d):
    Tendsto (fun i=>(J (r i) d).symm (difference R U (r i) (t i) (c i) v)) l
      (𝓝 (velocity R s g Z v)):=by
  have raw:=WilsonMeasuredPublicEntranceNativeArrow.held aligned hr ht pos Z target (v:=fun _:T=>v) tendsto_const_nhds
  have travelled:=vote R aligned hr raw
  have here:=vote R aligned hr (v:=fun _:T=>v) tendsto_const_nhds
  have amount:Tendsto (fun i=>(c i:ℂ)) l (𝓝 (g:ℂ)):=Complex.continuous_ofReal.continuousAt.tendsto.comp hc
  simpa only [difference,velocity,map_sub,map_smul,LinearEquiv.apply_symm_apply] using
    travelled.sub (amount.smul here)

theorem original {U J:ℝ→tower S}(lead:Leading F J)(aligned:localCost trail U J){T:Type*}{l:Filter T}
    {r t c:T→ℝ}{s g:ℝ}(hr:Tendsto r l trail)(ht:Tendsto t l (𝓝 s))(pos:∀i,0<t i)
    (hc:Tendsto c l (𝓝 g)){d:ℕ}(le:e≤d)(Z:Module.End ℂ (D d))
    (target:∀w,Tendsto (fun i=>PhysMS.Frame.cocycle d J (r i) (t i) (pos i) w) l (𝓝 (Z w)))
    (v:D d){x:T→Points 2}{y:Points 2}(hx:Tendsto x l (𝓝 y))(hy:y∈conf 2)
    (rank:IsUnit (panel R B e a y).det){z:T→Points 2}{w:Points 2}(hz:Tendsto z l (𝓝 w))(hw:w∈conf 2)
    {k:ℕ}(peer:D k):
    let X i:=difference R U (r i) (t i) (c i) v
    let v₀:=velocity R s g Z v
    let low i:=WilsonMeasuredPublicEntranceNativeLowerLeft.representative R (U (r i)) B e a (r i • x i) (X i)
    Tendsto (fun i=>WilsonPhysicalStationLowerReceiver.ear R (r i • z i) (U (r i) k peer)
        (X i-F.sector.derivatives.rise le (low i))) l
      (𝓝 (free R w (v₀-(Maxwell.Free.scheme R.family.labels).rise le
        (WilsonMeasuredPublicEntranceNativeLowerLimit.lower R B e a y v₀)) peer)):=by
  intro X v₀ low
  have incomingX:Tendsto (fun i=>(J (r i) d).symm (X i)) l (𝓝 v₀):=incoming R aligned hr ht pos hc Z target v
  have old:=WilsonMeasuredPublicEntranceNativeLowerLimit.lifted R F B e a lead aligned hr hx hy rank le incomingX
  apply WilsonMeasuredPublicEntranceNativeLowerMoment.original R F lead hr hz hw
  · simpa only [map_sub] using incomingX.sub old
  · exact vote R aligned hr tendsto_const_nhds

end YM.Integration.WilsonMeasuredPublicEntranceNativeLowerSignal
end
