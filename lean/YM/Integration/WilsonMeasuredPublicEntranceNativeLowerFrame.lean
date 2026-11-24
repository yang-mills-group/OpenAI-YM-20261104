import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerMoment

/-! The ordinary lower Gram and the original physical incoming row on the
same previously appointed coarse chart. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceNativeLowerFrame
open Function Filter Finset Set Lattice Wilson RG Source Cells GapsContact.Seams Trace.Terrace
open PhysicalNext.Repeat.Legato Extraction RG17 Spec Table Table.Pairing Climb Trace.Pilot PhysMS PhysMS.Frame
open Maxwell Maxwell.Wick XSpace XSpace.Normalize XSpace.Structure1
open MS MS.Land MS.Menus MS.Theater Local.Physical
open WilsonOriginalPublicRelativeGramFreePanel (named pointsAt incidence)
open WilsonPositionProgramPublicWickGram (reading nodes)
open WilsonPhysicalStationGradedLowerPanel (left right frame)
open WilsonMeasuredPublicEntranceNativeLowerMoment (free)
open WilsonMeasuredPublicEntranceNativeLowerLeft (ears)
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    (B:Deck G)(e:ℕ)(a:Axis)
local notation "I" => Glyph B e
local notation "D" => Table.Field (Bel R.family.book)

def pivot (i:I):D e:=(Bel R.family.book).adj (Maxwell.Free.spin_free R.family.labels) e a (named R B e i)

def panel (x:Points 2):Matrix I I ℂ:=fun i j=>free R x (pivot R B e a i) (named R B e j)
def row {h:ℕ}(x:Points 2)(v:D h):I→ℂ:=fun j=>free R x v (named R B e j)

theorem reflected :panel R B e a (pointsAt a)=reading a (nodes a) (id:I→I):=by
  funext i j
  exact incidence R B e a i j

theorem funded :IsUnit (panel R B e a (pointsAt a)).det:=by
  obtain ⟨k,δ,_,dp,positive⟩:=WilsonOriginalPublicRelativeGramReference.original a (id:I→I) injective_id
  apply (positive _ ?_).1
  simpa [reflected] using dp.le

theorem vote {U J:ℝ→tower S}(aligned:localCost trail U J){T:Type*}{l:Filter T}
    {r:T→ℝ}(hr:Tendsto r l trail){d:ℕ}{v:T→D d}{z:D d}(hv:Tendsto v l (𝓝 z)):
    Tendsto (fun t=>(J (r t) d).symm (U (r t) d (v t))) l (𝓝 z):=
  Dash.arcing ((WilsonMeasuredPublicEntranceNativeChange.directions aligned d).2.comp hr) hv

theorem original {U J:ℝ→tower S}(lead:Leading F J)(aligned:localCost trail U J){T:Type*}{l:Filter T}
    {r:T→ℝ}(hr:Tendsto r l trail){x:T→Points 2}{y:Points 2}(hx:Tendsto x l (𝓝 y))(hy:y∈conf 2)
    {h:ℕ}{X:T→S.Field h}{v:D h}(hv:Tendsto (fun t=>(J (r t) h).symm (X t)) l (𝓝 v)):
    Tendsto (fun t=>frame R (U (r t)) B e a (r t • x t)) l (𝓝 (panel R B e a y)) ∧
    Tendsto (fun t=>ears R (U (r t)) B e (r t • x t) (X t)) l (𝓝 (row R B e y v)):=by
  have piv (i:I):Tendsto (fun t=>(J (r t) e).symm (left R (U (r t)) B e a i)) l (𝓝 (pivot R B e a i)):=
    vote R aligned hr tendsto_const_nhds
  have peer (j:I):Tendsto (fun t=>(J (r t) e).symm (right R (U (r t)) B e j)) l (𝓝 (named R B e j)):=
    vote R aligned hr tendsto_const_nhds
  constructor
  · exact tendsto_pi_nhds.mpr fun i=>tendsto_pi_nhds.mpr fun j=>
      WilsonMeasuredPublicEntranceNativeLowerMoment.original R F lead hr hx hy (piv i) (peer j)
  · exact tendsto_pi_nhds.mpr fun j=>WilsonMeasuredPublicEntranceNativeLowerMoment.original R F lead hr hx hy hv (peer j)

end YM.Integration.WilsonMeasuredPublicEntranceNativeLowerFrame
end
