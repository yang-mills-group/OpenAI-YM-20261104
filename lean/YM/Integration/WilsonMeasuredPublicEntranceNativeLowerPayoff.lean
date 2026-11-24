import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerSignal
import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerBill

/-! The signed two-home difference after the common lower subtraction. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceNativeLowerPayoff
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

open WilsonPhysicalStationLowerReceiver (ear)
open WilsonPhysicalStationGradedLowerPanel (metered charge)
open WilsonMeasuredPublicEntranceNativeLowerSignal (velocity difference)

def Earned {d:ℕ}(le:e≤d)(U:tower S)(x:Points 2)(T:ℝ)(q Q:ℕ)(L:S.Field d→ₗ[ℂ]ℂ)
    (X W:S.Field d)(eps:ℝ)(fee cap:I→ℝ):Prop:=
  1≤T ∧ x∈conf 2 ∧ IsUnit (metered B e T (frame R U B e a x)).det ∧ W∈LinearMap.range (F.sector.derivatives.rise le) ∧
  ‖L (X-W)‖*T^Q≤T^q*eps ∧ (∀j:I,‖ear R x (right R U B e j) (X-W)‖*T^j.2.1.val≤T^q*fee j) ∧
  ∀j:I,‖charge R U B e a x T Q (L.comp (F.sector.derivatives.rise le)) j‖*T^Q≤cap j*T^j.2.1.val

theorem original {U J:ℝ→tower S}(lead:Leading F J)(aligned:localCost trail U J){A:Type*}{l:Filter A}[NeBot l]
    {r t c:A→ℝ}{s g:ℝ}(hr:Tendsto r l trail)(ht:Tendsto t l (𝓝 s))(pos:∀i,0<t i)
    (hc:Tendsto c l (𝓝 g)){d:ℕ}(le:e≤d)(Z:Module.End ℂ (D d))
    (target:∀w,Tendsto (fun i=>PhysMS.Frame.cocycle d J (r i) (t i) (pos i) w) l (𝓝 (Z w)))
    (v:D d){x:A→Points 2}{y:Points 2}(hx:Tendsto x l (𝓝 y))(hy:y∈conf 2)
    (rank:IsUnit (panel R B e a y).det){z:A→Points 2}{w:Points 2}(hz:Tendsto z l (𝓝 w))(hw:w∈conf 2)
    {k:ℕ}(peer:D k)(q Q:ℕ)(order:q≤Q)(T:A→ℝ)(W:A→S.Field d)
    (eps:A→ℝ)(fee:A→I→ℝ)(cap:I→ℝ)(funded:∀j,0≤cap j)
    (smaller:Tendsto eps l (𝓝 0))(paid:∀j,Tendsto (fun i=>fee i j) l (𝓝 0))
    (actual:∀ᶠ i in l,Earned R F B e a le (U (r i)) (r i • x i) (T i) q Q
      (ear R (r i • z i) (U (r i) k peer)) (difference R U (r i) (t i) (c i) v) (W i) (eps i) (fee i) cap):
    let v₀:=velocity R s g Z v
    free R w (v₀-(Maxwell.Free.scheme R.family.labels).rise le
      (WilsonMeasuredPublicEntranceNativeLowerLimit.lower R B e a y v₀)) peer=0:=by
  intro v₀
  let X i:=difference R U (r i) (t i) (c i) v
  let L i:=ear R (S:=S) (e:=d) (r i • z i) (U (r i) k peer)
  let low i:=WilsonMeasuredPublicEntranceNativeLowerLeft.representative R (U (r i)) B e a (r i • x i) (X i)
  let gain i:=L i (X i-F.sector.derivatives.rise le (low i))
  have port:=WilsonMeasuredPublicEntranceNativeLowerSignal.original R F B e a lead aligned hr ht pos hc le Z target v hx hy rank hz hw peer
  have filed:=WilsonMeasuredPublicEntranceNativeLowerSignal.incoming R aligned hr ht pos hc Z target v
  have invert:=(WilsonMeasuredPublicEntranceNativeLowerLimit.original R F B e a lead aligned hr hx hy rank filed).1
  have small:Tendsto (fun i=>eps i+∑j:I,cap j*fee i j) l (𝓝 0):=by
    simpa only [mul_zero,Finset.sum_const_zero,add_zero] using smaller.add
      (tendsto_finsetSum Finset.univ fun j _=>(tendsto_const_nhds (x:=cap j)).mul (paid j))
  have first:∀ᶠ i in l,‖gain i‖≤eps i+∑j:I,cap j*fee i j:=by
    filter_upwards [actual,invert] with i bought unit
    obtain ⟨big,clear,tariff,old,head,axes,bill⟩:=bought
    have positive:0<T i:=lt_of_lt_of_le zero_lt_one big
    have booked:=WilsonMeasuredPublicEntranceNativeLowerBill.original R F (U (r i)) B e a le
      (r i • x i) clear unit (T i) positive tariff (X i) (W i) old q Q (L i) (eps i) (fee i) cap funded head axes bill
    have lowcost:‖gain i‖*(T i)^q≤‖gain i‖*(T i)^Q:=mul_le_mul_of_nonneg_left (pow_le_pow_right₀ big order) (norm_nonneg _)
    exact le_of_mul_le_mul_right (lowcost.trans (by simpa only [mul_comm ((T i)^q)] using booked)) (pow_pos positive q)
  exact norm_le_zero_iff.mp (le_of_tendsto_of_tendsto port.norm small first)

end YM.Integration.WilsonMeasuredPublicEntranceNativeLowerPayoff
end
