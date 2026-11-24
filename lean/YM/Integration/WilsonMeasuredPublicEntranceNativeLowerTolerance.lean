import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerPayoff
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceNativeLowerTolerance
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

open WilsonMeasuredPublicEntranceNativeLowerPayoff (Earned)
open WilsonMeasuredPublicEntranceNativeLowerSignal (difference velocity)
open WilsonPhysicalStationLowerReceiver (ear)

def Meter {d:ℕ}(le:e≤d)(U:tower S)(x:Points 2)(q Q:ℕ)(L:S.Field d→ₗ[ℂ]ℂ)(X:S.Field d)(tol:ℝ):Prop:=
  ∃(T:ℝ)(W:S.Field d)(eps:ℝ)(fee cap:I→ℝ),(∀j,0≤cap j) ∧ Earned R F B e a le U x T q Q L X W eps fee cap ∧
    eps+∑j:I,cap j*fee j≤tol

theorem station {d:ℕ}(le:e≤d)(U:tower S)(x:Points 2)(unit:IsUnit (frame R U B e a x).det)
    {q Q:ℕ}(up:q≤Q)(L:S.Field d→ₗ[ℂ]ℂ)(X:S.Field d){tol:ℝ}(price:Meter R F B e a le U x q Q L X tol):
    ‖L (X-F.sector.derivatives.rise le (representative R U B e a x X))‖≤tol:=by
  obtain ⟨T,W,eps,fee,cap,nonneg,⟨big,clear,tariff,old,head,axes,bill⟩,final⟩:=price
  have positive:0<T:=lt_of_lt_of_le zero_lt_one big
  have booked:=WilsonMeasuredPublicEntranceNativeLowerBill.original R F U B e a le x clear unit T positive tariff X W old q Q L eps fee cap nonneg head axes bill
  have low:‖L (X-F.sector.derivatives.rise le (representative R U B e a x X))‖*T^q≤
      ‖L (X-F.sector.derivatives.rise le (representative R U B e a x X))‖*T^Q:=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ big up) (norm_nonneg _)
  exact (le_of_mul_le_mul_right (low.trans (by simpa only [mul_comm (T^q)] using booked)) (pow_pos positive q)).trans final

theorem original {U J:ℝ→tower S}(lead:Leading F J)(aligned:localCost trail U J){A:Type*}{l:Filter A}[NeBot l]
    {r t c:A→ℝ}{s g:ℝ}(hr:Tendsto r l trail)(ht:Tendsto t l (𝓝 s))(pos:∀i,0<t i)
    (hc:Tendsto c l (𝓝 g)){d:ℕ}(le:e≤d)(Z:Module.End ℂ (D d))
    (target:∀w,Tendsto (fun i=>PhysMS.Frame.cocycle d J (r i) (t i) (pos i) w) l (𝓝 (Z w)))
    (v:D d){x:A→Points 2}{y:Points 2}(hx:Tendsto x l (𝓝 y))(hy:y∈conf 2)
    (rank:IsUnit (panel R B e a y).det){z:A→Points 2}{w:Points 2}(hz:Tendsto z l (𝓝 w))(hw:w∈conf 2)
    {k:ℕ}(peer:D k)(q Q:ℕ)(order:q≤Q)(actual:∀tol:ℝ,0<tol→∀ᶠi in l,
      Meter R F B e a le (U (r i)) (r i • x i) q Q (ear R (r i • z i) (U (r i) k peer))
        (WilsonMeasuredPublicEntranceNativeLowerSignal.difference R U (r i) (t i) (c i) v) tol):
    let v₀:=velocity R s g Z v
    free R w (v₀-(Maxwell.Free.scheme R.family.labels).rise le
      (WilsonMeasuredPublicEntranceNativeLowerLimit.lower R B e a y v₀)) peer=0:=by
  intro v₀
  let X i:=WilsonMeasuredPublicEntranceNativeLowerSignal.difference R U (r i) (t i) (c i) v
  let L i:=ear R (S:=S) (e:=d) (r i • z i) (U (r i) k peer)
  let low i:=representative R (U (r i)) B e a (r i • x i) (X i)
  let gain i:=L i (X i-F.sector.derivatives.rise le (low i))
  have port:=WilsonMeasuredPublicEntranceNativeLowerSignal.original R F B e a lead aligned hr ht pos hc le Z target v hx hy rank hz hw peer
  have filed:=WilsonMeasuredPublicEntranceNativeLowerSignal.incoming R aligned hr ht pos hc Z target v
  have invert:=(WilsonMeasuredPublicEntranceNativeLowerLimit.original R F B e a lead aligned hr hx hy rank filed).1
  apply norm_le_zero_iff.mp
  apply le_of_forall_pos_le_add
  intro tol positive
  rw [zero_add]
  apply le_of_tendsto port.norm
  filter_upwards [actual tol positive,invert] with i paid unit using
    station R F B e a le (U (r i)) (r i • x i) unit order (L i) (X i) paid

end YM.Integration.WilsonMeasuredPublicEntranceNativeLowerTolerance
end
