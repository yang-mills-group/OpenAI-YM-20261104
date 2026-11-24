import YM.Integration.WilsonThermometerUnitFilingPinEdition
import YM.Integration.WilsonThermometerUnitFilingPinCharge
import YM.Integration.WilsonThermometerUnitFilingRowIncome

/-! Absolute one-row wages for the complete cover packet along a genuinely enrolled family. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingPinSalary
open Function Finset Gauge Lattice RG Wilson QuadraticLocal Marker QuadraticLocal.Earn Stationary
open RegulatorIR Geometry Taping Budget Budget.Packet Budget.Tuple Diagram Prim Profiles Halo Ledger Ledger.Sky
open WilsonThermometerUnitFilingCoverInvoice WilsonThermometerUnitFilingPinEdition
open scoped Classical BigOperators ENNReal

variable {G:Gauge}{n:Side}{o:Passport n Unit}{J:Census Unit}{I X:Type}
  (M:I→Row o J G X)(t:X)(a:ℂ→L[ℝ]ℝ){h:ℕ}(grade:∀ i,h ≤ (M i).lamp.toll+1)(z:Cover)
  {w:Unit→ℝ}{grades:Unit→ℕ}{σ C δ β:ℝ}{ord cap H:ℕ}
  (stock:Scene.Armada M w grades σ C ord cap H)
  {W:Type}{k:W→ℕ}{sides:Page k→Side}{S:Heir sides G}(T:S.Accounts)(v:W)

def wage (w:Unit→ℝ)(σ δ β:ℝ)(h e:ℕ)(i:I):ℝ:=
  |invoice G (e+h) 0 δ β (WilsonThermometerUnitFilingRowIncome.cash M w σ i) (w ())|

include stock in
theorem summable (e:ℕ):Summable (wage M w σ δ β h e):=by
  let c:ℝ:=(3+8*((e+h:ℕ):ℝ))^0*WilsonThermometerUnitFilingMomentSale.price G (e+h) 0 δ*β^δ/w ()
  have same:wage M w σ δ β h e=fun i=>|c*WilsonThermometerUnitFilingRowIncome.cash M w σ i|:=by
    funext i;unfold wage WilsonThermometerUnitFilingCoverInvoice.invoice c;apply congr_arg abs;ring
  rw [same]
  exact ((WilsonThermometerUnitFilingRowIncome.summable M w σ stock).mul_left c).abs

include stock T v in
theorem original (seed:0<σ)(tiny:0<δ)(late:Real.exp 1 ≤ β)(paid:Real.exp (σ⁻¹^2) ≤ β)
    (re:‖a‖ ≤ 1)(e r:ℕ)(i:I):
    quota (row M t a grade z i e r) 1 ≤ ENNReal.ofReal (wage M w σ δ β h e i):=by
  let q:Orders (Prim.Foot G):=(stamp_symbol (ink M t a grade i)).choose
  have earned:=WilsonThermometerUnitFilingCoverShare.original (fun _:Unit=>M i) Finset.univ t a T
    (fun _=>single M t a i) (fun _=>ink M t a grade i) v rfl
    (WilsonThermometerUnitFilingRowIncome.single M w σ stock i) seed tiny late paid
    (stock.positive ()) re (l:=1) (ρ:=1) zero_lt_one zero_lt_one le_rfl e r 0
  let x:=Motion.slide 1 z
  let grid:=WilsonThermometerUnitFilingPinCharge.grid (G:=G) 1 1 zero_lt_one 0 x
  have shifted:=WilsonThermometerUnitFilingPinCharge.original (l:=1) (ρ:=1) zero_lt_one
    0 x z (show dist x (Motion.slide 1 z) ≤ 1 by simp [x]) (q e r)
  have dom:quota (row M t a grade z i e r) 1 ≤ markQ grid (row M t a grade z i e r):=
    quota_mono _ (fun y=>grid.width_unit y)
  apply dom.trans (shifted.trans ?_)
  rw [pow_zero,mul_one]
  exact earned.trans (ENNReal.ofReal_le_ofReal (le_abs_self _))

end YM.Integration.WilsonThermometerUnitFilingPinSalary
