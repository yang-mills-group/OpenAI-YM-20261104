import YM.Integration.WilsonPhysicalStationGradedLowerPanel

/-! One left representative of a physical field in the lower measured space.
The same representative is used for every subsequently chosen right detector. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceNativeLowerLeft
open Function Filter Finset Set Lattice Wilson RG Source Cells GapsContact.Seams Trace.Terrace
open PhysicalNext.Repeat.Legato Extraction RG17 Spec Table Table.Pairing Climb Trace.Pilot PhysMS
open Maxwell Maxwell.Wick XSpace XSpace.Normalize XSpace.Structure1
open MS MS.Land MS.Menus MS.Theater Local.Physical
open WilsonPhysicalStationLowerReceiver (ear raised)
open WilsonPhysicalStationGradedLowerPanel (left right frame metered charge solves)
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    (U:tower S)(B:Deck G)(e:ℕ)(a:Axis)
local notation "I" => Glyph B e

def ears {h:ℕ}(x:Points 2)(v:S.Field h):I→ℂ:=fun j=>ear R x (right R U B e j) v

def coefficients {h:ℕ}(x:Points 2)(X:S.Field h):I→ℂ:=
  ears R U B e x X ᵥ* (frame R U B e a x)⁻¹

def representative {h:ℕ}(x:Points 2)(X:S.Field h):S.Field e:=
  ∑i:I,coefficients R U B e a x X i • left R U B e a i

theorem matched {h:ℕ}(x:Points 2)(unit:IsUnit (frame R U B e a x).det)(X:S.Field h)(j:I):
    ear R x (right R U B e j) (representative R U B e a x X)=ear R x (right R U B e j) X:=by
  let A:=frame R U B e a x
  let y:=ears R U B e x X
  have recover:(y ᵥ* A⁻¹) ᵥ* A=y:=by
    rw [Matrix.vecMul_vecMul,Matrix.nonsing_inv_mul _ unit,Matrix.vecMul_one]
  simpa only [representative,map_sum,map_smul,smul_eq_mul,coefficients,Matrix.vecMul,dotProduct,
    A,y,WilsonPhysicalStationGradedLowerPanel.frame,ears] using congrFun recover j

theorem original {h:ℕ}(le:e≤h)(x:Points 2)(clear:x∈conf 2)
    (unit:IsUnit (frame R U B e a x).det)(T:ℝ)(tp:0<T)
    (tariff:IsUnit (metered B e T (frame R U B e a x)).det)
    (X W:S.Field h)(old:W∈LinearMap.range (F.sector.derivatives.rise le))
    (Q:ℕ)(L:S.Field h→ₗ[ℂ]ℂ):
    let pay:=charge R U B e a x T Q (L.comp (F.sector.derivatives.rise le))
    L (X-F.sector.derivatives.rise le (representative R U B e a x X))=
      L (X-W)-∑j:I,pay j*ear R x (right R U B e j) (X-W):=by
  intro pay
  let rise:=F.sector.derivatives.rise le
  let V:=representative R U B e a x X
  obtain ⟨w,rfl⟩:=old
  have booked (Y:S.Field e):∑j:I,pay j*ear R x (right R U B e j) Y=L (rise Y):=by
    have eq:=DFunLike.congr_fun (solves R U B e a x T tp Q (L.comp rise) tariff) Y
    simpa only [LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,LinearMap.comp_apply] using eq
  have cost:∑j:I,pay j*ear R x (right R U B e j) (X-rise w)=L (rise (V-w)):=by
    rw [←booked]
    refine Finset.sum_congr rfl fun j _=>?_
    have atOld:=DFunLike.congr_fun (raised R F le x clear (right R U B e j)) w
    simp only [LinearMap.comp_apply] at atOld
    rw [map_sub,map_sub,atOld,matched R U B e a x unit X j]
  rw [cost,map_sub,map_sub,map_sub,map_sub]
  ring

end YM.Integration.WilsonMeasuredPublicEntranceNativeLowerLeft
end
