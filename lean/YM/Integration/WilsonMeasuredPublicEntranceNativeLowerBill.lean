import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerLeft

/-! One left representative of a physical field in the lower measured space.
The same representative is used for every subsequently chosen right detector. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceNativeLowerBill
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

theorem difference {V:Type*}[AddCommGroup V][Module ℂ V](L:V→ₗ[ℂ]ℂ)(v A W:V)(c:ℂ)
    (born:ℂ)(T:ℝ)(tp:0≤T)(Q:ℕ)(eb ea:ℝ)
    (hb:‖L (v-W)-c*born‖*T^Q≤eb)(ha:‖L A-born‖*T^Q≤ea):
    ‖L ((v-c • A)-W)‖*T^Q≤eb+‖c‖*ea:=by
  have eq:L ((v-c • A)-W)=(L (v-W)-c*born)-c*(L A-born):=by
    simp only [map_sub,map_smul,smul_eq_mul]
    ring
  rw [eq]
  calc _≤(‖L (v-W)-c*born‖+‖c*(L A-born)‖)*T^Q:=mul_le_mul_of_nonneg_right (norm_sub_le _ _) (pow_nonneg tp Q)
       _=‖L (v-W)-c*born‖*T^Q+‖c‖*(‖L A-born‖*T^Q):=by rw [norm_mul];ring
       _≤eb+‖c‖*ea:=add_le_add hb (mul_le_mul_of_nonneg_left ha (norm_nonneg _))

theorem original {h:ℕ}(le:e≤h)(x:Points 2)(clear:x∈conf 2)
    (unit:IsUnit (frame R U B e a x).det)(T:ℝ)(tp:0<T)
    (tariff:IsUnit (metered B e T (frame R U B e a x)).det)
    (X W:S.Field h)(old:W∈LinearMap.range (F.sector.derivatives.rise le))
    (q Q:ℕ)(L:S.Field h→ₗ[ℂ]ℂ)(eps:ℝ)(fee cap:I→ℝ)(funded:∀j,0≤cap j)
    (head:‖L (X-W)‖*T^Q≤T^q*eps)
    (axis:∀j:I,‖ear R x (right R U B e j) (X-W)‖*T^j.2.1.val≤T^q*fee j)
    (bill:∀j:I,‖charge R U B e a x T Q (L.comp (F.sector.derivatives.rise le)) j‖*T^Q≤cap j*T^j.2.1.val):
    ‖L (X-F.sector.derivatives.rise le (WilsonMeasuredPublicEntranceNativeLowerLeft.representative R U B e a x X))‖*T^Q≤
      T^q*(eps+∑j:I,cap j*fee j):=by
  let pay:=charge R U B e a x T Q (L.comp (F.sector.derivatives.rise le))
  let y (j:I):=ear R x (right R U B e j) (X-W)
  have paid (j:I):‖pay j*y j‖*T^Q≤T^q*(cap j*fee j):=by
    calc _=‖y j‖*(‖pay j‖*T^Q):=by rw [norm_mul];ring
         _≤‖y j‖*(cap j*T^j.2.1.val):=mul_le_mul_of_nonneg_left (bill j) (norm_nonneg _)
         _=cap j*(‖y j‖*T^j.2.1.val):=by ring
         _≤cap j*(T^q*fee j):=mul_le_mul_of_nonneg_left (axis j) (funded j)
         _=T^q*(cap j*fee j):=by ring
  rw [WilsonMeasuredPublicEntranceNativeLowerLeft.original R F U B e a le x clear unit T tp tariff X W old Q L]
  calc
    _≤(‖L (X-W)‖+∑j:I,‖pay j*y j‖)*T^Q:=
      mul_le_mul_of_nonneg_right ((norm_sub_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))) (pow_nonneg tp.le Q)
    _≤T^q*(eps+∑j:I,cap j*fee j):=by
      rw [add_mul,Finset.sum_mul,mul_add,Finset.mul_sum]
      exact add_le_add head (Finset.sum_le_sum fun j _=>paid j)

end YM.Integration.WilsonMeasuredPublicEntranceNativeLowerBill
end
