import YM.Integration.WilsonThermometerPositionFilmChartContact
import YM.Integration.WilsonThermometerOriginalCoveredRows

/-! Both coefficients of the original conditional Gaussian on the real forest and its retained link field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerPositionFilmCloudReading
open Finset Function MeasureTheory Lattice RG Tree Wilson Exterior Precision Marker Multi Comparison.RG02
open Comparison.RG02.Assembly Comparison.RG02.Cumulants Comparison.RG02.Order
open PertExtension.Series YM.Next.SectorChange YM.Primitives.GCC.Anchor WilsonThermometerPositionFilmChartContact
open scoped Classical BigOperators
variable {G:Gauge} {c f:Side} {V:Type} [DecidableEq V] [Fintype V] {R:Census V}
  {S:StepData c f} {clip:Clip} {P:PathData G} {O:ChartRatio G}
  (K:Bulk.Kernel S clip P O) (F:Forest S.ratio) (t:S.Choices)
  (C:Bulk.Colors R G f) (s:R.Mode) (x:fieldDir G c 1)

local notation "zrow" z:max => Bulk.translated K F x z
local notation "μ" => Gaussian.cloud (K.covariance F t)
local notation "I" => Precision.Key F G

def paid (j:ℕ) (z:I→ℝ) : ℂ :=
  rows (expansions C.power (Bulk.markFn S F C) (Bulk.geometric K F t C)) s j (zrow z)

theorem integrable (j:ℕ) : Integrable (paid K F t C s x j) μ := by
  have h:=(gather (Bulk.stage K F x) (Bulk.hinge F) C.power (Bulk.markFn S F C)
    (Bulk.geometric K F t C) (K.covariance F t) (K.symm F t) (K.positive F t) s (pick j j)).1
  rw [picked j (le_refl j)] at h
  exact h

def noise (z:I→ℝ) : ℂ := (jet (Bulk.geometric K F t C) 3 (zrow z):ℝ)

private theorem position (z:I→ℝ) : zrow z=(1,(zrow z).2) := by
  rw [Bulk.footing]

omit [Fintype V] in
private theorem clean (z:I→ℝ) :
    Radial.expsum (Radial.layers (Bulk.geometric K F t C)) 0 0 (zrow z)=1 := by
  norm_num [Radial.expsum,Zone.TaylorPow,sum_range_succ]

omit [Fintype V] in
private theorem cubic (z:I→ℝ) :
    Radial.expsum (Radial.layers (Bulk.geometric K F t C)) 1 1 (zrow z)=
      -jet (Bulk.geometric K F t C) 3 (zrow z) := by
  norm_num only [Radial.expsum,Radial.layers,Finset.sum_range_succ,Finset.sum_range_zero,
    Zone.TaylorPow,Zone.mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,if_true,if_false,
    zero_mul,mul_zero,one_mul,mul_one,zero_add,add_zero,Nat.factorial,←jet_eq,
    Nat.reduceSub,Nat.reduceAdd,neg_add_cancel]

theorem ground (z:I→ℝ) : paid K F t C s x 0 z=bent S F C s 0 (zrow z).2 := by
  unfold paid rows expansions
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,map_mul,←PowerSeries.coeff_zero_eq_constantCoeff_apply,
    ←PowerSeries.coeff_zero_eq_constantCoeff_apply,realCoeff,clean,Complex.ofReal_one,map_one,one_mul]
  rw [position K F x z]
  rfl

theorem first (z:I→ℝ) : paid K F t C s x 1 z=
    bent S F C s 1 (zrow z).2 - noise K F t C x z * bent S F C s 0 (zrow z).2 := by
  unfold paid rows expansions
  rw [PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,Nat.reduceSub,Nat.sub_zero,
    realCoeff,clean,cubic,Complex.ofReal_one,Complex.ofReal_neg,Poly.product_bead,one_smul,
    Poly.part_plus,Poly.part_smul]
  unfold noise bent rows
  rw [position K F x z]
  ring

theorem observed (p j:ℕ) (fits:j≤p) :
    (Order.observe R p (Bulk.Fk K F t C x p) j).part s=∫ z,paid K F t C s x j z ∂μ :=
  order_read (Bulk.stage K F x) (Bulk.hinge F) C.power (Bulk.markFn S F C) (Bulk.geometric K F t C)
    (K.covariance F t) (K.symm F t) (K.positive F t) s fits

end YM.Integration.WilsonThermometerPositionFilmCloudReading
