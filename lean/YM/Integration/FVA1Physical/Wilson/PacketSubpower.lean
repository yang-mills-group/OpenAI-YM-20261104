import YM.Integration.FVA1Physical.Wilson.PacketReceipt
import YM.Integration.FVA1Physical.Wilson.PacketScale

/-! The inherited-source estimate is homogeneous in the complete rooted norm
of its independent incoming coefficients. The stage never depends on that bank. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Set Filter Finset Matrix MeasureTheory MvPolynomial Lattice RG YM.Wilson Tree Precision Exterior
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Bakery MSbar.Bakery.Portal MSbar.Bakery.Film MSbar.Heath MSbar.Heath.Cottage MSbar.Heath.Stock
open MSbar.Bout MSbar.Lis MSbar.Mosaic MSbar.Rolling MSbar.Kelvin MSbar.Lapaz Push.Uniform Next.SectorChange
open YM.Integration.FVA1Physical.Round2.Curvature
open scoped Classical BigOperators
variable {G:Gauge}

/-- Spatial support may spread throughout the entire torus. Only the anchored
all-degree norm is charged, with the exact power of the same measured width. -/
theorem subpower_port (A:Issue G) (p degree:ℕ) {y δ E:ℝ} (hy:0<y)
    (b:Site A.f) (Z:Positions (Primary A.c G)) (V:Voice G) (χ:ChartRatio G) (kind:Kind A.T)
    (pd:(mold A.pre A.F A.v).PosDef) (paid:InheritedPort A χ V p degree y E b Z) (P:Palisade) (copied:Bool)
    (T:Nesting G A.f) (bank:BankPaid b y 0 p degree δ T) (flat:(PowerSeries.coeff 0 T).totalDegree=0)
    (U:Config G A.f) (inside:U∈A.regionX y b Z V P) :
    |A.modelP y b Z P V (fun v=>clockReading p A.fClock T (chartLog A.fClock (packetConfig A V y b Z copied v))) U -
      taste p (innerColumn A χ V y (A.fClock•Z) b U (enterRows A T) p) A.fClock| ≤ y^δ*E := by
  let q:ℝ:=y^δ
  have hq:0 < q:=Real.rpow_pos_of_pos hy _
  have flat':(PowerSeries.coeff 0 (q⁻¹ • T)).totalDegree=0:=by
    rw [PowerSeries.coeff_smul];exact Nat.eq_zero_of_le_zero ((MvPolynomial.totalDegree_smul_le ..).trans flat.le)
  have bound:=paid P copied (q⁻¹ • T) (bank_paid_normalize b hy bank) flat' U inside
  simp_rw [bank_clock_smul] at bound
  rw [model_smul,inner_smul A V χ y b U (A.fClock•Z) p A.fClock q⁻¹ T kind pd,←mul_sub,abs_mul,abs_of_pos (inv_pos.mpr hq)] at bound
  have rescale:=mul_le_mul_of_nonneg_left bound hq.le
  simpa only [←mul_assoc,mul_inv_cancel₀ hq.ne',one_mul,q] using rescale

end YM.Integration.FVA1Physical.Wilson
