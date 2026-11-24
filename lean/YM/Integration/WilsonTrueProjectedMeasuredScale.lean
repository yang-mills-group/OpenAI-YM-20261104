import YM.Integration.WilsonTrueProjectedPrimaryHistory
import YM.Integration.WilsonPositionThermometerStationTransport
import YM.Integration.WilsonRegisteredRectangleChannelClock

/-! Original measured coordinates on a finite scale interval. The two
conversions from stored field coordinates to measured germs occur only at
its ends. All intermediate column costs come from the actual Wilson clock. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedMeasuredScale
open Function Filter Finset Lattice Wilson RG Labels Source Trace.Physical Trace.Physical.GermGraph
open Extra.Histories Extra.Histories.Relay AllOrder PhysicalNext Repeat Legato Next.Rank
open scoped Classical Topology Matrix.Norms.Frobenius
variable {G : Gauge} (C : Family G) {d m j N p : ℕ}
local notation "σ" => (C.labels.level d).coeffSize
local notation "X" => measuring C d N p

theorem column_cost (j : ℕ) :
    (C.path.levels.params (j+1)).columns ≤ ((C.S.block j).val : ℝ) := by
  let a := C.path.levels.params (j+1)
  have invoice := WilsonRegisteredRectangleChannelClock.cost C.path.levels j
  change 1+a.paths+a.width⁻¹+a.columns+a.clip.relaxation+a.supportExponent ≤ _ at invoice
  change a.columns ≤ _
  linarith only [invoice,a.paths_pos,inv_nonneg.mpr a.width_pos.le,a.price_pos,a.clip.radius_pos]

/-- The bound holds before both original regulators and for each fitted
numerical input, even one depending on the cutoff and physical volume. -/
theorem original (H : C.Makes) (hm : Opened C d m p) (hj : Opened C d j p)
    (later : m ≤ j) (live : j ≤ N) (v : C.label d) :
    σ (X m v) ≤ 4*(C.S.a m/C.S.a j)^(d+1)*σ (X j v) := by
  let T := C.factory d N p
  have posted := WilsonPositionThermometerStationTransport.interval (p:=p) (N:=N) C H hm.post later live
    (T.terminal v) 1 (fun i _ _ => by simpa only [Real.rpow_one] using column_cost C i)
  have atM := (size_gap d N p m H hm (later.trans live) v).1
  have atJ := (size_gap d N p j H hj live v).2
  have first := C.S.a_pos m
  have last := C.S.a_pos j
  simp only [Price.awake,Size.smul,norm_inv,norm_pow,Complex.norm_real,Real.norm_of_nonneg first.le,
    Real.norm_of_nonneg last.le,Real.rpow_one,Price.columns] at posted
  change ((C.S.a m)^d)⁻¹*σ (T.entries m (T.terminal.symm (T.terminal v))).x ≤
    (C.S.a m/C.S.a j)*(((C.S.a j)^d)⁻¹*σ (T.entries j (T.terminal.symm (T.terminal v))).x) at posted
  rw [T.terminal.symm_apply_apply] at posted
  have base : σ (T.entries m v).x ≤ (C.S.a m/C.S.a j)^(d+1)*σ (T.entries j v).x := by
    calc
      _ = (C.S.a m)^d*(((C.S.a m)^d)⁻¹*σ (T.entries m v).x) := by
        rw [←mul_assoc,mul_inv_cancel₀ (pow_ne_zero d first.ne'),one_mul]
      _ ≤ (C.S.a m)^d*((C.S.a m/C.S.a j)*(((C.S.a j)^d)⁻¹*σ (T.entries j v).x)) :=
        mul_le_mul_of_nonneg_left posted (pow_nonneg first.le d)
      _ = _ := by rw [pow_succ,div_pow]; field_simp [first.ne',last.ne']
  have budget : 0 ≤ (C.S.a m/C.S.a j)^(d+1) := by positivity
  change σ (X m v) ≤ 2*σ (T.entries m v).x at atM
  change σ (T.entries j v).x ≤ 2*σ (X j v) at atJ
  calc
    _ ≤ 2*((C.S.a m/C.S.a j)^(d+1)*(2*σ (X j v))) := by
      exact atM.trans (mul_le_mul_of_nonneg_left (base.trans (mul_le_mul_of_nonneg_left atJ budget)) zero_le_two)
    _ = _ := by ring

end YM.Integration.WilsonTrueProjectedMeasuredScale
