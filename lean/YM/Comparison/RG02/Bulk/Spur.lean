import YM.Comparison.RG02.Bulk.Fk
import YM.Comparison.RG02.Order.Rim
/-! Real calibration form of the Fk unmarked scalar. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Bulk
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open Next.SectorChange
open PertExtension.Series Multi Marker Order Assembly Cumulants
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G}
    {O : ChartRatio G} {V : Type} [Fintype V] [DecidableEq V] {R : Census V}
  (K : Kernel S p P O) (F : Forest S.ratio) (t : S.Choices)
  (W : Colors R G f) (x : fieldDir G c 1) (r : ℕ)

-- no marker input contributes to unmarked. This also isolates volume factor prices later.
private lemma no_mark {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (u:E)
    (w : Hot R→E→ℂ) (l : Hot R→ℕ) : PowerSeries.map (blank R).toRingHom (markExp (curve l w u))=1 := by
    let L := PowerSeries.map (blank R).toRingHom
    let d := curve l w u
    have he : L d=0 := by ext1 i; rw [PowerSeries.coeff_map]; exact mark_curve_quiet l w u i
    let f := markExp d
    have hm (p : PTable R) (a : ℂ) : L (a • p)=a • L p := by ext1 i; rw [PowerSeries.coeff_map,PowerSeries.coeff_smul]; rw [PowerSeries.coeff_smul, PowerSeries.coeff_map]; exact Poly.part_smul ..
    change L f=1; unfold f markExp; simp_rw [map_sum,hm,map_pow,he]; simp [zero_pow_eq]

private lemma at_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : Hot R→E→ℂ) (l : Hot R→ℕ) (f : E→ℝ) (u:E) (n : ℕ) :
    rows (expansions l w f) R.quiet n u = Complex.ofReal (Radial.expsum (Radial.layers f) n n u) := by
   unfold rows; change ((blank R).toRingHom ((PowerSeries.coeff n) (expansions l w f u)))=_
   rw [← PowerSeries.coeff_map, expansions,map_mul,no_mark,mul_one, PowerSeries.coeff_map,realCoeff]; exact (blank R).commutes _
lemma uncolored : Order.Simple (Fk K F t W x r) := by
   apply real_entries; intro i; rw [table]; refine (Rim.natural (Nat.factorial i.val.card)).mul <| Rim.integrate _ fun y=>?_ ; rw [at_zero]; exact Rim.ofReal _

lemma clear {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (w : Hot R→E→ℂ) (l:Hot R→ℕ) (f:E→ℝ) (u:E) (n:ℕ) :
    rows (expansions l w f) R.quiet n u= Complex.ofReal (Radial.expsum (Radial.layers f) n n u):= at_zero ..

end YM.Comparison.RG02.Bulk
