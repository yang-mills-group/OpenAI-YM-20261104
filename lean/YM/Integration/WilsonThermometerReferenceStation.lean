import YM.Integration.WilsonPositionThermometerStationNorm
import YM.TraceExtension.Terrace.Annual

/-! Size of the original reference coordinate before both regulators on a checked physical station. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerReferenceStation
open Function Set Filter Finset RG Labels Source Lattice Wilson Next.Rank Next.Rank.East Next.Rank.Price
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East
open scoped BigOperators Classical Topology
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {H : (Bel C.book).Hierarchy}

/-- The two exact engineering factors at the same reference seat. -/
theorem balance (C : Family G) (d k : ℕ) :
    outward C d k * (C.S.a k)^d = Real.exp (Work.D01.columnLogs C.path.levels k) := by
  rw [Trace.Terrace.waters, mul_assoc]
  have a : Real.exp (C.S.scale k) = (C.S.a k)⁻¹ :=
    Real.exp_log (inv_pos.mpr (C.S.a_pos k))
  change Real.exp _ * (Real.exp (C.S.scale k*(d:ℝ)) * (C.S.a k)^d) = _
  rw [mul_comm (C.S.scale k), Real.exp_nat_mul, a, inv_pow,
    inv_mul_cancel₀ (pow_ne_zero d (C.S.a_pos k).ne'), mul_one]

theorem original (construction : C.Makes) {d k N : ℕ} (p : ℕ)
    (early : C.ref d ≤ k) (top : k ≤ N) (x : C.label d) :
    (C.labels.level d).coeffSize x ≤ Real.exp (Work.D01.columnLogs C.path.levels k) *
      (C.labels.level d).coeffSize (awake C d k N p x) := by
  simpa only [balance] using reference_size C construction early top p x

theorem cutoff (smooth : G.Simple) (construction : C.Makes) (d : ℕ) (ε : ℝ) (positive : 0<ε) :
    ∀ᶠ k in atTop, ∀ {D : ℕ} (V : Vane C D) (j : Fin (D+1)), j.val=d → V.k=k →
      V.checked f H D → ∀ (w : (Bel C.book).Field j) (N p : ℕ), k<N →
      (C.labels.level j).coeffSize (V.wheel.atCut (N,p) j w) ≤
        Real.exp (Work.D01.columnLogs C.path.levels k) *
          ((C.path.levels.clock.hatBeta k)^ε * (WilsonPositionThermometerStationNorm.cost C d * ‖w‖)) := by
  filter_upwards [WilsonPositionThermometerStationNorm.original (f:=f) (H:=H) smooth construction d ε positive]
    with k priced D V j rank seat checked w N p top
  have early : C.ref j ≤ k := seat ▸ checked.early j
  exact (original construction p early top.le _).trans
    (mul_le_mul_of_nonneg_left (priced V j rank seat checked w N p top) (Real.exp_pos _).le)

end YM.Integration.WilsonThermometerReferenceStation
