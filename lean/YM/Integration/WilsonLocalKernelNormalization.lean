import YM.RG02.Flat.Scalar
import YM.XSpace.Bare
import YM.RG.History

/-! The singular block normalization for a fixed number of observed links.
On one original calendar the scalar coefficient series and every remainder
constant are chosen before the lattice period and the blocking station. -/
noncomputable section
namespace YM.Integration.WilsonLocalKernelNormalization
open YM RG RG02 RG02.Asym PertExtension PertExtension.Chart PertExtension.Series
open PertExtension.Series.Tested PowerSeries Filter Lattice
open scoped Topology

variable {c f : Side} (S : StepData c f)
def scaled (G : Gauge) (k : ℕ) (t : ℝ) : ℂ :=
  ((((t : ℂ) ^ Friction.cardinal G)⁻¹ * (S.penaltyZ (t^2)⁻¹ G : ℂ))⁻¹) ^ k

theorem physical_factor (G : Gauge) (k : ℕ) (t : ℝ) :
    scaled S G k t = (t : ℂ)^(Friction.cardinal G * k) *
      ((S.penaltyZ (t^2)⁻¹ G : ℂ)⁻¹)^k := by
  unfold scaled
  rw [mul_inv_rev, inv_inv, mul_pow, pow_mul, mul_comm]

def coefficients (G : Gauge) (k : ℕ) : PowerSeries ℂ :=
  ((Friction.paidSeries S (XSpace.Bare.chart G))⁻¹) ^ k

/-- Genuine Haar normalization of k links, including the leading determinant power. -/
theorem all_orders (G : Gauge) (k : ℕ) :
    Near (scaled S G k) (coefficients S G k) := by
  let η := XSpace.Bare.chart G
  have hη := XSpace.Bare.chart_ratio G
  have hz : coeff 0 (Friction.paidSeries S η) ≠ 0 := by
    rw [Friction.paid_base S η hη]
    exact Complex.ofReal_ne_zero.mpr (mul_pos (Therm.leading_pos ..) hη.scale).ne'
  exact Near.stand (Near.fine_inverse (Friction.restored S η hη) hz) k

/-- The profile and constant are shared by all clocks of the same funded kernel.
No bound on the surrounding lattice volume occurs. -/
theorem calendar {G : Gauge} (D : Calendar G) (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t in Tested.germ, ∀ m p : ℕ,
      ‖scaled (D.op m p) G k t -
        peval (fun i => coeff i (coefficients (D.op 0 0) G k)) n t‖ ≤ C*t^(n+1) := by
  obtain ⟨C,hC,h⟩ := all_orders (D.op 0 0) G k n
  refine ⟨C,hC,h.mono ?_⟩
  intro t ht m p
  exact ht

end YM.Integration.WilsonLocalKernelNormalization
