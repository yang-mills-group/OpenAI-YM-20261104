import YM.Pier.Lair.Travel
import YM.PhysMS.Frame.Step

/-! The bounded-ratio mixed Gram receiver in the original physical quotient. -/

noncomputable section
namespace YM.Integration.WilsonOrdinaryMixedGram
open Filter Set Spec Climb SharpGram OPE.Levy Push.FiniteDetection.Free Trace.Pilot
open scoped Topology

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable (F : Final C f S) (J : ℝ → PhysMS.tower S) (d : ℕ)
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field d

/-- Both physical legs are measured at the ordinary reflected detector pair of radius
`r`. The first leg carries the field normalized at `s`, the second that at `r`. -/
def mixed (r s : ℝ) : RealForm D D :=
  pullBoth ((J s d).toLinearMap.restrictScalars ℝ) ((J r d).toLinearMap.restrictScalars ℝ)
    (glass S F.room.kernel.spin d (r • detectors))

/-- Read a proposed relative frame `A` against the actual radius-`r` reflected form. -/
def trial (r : ℝ) (A : D →ₗ[ℝ] D) : RealForm D D :=
  pullBoth A LinearMap.id (Pier.Lair.arcPrice F d (J r d) (r • detectors))

theorem mixed_eq (r s : ℝ) (v w : D) : mixed F J d r s v w =
    Pier.Lair.arcPrice F d (J r d) (r • detectors) ((J r d).symm (J s d v)) w := by
  simp only [mixed,Pier.Lair.arcPrice,pullBoth_read,LinearMap.coe_restrictScalars,
    LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]

/-- Uniformly invert the actual Gram on the final field quotient. A measured mixed
error bounds the frame error, for every proposed numerical truncation and every slot.
The trial and mixed terms share the same actual radius, sites, and second physical leg. -/
theorem read_frame (P : Pier.Lair.Present F J) : ∃ K : ℝ, 0 < K ∧ ∀ᶠ r in trail,
    ∀ s : ℝ, ∀ A : D →ₗ[ℝ] D, ∀ v : D,
    ‖(J r d).symm (J s d v) - A v‖ ≤
      K * ‖mixed F J d r s - trial F J d r A‖ * ‖v‖ := by
  let δ := Lenses.margin C d / 2
  have hδ : 0 < δ := half_pos (Weak.Portfolio.freely (C:=C) d).choose_spec.1
  refine ⟨δ⁻¹,inv_pos.mpr hδ,?_⟩
  filter_upwards [Pier.Lair.heights F P d] with r hg s A v
  let g := Pier.Lair.arcPrice F d (J r d) (r • detectors)
  let b := mixed F J d r s - trial F J d r A
  let z := (J r d).symm (J s d v) - A v
  change ‖z‖ ≤ δ⁻¹ * ‖b‖ * ‖v‖
  have identify : g z z = b v z := by
    change g ((J r d).symm (J s d v) - A v) z = mixed F J d r s v z - trial F J d r A v z
    rw [mixed_eq]
    exact congrArg (fun h : D →L[ℝ] ℝ => h z) (map_sub g ((J r d).symm (J s d v)) (A v))
  have test : δ * ‖z‖^2 ≤ (‖b‖ * ‖v‖) * ‖z‖ := by
    calc
      _ ≤ g z z := hg.1 z
      _ = b v z := identify
      _ ≤ ‖b v z‖ := le_abs_self _
      _ ≤ ‖b v‖ * ‖z‖ := (b v).le_opNorm z
      _ ≤ _ := mul_le_mul_of_nonneg_right (b.le_opNorm v) (norm_nonneg _)
  by_cases hz : z = 0
  · rw [hz,norm_zero]; positivity
  have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have cancel : δ * ‖z‖ ≤ ‖b‖ * ‖v‖ := (mul_le_mul_iff_left₀ hz').mp (by simpa [pow_two,mul_assoc] using test)
  calc
    ‖z‖ = δ⁻¹ * (δ * ‖z‖) := by rw [← mul_assoc, inv_mul_cancel₀ hδ.ne', one_mul]
    _ ≤ δ⁻¹ * (‖b‖ * ‖v‖) := mul_le_mul_of_nonneg_left cancel (inv_pos.mpr hδ).le
    _ = _ := (mul_assoc ..).symm

end YM.Integration.WilsonOrdinaryMixedGram
