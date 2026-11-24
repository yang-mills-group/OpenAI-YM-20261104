import YM.Integration.WilsonCenteredCompactBooking

/-! A fixed dilation changes the reporting scale of an actual cluster while
preserving its signed integral on every individual microscopic cell. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredSourceScale
open Function Set Filter MeasureTheory Analysis Table Spec Lattice Extraction Next.UVStress
open Wilson RG Source PhysicalNext.Repeat.Legato StressFlux.Matching Finset Cells
open WilsonCenteredPhysicalPanel WilsonCenteredCompactBooking
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) {n:ℕ}

private theorem indicator (φ:Test n)(r:ℝ)(k:ℕ×ℕ)(u:Sites R k n):
    mass R φ r k u = φ.applyTo (fun x=> if site R r k x=u then 1 else 0) :=by
  change (∫x in cell R r k u,φ x) = ∫x,φ x*_
  rw [←integral_indicator (measurable_cell R r k u)]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx:site R r k x=u <;> simp [cell,hx]

theorem mass_at (φ:Test n){c:ℝ}(hc:0<c)(r:ℝ)(k:ℕ×ℕ)(u:Sites R k n):
    mass R (dilate (inv_pos.mpr hc) φ) (c*r) k u = mass R φ r k u :=by
  rw [indicator,indicator,zoom_integral]
  apply integral_congr_ae
  filter_upwards with x
  have same:site R (c*r) k (c⁻¹•x)=site R r k x:=by
    simp only [site,smul_smul,show c*r*c⁻¹=r by field_simp]
  rw [same]

theorem active (φ:Test n)(r:ℝ)(k:ℕ×ℕ)(u:Sites R k n)(paid:mass R φ r k u≠0):
    ∃x∈tsupport (φ:Points n→ℂ), site R r k x=u :=by
  by_contra! none
  apply paid
  rw [indicator]
  change (∫x,φ x*_) = 0
  have z (x:Points n):φ x*(if site R r k x=u then 1 else 0)=0:=by
    by_cases hx:φ x=0
    · simp [hx]
    · simp [none x (subset_closure hx)]
  simp [z]

end YM.Integration.WilsonCenteredSourceScale
