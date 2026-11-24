import YM.Integration.WilsonThermometerUnitFilingCylinder
import YM.Integration.WilsonRenderedScalarReturn

/-! The physical three-field test with its frozen independent face inverse
on the actual finite Wilson law and its successive conditional integrals. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerOriginalScalarTelescope
open Filter MeasureTheory Finset Lattice Wilson RG Source Labels Table Spec XSpace XSpace.Rose
open Extraction Climb Next.UVStress RG12 RG17 PhysicalNext.Repeat.Legato
open RG16 Trace.Physical.GermGraph OPE.Therm Marker
open WilsonPositionThermometerCapStation WilsonThermometerUnitFilingCylinder
open Primitives.GCC.Anchor
open scoped BigOperators Topology Classical
variable {G : Gauge} (R : Run G) (A : Group R.family 6) (z : UVIndex)
    (r : ℝ) (φ : Test 3) (Q : Sites R z → Poly (Stock.census (Fin 3)))
local notation "X" j:max => Config G (R.family.side j z.2)
local notation "μ" j:max => scene R.family.path z.1 z.2 j

theorem original {u b : ℕ} (stop : u ≤ b) (top : b ≤ z.1) (rows : ∀ j, X j → ℂ)
    (enrolled : ∀ j, u ≤ j → j ≤ b → Envelope (rows j)) (c : ℂ) :
    let Y := cylinder R A z r φ Q
    let full := actualTransport R.family (N:=z.1) Y top
    tested R A z r φ Q - c =
      (∫ U, full U - rows b U ∂μ b) -
        (∑ j ∈ Ico u b, ∫ U, rows j U - actualAverage R.family (N:=z.1) (rows (j+1)) U ∂μ j) +
          ((∫ U, rows u U ∂μ u) - c) := by
  intro Y full
  have cont : Continuous Y := continuous_cylinder R A z r φ Q
  have initial : Integrable (fun U => (R.family.path.rep z.1 z.2 z.1).eval U • Y U) (prior G _) := by
    simpa only [Complex.real_smul] using RG05Readout.Harvest.dye_grow («C»:=R.family) R.makes cont
  have physical := actualScene_transport R.family R.makes (le_refl z.1) initial top
  have topLaw : μ z.1 = law G (R.family.side z.1 z.2) (R.family.beta z.1 z.2) := by
    have originalLaw : R.family.Makes := R.makes
    unfold scene law dose Wilson.weight
    rw [(originalLaw.wilson.starts z.1 z.2).2]
  have read : (∫ U, full U ∂μ b) = tested R A z r φ Q := by
    rw [physical,topLaw]
    exact literal R A z r φ Q
  rw [← read]
  exact WilsonRenderedScalarReturn.telescope R.family R.makes stop top rows enrolled full
    (actualTransport_weighted_integrable_of_integrable R.family R.makes (le_refl z.1) initial top) c

theorem bound {u b : ℕ} (stop : u ≤ b) (top : b ≤ z.1) (rows : ∀ j, X j → ℂ)
    (enrolled : ∀ j, u ≤ j → j ≤ b → Envelope (rows j)) (c : ℂ) :
    let full := actualTransport R.family (N:=z.1) (cylinder R A z r φ Q) top
    ‖tested R A z r φ Q - c‖ ≤
      ‖∫ U, full U - rows b U ∂μ b‖ +
        (∑ j ∈ Ico u b, ‖∫ U, rows j U - actualAverage R.family (N:=z.1) (rows (j+1)) U ∂μ j‖) +
          ‖(∫ U, rows u U ∂μ u) - c‖ := by
  intro full
  rw [original R A z r φ Q stop top rows enrolled c]
  exact (norm_add_le ..).trans <| add_le_add
    ((norm_sub_le ..).trans (add_le_add le_rfl (norm_sum_le ..))) le_rfl

end YM.Integration.WilsonThermometerOriginalScalarTelescope
