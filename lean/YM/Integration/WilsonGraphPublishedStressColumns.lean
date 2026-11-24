import YangMills.WilsonProof.NativeSupport.ContinuumConstruction.PublishedFiledTensor
import YM.Integration.WilsonGraphAppointedStressCoordinates

/-! The four common coordinates of the stress measured on the published frame. -/
set_option autoImplicit false
noncomputable section
namespace PhysicalMatching.H7StandaloneAppointedPublicWardRows
open YM YM.Answer.ContinuumLimit Filter Maxwell Trace.Pilot
open YM.UVNext.FreeStress.PublicPanels
open YM.Integration YM.Integration.Election YM.PhysMS YM.PhysMS.Frame
open YM.FVA2 YM.FVA2.Register YM.FVA2.Scale YM.MS YM.MS.Land YM.MS.Fleet
open scoped BigOperators Classical
universe u
variable {g : YangMills.GaugeGroup} {H : g.core.Simple} {ε : ℝ} {e : YM.Axis}
  {O : OrderS g.core} {E : Construction.{u} H ε e O} {ξ : Extraction.Order}

theorem filedStressAddress (V : Vision E ξ) (Z : WilsonPrescription g.core) {lamp : Bool}
    (Q : Perspective H Z lamp) :
    ∀ᶠ r : ℝ in trail, ∃ u : Fin 4 → ℂ, ∀ a b : YM.Axis,
      Maxwell.Free.address E.paths.family.labels 4
        ((V.Post Z r 4).symm (r ^ 4 • V.pupil.last.sector.energy a b)) =
      ∑ k : Fin 4, u k • (columns H a b k).val := by
  filter_upwards [PublishedStressCoordinates.filedTensor V Z Q] with r hr
  exact signedTensorCoordinates E.paths.family.labels H V.pupil.H.spin _ hr

theorem measuredStressValue (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (r : ℝ) (a b : YM.Axis) :
    (measuredStress V Z r a b).val = Maxwell.Free.address E.paths.family.labels 4
      ((V.Post Z r 4).symm (r ^ 4 • V.pupil.last.sector.energy a b)) := by
  have scale : (r ^ 4 : ℂ) = (r ^ 4 : ℝ) • (1 : ℂ) := by
    rw [← Complex.ofReal_pow]
    exact ((Algebra.smul_def (r ^ 4 : ℝ) (1 : ℂ)).trans (mul_one _)).symm
  rw [Maxwell.Free.address_eval]
  change ((Maxwell.Free.fields E.paths.family.labels 4)
    ((V.Post Z r 4).symm ((r ^ 4 : ℂ) • V.pupil.last.sector.energy a b))).val = _
  rw [scale, smul_assoc, one_smul]

theorem measuredStressColumns (V : Vision E ξ) (Z : WilsonPrescription g.core) {lamp : Bool}
    (Q : Perspective H Z lamp) :
    ∀ᶠ r : ℝ in trail, ∃ u : Fin 4 → ℂ, ∀ a b : YM.Axis,
      measuredStress V Z r a b = ∑ k : Fin 4, u k • columns H a b k := by
  filter_upwards [filedStressAddress V Z Q] with r hr
  obtain ⟨u, hu⟩ := hr
  refine ⟨u, fun a b => Subtype.ext ?_⟩
  rw [measuredStressValue, hu]
  exact (map_sum ((YangMills.maxwellReference g).sector 4).subtype
    (fun k => u k • columns H a b k) Finset.univ).symm

end PhysicalMatching.H7StandaloneAppointedPublicWardRows

