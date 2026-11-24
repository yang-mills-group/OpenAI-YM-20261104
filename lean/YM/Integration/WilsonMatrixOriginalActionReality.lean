import YM.Integration.WilsonMatrixOriginalRealFields

/-! The centered physical Ward insertion is represented by the real part of its filed label. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalActionReality
open Filter Function Table Spec Climb Spin Trace.Pilot Trace.Over TraceExtension PhysMS
open Next.UVStress PhysicalNext.Repeat.Legato WilsonMatrixOriginalRealFields
open scoped Classical Topology
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ → tower S)

theorem projected (a : R.family.label 4) :
    S.project 4 (realLabel a) =
      (2 : ℂ)⁻¹ • (S.project 4 a + S.conj F.room.kernel.spin 4 (S.project 4 a)) := by
  rw [realLabel,map_smul,map_add,S.conj_project]

theorem trace : S.conj F.room.kernel.spin 4 (centering S 4 (center F)) =
    centering S 4 (center F) := by
  have same : centering S 4 (center F) = centering S 4 (lum F) := by
    change centering S 4 (stressTrace F.sector.energy - _ • S.unit 4) =
      centering S 4 (stressTrace F.sector.energy - _ • S.unit 4)
    simp only [map_sub,map_smul,const_out F.room.kernel.laws,smul_zero,sub_zero]
  rw [same,conj_center F.room.kernel,lum_real F]

theorem ward (simple : G.Simple) {P : ℝ → change S 4} {δ g : ℝ → ℝ}
    (same : ∀ᶠ r in trail, J r 4 = P r) (cal : TendC F P δ) (coupling : Coupling G g) :
    ∀ᶠ r in trail,
      centering S 4 (S.project 4 (realLabel (R:=R) (S.representative 4 (J r 4 (stepField R.family))))) =
        centering S 4 (J r 4 (stepField R.family)) := by
  obtain ⟨c,value⟩ := WilsonInvariantActionOnePoint.resolved F J simple same cal coupling
  filter_upwards [value] with r hr
  let y := J r 4 (stepField R.family)
  have fixed : S.conj F.room.kernel.spin 4 (centering S 4 y) = centering S 4 y := by
    have central : centering S 4 y =
        ((r^4/(4*δ r):ℝ):ℂ) • centering S 4 (center F) := by
      dsimp only [y]
      rw [hr,show (r^4/(4*δ r):ℝ) • (center F-c • S.unit 4) =
          ((r^4/(4*δ r):ℝ):ℂ) • (center F-c • S.unit 4) from Complex.coe_smul ..,
        map_smul,map_sub,map_smul,const_out F.room.kernel.laws,smul_zero,sub_zero]
    rw [central,map_smulₛₗ,trace F]
    rw [Complex.conj_ofReal]
  change centering S 4 (S.project 4 (realLabel (R:=R) (S.representative 4 y))) = centering S 4 y
  rw [projected F,S.rep,map_smul,map_add,←conj_center F.room.kernel,fixed,←two_smul ℂ,smul_smul]
  norm_num

end YM.Integration.WilsonMatrixOriginalActionReality
