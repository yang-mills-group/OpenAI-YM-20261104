import YM.Integration.WilsonIndependentConditionedLocatedCell
import YM.Integration.WilsonIndependentConditionedGramBulbProfile

/-! One genuine positive support purchase for every selected basis or quadrant
of a reflected two-field pupil on the full K-mesh. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedLocatedBulb
open Function Set Filter MeasureTheory Metric Extraction Lattice OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress
open Wilson RG Source PhysicalNext.Repeat.Legato RG17 PhysMS PhysMS.Frame WilsonCenteredPhysicalPanel
open RG12 Cells Push.GridApprox Trace.Physical.GermGraph RG16 RG16.Literal
open Maxwell XSpace XSpace.Cirrus Table.Pairing WilsonMaxwellThermometerReflectedIncidence
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Embroider
open WilsonIndependentConditionedGramBulbProfile (chart profile)
open scoped Classical Topology ContDiff
variable {a:Axis}{x:E4}(B:Bulb (site x) a)

def region:Set (Points 2):=(pairIso a (n:=1) (m:=1)).symm '' (tsupport B.bump ×ˢ tsupport B.bump)

theorem compact:IsCompact (region B):=
  (B.bump.hasCompactSupport.prod B.bump.hasCompactSupport).image (pairIso a (n:=1) (m:=1)).symm.continuous

theorem separated:region B ⊆ conf 2:=by
  rintro _ ⟨y,pair,rfl⟩
  exact spans (B.active y.1 pair.1) (B.active y.2 pair.2)

theorem represented (a:Axis)(δ:ℝ)(o:Fin 2 → Cover):
    tag δ o=(pairIso a (n:=1) (m:=1)).symm (chart a true (δ • actualW (o 0)),chart a false (δ • actualW (o 1))):=by
  apply (pairIso a (n:=1) (m:=1)).injective
  rw [ContinuousLinearEquiv.apply_symm_apply,Table.Pairing.equals,
    (WilsonIndependentConditionedGramBulbProfile.actual a _).2,(WilsonIndependentConditionedGramBulbProfile.actual a _).1]
  apply Prod.ext <;> apply PiLp.ext <;> intro i <;> have hi:i=0:=Subsingleton.elim .. <;> subst i <;> rfl

theorem located (D E:ℕ)(δ:ℝ)(o:Fin 2 → Cover)
    (shown:(profile B D true).ψ.val (δ • actualW (o 0))*(profile B E false).ψ.val (δ • actualW (o 1))≠0):
    tag δ o∈region B:=by
  rw [represented a δ o]
  apply Set.mem_image_of_mem
  exact ⟨WilsonIndependentConditionedGramBulbProfile.supported B D true
    (subset_tsupport _ (left_ne_zero_of_mul shown)),WilsonIndependentConditionedGramBulbProfile.supported B E false
    (subset_tsupport _ (right_ne_zero_of_mul shown))⟩

theorem original (G:Gauge):
    ∃φ:Test 2,∃σ:ℝ,0<σ ∧ (∀x,0≤(φ x).re) ∧ ∀(R:Run G){r:ℝ},0<r→∀(z:UVIndex)(D E:ℕ),
      let δ:=R.family.S.a z.1/r
      8*δ ≤ σ → ∀o:Fin 2 → Cover,
        (profile B D true).ψ.val (δ • actualW (o 0))*(profile B E false).ψ.val (δ • actualW (o 1))≠0 →
        WilsonCenteredCompactBooking.mass R φ r z (wrap _ ∘ o)≠0:=by
  obtain ⟨φ,σ,sp,positive,admitted⟩:=WilsonIndependentConditionedLocatedCell.original (G:=G) (compact B) (separated B)
  refine ⟨φ,σ,sp,positive,?_⟩
  intro R r rp z D E δ fits o visible
  exact admitted R rp z (by norm_num at ⊢;exact fits) o (located B D E δ o visible)

end YM.Integration.WilsonIndependentConditionedLocatedBulb
end
