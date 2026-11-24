import YM.Integration.WilsonWindowFormalPurchase
import YM.Integration.OriginalMarkedBoltKinetic
import YM.FormalBulk08.Primer.Model

/-! Read the formal-graph cover purchases on the very same family whose
signed physical cutoff is under study. Its provenance is the canonical
Bolt of this run, not an existential formal family chosen afterward. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonWindowFormalAnnouncement

open RG RG.Supply Precision Org Push.PriceCompiler
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Next.Foundations FormalBulk08

theorem on_run {G : Gauge} (R : Run G) {U : ℕ → ℕ}
    (grant : WilsonWindowFormalPurchase.Canonical U R.kit) : Primer.Announced R.family U := by
  rcases grant with ⟨fixed,coverage,radius,soil,grain⟩
  have origin : Provenance G R.family R.metals.O :=
    OriginalMarkedBoltKinetic.provenance (C := R.family) R.T rfl rfl rfl HEq.rfl
  rw [fixed] at origin
  have levels : R.family.path.levels = R.alloy.B.a := rfl
  refine ⟨R.makes,origin,?_,?_,Primer.provenance_lives origin,?_,?_⟩
  · unfold Primer.FamilyWindow Primer.Noise
    rw [origin.tie,origin.stencil,levels,R.alloy.B.valid.kernel]
    exact coverage
  · unfold Primer.FamilyWindow Primer.Noise
    rw [levels,R.alloy.B.valid.kernel]
    exact radius
  · unfold Primer.Noise
    rw [origin.tie,origin.stencil,levels,R.alloy.B.valid.kernel]
    exact soil
  · unfold Primer.Noise
    rw [origin.tie,origin.stencil,levels,R.alloy.B.valid.kernel]
    exact grain

end YM.Integration.WilsonWindowFormalAnnouncement
end

