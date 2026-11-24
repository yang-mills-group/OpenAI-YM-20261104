import YM.Integration.WilsonMatrixTicketLanesReportedQuadrature
import YM.Integration.WilsonInvariantActionPromotedPair

/-! The uniform finite-torus bill of the reported mesh is the literal
quadrature of the two submitted physical fields on every period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalGermTestQuadrature
open Lattice Wilson RG FVA2 OPE PhysicalNext.Repeat.Legato Extraction XSpace Next.UVStress RG17 FullVolume Table Climb Trace.Pilot
open WilsonMatrixTicketLanesReportedQuadrature
open scoped BigOperators Classical
variable {G:Gauge} (R:Run G) {n:ℕ}

theorem position {r:ℝ} (hr:0 < r) (N p:ℕ) (x:Var R.family.S n N p):
    (mesh R N p r hr).rel ((mesh R N p r hr).back x) 0=r⁻¹ • Order.cells R.family N p x:=by
  apply PiLp.ext;intro i
  apply PiLp.ext;intro j
  change (R.family.S.a N/r)*((lift (x i) j:ℤ):ℝ)-(0:ℝ)=r⁻¹*(R.family.S.a N*((lift (x i) j:ℤ):ℝ))
  ring

theorem field (φ:Test n) {r:ℝ} (hr:0 < r) (N p:ℕ) (x:Var R.family.S n N p):
    WilsonExternalMeshMass.charge R.family (dilate hr φ) x=WilsonMatrixTicketLanesReportedQuadrature.weight (mesh R N p r hr) φ 0 x:=by
  unfold WilsonMatrixTicketLanesReportedQuadrature.weight
  rw [position R hr N p x]
  change (R.family.S.a N:ℂ)^(4*n)*((((r^(4*n))⁻¹:ℝ):ℂ)*φ (r⁻¹ • Order.cells R.family N p x))=
    ((R.family.S.a N/r:ℝ):ℂ)^(4*n)*φ (r⁻¹ • Order.cells R.family N p x)
  push_cast;rw [div_pow,div_eq_mul_inv];ring

theorem uniform (φ:Test n):∃B:ℝ,0 ≤ B ∧ ∀(r:ℝ) (hr:0 < r) (N p:ℕ),R.family.S.a N ≤ r →
    (∑x:Var R.family.S n N p,‖WilsonExternalMeshMass.charge R.family (dilate hr φ) x‖) ≤ B:=by
  obtain ⟨B,b,all⟩:=mass φ
  refine ⟨B,b,?_⟩
  intro r hr N p small
  simp_rw [field R φ hr N p]
  exact all (mesh R N p r hr) ((div_le_one hr).2 small) 0

end YM.Integration.WilsonMatrixOriginalGermTestQuadrature
