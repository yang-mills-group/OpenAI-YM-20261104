import YM.Integration.WilsonMacroscopicRichActualFourierProgram
import YM.Integration.WilsonMacroscopicRichFlatPosteriorLaw

/-! Linear evaluation in one actual cell under an arbitrary joint law and an integrable signed spectator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichCorrelatedTest
open Function MeasureTheory Lattice Wilson RG Source Extraction Push.GridApprox OPE OPE.Therm PhysicalNext.Repeat.Legato
open scoped Topology

variable {X Ω:Type*} [MeasurableSpace Ω] [TopologicalSpace X] [MeasurableSpace X]
  [BorelSpace X] [CompactSpace X] (μ:Measure Ω) (cell:Ω→X) (placed:Measurable cell)
  (Ψ:Ω→ℂ) (paid:Integrable Ψ μ)

include paid placed in
theorem mixed (Y:C(X,ℂ)):Integrable (fun U=>Ψ U*Y (cell U)) μ:=
  paid.mul_bdd (Y.continuous.measurable.comp placed).aestronglyMeasurable
    (ae_of_all μ fun U=>ContinuousMap.norm_coe_le_norm Y (cell U))

include paid placed in
def meter:C(X,ℂ)→ₗ[ℂ]ℂ where
  toFun Y:=∫U,Ψ U*Y (cell U) ∂μ
  map_add' f g:=by
    simp only [ContinuousMap.add_apply,mul_add]
    exact integral_add (mixed μ cell placed Ψ paid f) (mixed μ cell placed Ψ paid g)
  map_smul' c f:=by
    simp only [ContinuousMap.smul_apply,smul_eq_mul,RingHom.id_apply]
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all μ fun U=>by ring)

theorem physical {G:Gauge} (R:Run G) {u N per:ℕ} (cut:u+1≤N)
    (V:Config G (R.family.side u per)) (H:Config G (R.family.side N per)→ℂ)
    (fine:Integrable H (scene R.family.path N per N))
    (held:Integrable H (WilsonMacroscopicRichFlatPosteriorLaw.law R N per cut V))
    (Y:C(Config G (R.family.side N per),ℂ)):
    meter (WilsonMacroscopicRichFlatPosteriorLaw.law R N per cut V) id measurable_id H held Y=
      WilsonMacroscopicForwardTransfer.exterior (C:=R.family) (N:=N) ((Nat.le_succ u).trans cut)
        (fun U=>H U*Y U) V:=by
  have mixedFine:=mixed (scene R.family.path N per N) id measurable_id H fine Y
  exact (WilsonMacroscopicRichFlatPosteriorLaw.reading R cut le_rfl V _ mixedFine).symm

end YM.Integration.WilsonMacroscopicRichCorrelatedTest
