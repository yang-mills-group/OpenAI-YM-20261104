import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedBilateralSmoothField
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedAppointedFieldBank
import YM.Integration.WilsonPositionHomogeneousNear
set_option autoImplicit false
noncomputable section
namespace IssuedBridge.PostedBilateralAdjustment
open YangMills YangMills.Wilson YM YM.Integration YM.Maxwell YM.Maxwell.Free WilsonLimitConstruction
open XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale WilsonPositionHomogeneousCoefficients
open scoped Topology ContDiff BigOperators Classical
open Function Filter Set
variable {g : GaugeGroup} (Z : WilsonPrescription g.core)

def limb (d : ℕ) (t : ℝ) : Change g.core d :=
  (guide g.core d).symm (PostedBilateralPositiveField.field (dossier Z) d t)
def value (d : ℕ) (t : ℝ) : Module.End ℂ ((maxwellReference g).sector d) := stand (limb Z d t)

theorem positive (d : ℕ) {t : ℝ} (ht : 0 < t) :
    limb Z d t = WilsonPositionHomogeneousRealization.correction Z d t :=
  PostedBilateralPositiveField.original Z d ht

theorem zero (d : ℕ) : value Z d 0 = LinearMap.id := by
  have zeroField : PostedBilateralPositiveField.field (dossier Z) d 0 = 0 := by
    unfold PostedBilateralPositiveField.field
    have hz (n : ℕ) : PostedBilateralFieldCutoff.weight (dossier Z) n 0 • dossier Z d n = 0 := by
      rcases eq_or_ne n 0 with rfl | hn
      · simp [dossier,WilsonPositionHomogeneousCoefficients.letter]
      · rw [(PostedBilateralFieldCutoff.original _ n).2 0 le_rfl]
        change (Real.smoothTransition _ * (0:ℝ)^n) • _ = 0
        rw [zero_pow hn,mul_zero,zero_smul]
    simp only [hz,tsum_zero]
  rw [value,limb,zeroField,map_zero,stand0]
  rfl

theorem original (d : ℕ) (v : (maxwellReference g).sector d) (out : (maxwellReference g).sector d →ₗ[ℂ] ℂ) :
    ContDiffAt ℝ ∞ (fun t => out (value Z d t v)) 0 := by
  let eval : MoveSpace g.core d →ₗ[ℝ] (maxwellReference g).sector d :=
    { toFun x := ((guide g.core d).symm x).val v
      map_add' := by intro a b; rw [map_add]; rfl
      map_smul' := by intro a b; rw [map_smul]; rfl }
  let read := (out.restrictScalars ℝ).comp eval
  have h := (read.toContinuousLinearMap.contDiff.comp (PostedBilateralSmoothField.original (dossier Z) d))
  have sum := (contDiff_const (c:=out v)).add h
  convert sum.contDiffAt using 1
  ext t
  exact map_add out v ((limb Z d t).val v)
end IssuedBridge.PostedBilateralAdjustment
