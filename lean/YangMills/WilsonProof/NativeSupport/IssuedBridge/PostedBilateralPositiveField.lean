import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedBilateralFieldCutoff
import YM.Integration.WilsonPositionHomogeneousRealization
set_option autoImplicit false
noncomputable section
namespace IssuedBridge.PostedBilateralPositiveField
open YM.Integration Function Filter Set Finset
open scoped Topology ContDiff Classical BigOperators
variable {E : ℕ→Type*} [∀ d,NormedAddCommGroup (E d)] [∀d,NormedSpace ℝ (E d)]
variable (a : ∀ d,ℕ→E d)


def field (d : ℕ) (t : ℝ) : E d :=
  ∑' n : ℕ, PostedBilateralFieldCutoff.weight a n t • a d n

theorem positive (d : ℕ) {t : ℝ} (ht : 0 < t) :
    field a d t = WilsonPositionGradedCutoffs.field a d t := by
  obtain ⟨N,cut⟩ := WilsonPositionGradedCutoffs.finite a ht
  have same (n : ℕ) := (PostedBilateralFieldCutoff.original a n).2 t ht.le
  unfold field
  simp_rw [same]
  rw [WilsonPositionGradedCutoffs.exactly a cut d]
  exact tsum_eq_sum fun n hn => by
    rw [cut n (by simpa only [Finset.mem_range,not_lt] using hn),zero_smul]

open YM YM.Maxwell YM.XSpace YM.XSpace.Normalize YM.MS YM.MS.Land YM.FVA2 YM.FVA2.Register YM.FVA2.Scale
theorem original {G : Gauge} (Z : WilsonPrescription G) (d : ℕ) {t : ℝ} (ht : 0 < t) :
    (guide G d).symm (field (WilsonPositionHomogeneousCoefficients.dossier Z) d t) =
      WilsonPositionHomogeneousRealization.correction Z d t := by
  rw [positive _ d ht]
  rfl
end IssuedBridge.PostedBilateralPositiveField
