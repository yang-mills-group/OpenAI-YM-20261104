import YM.Integration.WilsonReportingMeasuredWardFees
import YM.Integration.WilsonReportingPrescribedOldScale

/-! The genuine finite curvature fee matrix before all fields, cutoffs and periods. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingMeasuredWardFeePrice
open Filter Function Finset Wilson Precision Source PhysicalNext.Repeat.Legato
open MS.Land MS.Menus MS.Local.Physical MS.Theater
open WilsonReportingPrescribedOldFreeArms WilsonMatrixOriginalCurvatureStock
open WilsonReportingMeasuredWardFees
open scoped Classical BigOperators
variable {G:Gauge} {B:Deck G} (Q:Prescription B)
local notation "I" => B.BIndex (4:ℤ) 2

theorem tree (clock:ℝ) (i j:I):matrix Q clock 0 i j=if j=i then 1 else 0 := by
  have h:=WilsonReportingPrescribedOldAction.upper B Q i clock (curvature B j) (le_refl 2)
  change matrix Q clock 0 i j=(if curvature B j=curvature B i then 1 else 0) at h
  rw [h]
  by_cases equal:j=i
  · simp [equal]
  · have different:curvature B j≠curvature B i := by
      intro e
      exact equal (by simpa [curvature] using e)
    simp [equal,different]

theorem before (K:ℕ) (μ:ℝ): ∃C:ℝ,0<C ∧ ∃d:ℕ,∀ t:ℝ,∀k≤K,∀z:Stock B,
    (∑j:I,‖(projected Q (μ-t) k z).2 j‖)≤C*(1+‖t‖)^d*(∑i:I,‖z.2 i‖) := by
  obtain ⟨C,hC,d,fees⟩:=ActualOriginalFeeGrowth.shifted_bound B Q (WilsonReportingPrescribedOldAction.label B) K μ
  refine ⟨((Fintype.card I:ℝ)+1)*C,by positivity,d,?_⟩
  intro t k hk z
  let A:=C*(1+‖t‖)^d
  have row (j:I): ‖(projected Q (μ-t) k z).2 j‖≤A*(∑i:I,‖z.2 i‖) := by
    calc
      _ ≤ ∑i:I,‖z.2 i*matrix Q (μ-t) k i j‖:=norm_sum_le .. 
      _ ≤ ∑i:I,‖z.2 i‖*A:=sum_le_sum fun i _=>by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (fees i k hk (curvature B j) t) (norm_nonneg _)
      _ = _ :=by rw [←sum_mul,mul_comm]
  calc
    _ ≤ ∑_j:I,A*(∑i:I,‖z.2 i‖):=sum_le_sum fun j _=>row j
    _ = Fintype.card I*(A*(∑i:I,‖z.2 i‖)):=by simp
    _ ≤ ((Fintype.card I:ℝ)+1)*(A*(∑i:I,‖z.2 i‖)):=by
      apply mul_le_mul_of_nonneg_right (by linarith)
      dsimp only [A]
      positivity
    _ = _:=by dsimp only [A];ring

theorem physical (R:Run G) (simple:G.Simple) (K:ℕ) (μ:ℝ) :
    ∃C:ℝ,0<C ∧ ∃d:ℕ,∀ᶠ j:ℕ in atTop,∀{m t:ℕ},j≤t→WilsonReportHarvestUpperRange.eligible R.family.S m j t→
      ∀k≤K,∀z:Stock B,(∑i,‖(projected Q (μ-R.family.S.scale (t+1)) k z).2 i‖)≤
        C*(R.family.path.levels.clock.hatBeta j)^d*(∑i,‖z.2 i‖) := by
  obtain ⟨c,hc,d,fees⟩:=before Q K μ
  obtain ⟨a,ha,clock⟩:=WilsonReportingPrescribedOldScale.clock R simple
  refine ⟨c*a^d,by positivity,d,?_⟩
  filter_upwards [clock] with j earned
  intro m t jt member k hk z
  have scale:=earned jt member
  calc
    _ ≤ c*(1+‖R.family.S.scale (t+1)‖)^d*(∑i,‖z.2 i‖):=fees _ _ hk z
    _ ≤ c*(a*R.family.path.levels.clock.hatBeta j)^d*(∑i,‖z.2 i‖):=by
      apply mul_le_mul_of_nonneg_right _ (sum_nonneg fun i _=>norm_nonneg _)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) scale d) hc.le
    _ = _:=by rw [mul_pow];ring

end YM.Integration.WilsonReportingMeasuredWardFeePrice
