import YM.XSpace.Grow
import YM.XSpace.Panorama
/-! Restrict the same appointed field through the genuine homogeneous inclusions. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointPivotRestriction
open XSpace XSpace.Normalize
variable {G : Gauge} {d H : ℕ}

def steps (G : Gauge) (d : ℕ) : (k : ℕ) → (Change G (d+k) →ₗ[ℝ] Change G d)
  | 0 => LinearMap.id
  | k+1 => (steps G d k).comp (fell (d+k))

theorem nested (d k : ℕ) (T : Change G (d+k)) (v : Sec G d) :
    up (Nat.le_add_right d k) ((steps G d k T).val v) = T.val (up (Nat.le_add_right d k) v) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change step (d+k) (up (Nat.le_add_right d k) ((steps G d k (fell (d+k) T)).val v)) =
      T.val (step (d+k) (up (Nat.le_add_right d k) v))
    rw [ih, fells]

def lower (h : d ≤ H) : Change G H →ₗ[ℝ] Change G d :=
  (show d+(H-d)=H by omega) ▸ steps G d (H-d)

theorem filed (h : d ≤ H) (T : Change G H) (v : Sec G d) :
    up h ((lower h T).val v) = T.val (up h v) := by
  have move (k N : ℕ) (e : d+k=N) (b : d ≤ N) (A : Change G N) :
      up b (((e ▸ steps G d k : Change G N →ₗ[ℝ] Change G d) A).val v) = A.val (up b v) := by
    subst N
    exact nested d k A v
  exact move (H-d) H (by omega) h T

theorem original (h : d ≤ H) (T : Change G H) (v : Sec G d) :
    up h (stand (lower h T) v) = stand T (up h v) := by
  change up h (v+(lower h T).val v) = up h v+T.val (up h v)
  rw [map_add, filed]

def coordinates (h : d ≤ H) : MoveSpace G H →L[ℝ] MoveSpace G d :=
  (((guide G d).toLinearMap.comp (lower h)).comp (guide G H).symm.toLinearMap).toContinuousLinearMap

theorem guided (h : d ≤ H) (T : Change G H) :
    coordinates h (guide G H T) = guide G d (lower h T) := by
  change guide G d (lower h ((guide G H).symm (guide G H T))) = _
  rw [LinearEquiv.symm_apply_apply]
end YM.Integration.WilsonPositionProgramTrialPublicJointPivotRestriction
