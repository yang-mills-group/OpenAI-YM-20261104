import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedTriangleCutReturns
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedSubmittedTriangleSlope
noncomputable section
namespace IssuedBridge.PostedEveryBareSlope
open Set MeasureTheory YM YM.XSpace YangMills.MSbar
open scoped Topology
variable {g : YangMills.GaugeGroup}
local notation "B₀" => IssuedMaxwell.Reference.issued g
local notation "GC" => IssuedMaxwell.GraphCoefficients.issued g

theorem price (t : Position.Triangle B₀) (ht : t.Admissible) (e : Shade.Cut)
    (he : e.rOut ≤ t.cut.rOut) :
    ({t with cut := e} : Position.Triangle B₀).cT = t.cT := by
  unfold Position.Triangle.cT
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ tsupport t.profile
  · have large : x ∈ Photo.Good t.cut 3 := fun i j hij =>
      (le_max_right 4 _).trans_lt (ht.separated x hx i j hij)
    have small : x ∈ Photo.Good e 3 := fun i j hij =>
      (mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 5)).trans_lt (large i j hij)
    rw [PostedTriangleCutReturns.original g e t.cut x small large]
  · have hz : t.profile x = 0 := by
      by_contra h
      exact hx (subset_closure (show x ∈ Function.support t.profile from h))
    simp [hz]

theorem original (h : g.IsSimple) (t : Position.Triangle B₀) (ht : t.Admissible) :
    t.RawSlopeAgrees GC := by
  let prior := IssuedMaxwell.ElectedPrescription.prior g h
  let P₀ := prior.val
  have h₀ : Admissible P₀ := prior.property
  let r := min t.cut.rOut P₀.triangle.cut.rOut
  have hr : 0 < r := lt_min t.cut.rOut_pos P₀.triangle.cut.rOut_pos
  let e : Shade.Cut := ⟨r/2, r, half_pos hr, half_lt_self hr⟩
  have et : e.rOut ≤ t.cut.rOut := min_le_left _ _
  have es : e.rOut ≤ P₀.triangle.cut.rOut := min_le_right _ _
  let u : Position.Triangle B₀ := {t with cut := e}
  have cost : u.cT = t.cT := price t ht e et
  have hu : u.Admissible := by
    refine ⟨ht.nonnegative, ht.realValue, ht.turns, ?_, ?_⟩
    · intro x hx i j hij
      exact (max_le_max_left 4 (mul_le_mul_of_nonneg_left et (by norm_num : (0 : ℝ) ≤ 5))).trans_lt
        (ht.separated x hx i j hij)
    · rw [cost]
      exact ht.negative
  let P : PositionPrescription B₀ := ⟨P₀.screen, u⟩
  have hp : Admissible P := by
    refine ⟨h₀.toPrepared, hu, ?_⟩
    intro i w x hx a b hab
    exact (mul_le_mul_of_nonneg_left es (by norm_num : (0 : ℝ) ≤ 5)).trans_lt
      (h₀.screenClearance i x hx a b hab)
  have earned := PostedSubmittedTriangleSlope.original h P hp
  change (∫ x, t.profile x * t.firstConnected GC x) = (u.cT : ℂ) at earned
  rw [cost] at earned
  exact earned
end IssuedBridge.PostedEveryBareSlope
