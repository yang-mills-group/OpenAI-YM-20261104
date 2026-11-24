import YM.Integration.WilsonSurveyedColorScore

/-! The true same-vacuum promoted measurements form the marked album with the
finite, order-dependent coordinates computed from the nominated MS sections. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorMeasuredAlbum
open Function Finset Set Real Maxwell XSpace XSpace.Normalize
open PowerSeries MS MS.Plane MS.High MS.LogTime MS.Latch MS.Land MS.Rake MS.Rake.Geo MS.Theater MS.Book.Program
open FVA2 FVA2.Extras FVA2.O FVA2.O.Score FVA2.Position.OpenAxis FVA2.Scale FVA2.Scale.Equator
open WilsonSurveyedColorNominated WilsonSurveyedColorCurvature
open WilsonSurveyedColorScore WilsonSurveyedColorNamedTour
open scoped Classical BigOperators
variable {G : Gauge} [PreconnectedSpace G.El] (hG : G.Simple)
variable (U : G.Color ≃ₗᵢ[ℝ] G.Color) (same : Preserves U)
variable (M : MS_Data G (Plot (Press.portDeck G))) (a : ℝ)
variable {n : ℕ} (x : Points n) (p : Scan G n)

def points (x : Points n) : Rake.Position (Fin n) Unit := fun i _ => Theater.out (x i)

theorem separated (hx : x ∈ conf n) : Mesh (Tide.frameF Unit a) (points x) := by
  intro i j h
  have pos : 0 < ‖points x i () - points x j ()‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr ((Theater.out.injective.comp hx).ne h))
  refine ⟨⟨_, pos, fun _ => ?_⟩, ⟨_, pos, fun _ => ?_⟩⟩ <;>
    rw [roots, show ∀ i, (Tide.frameF Unit a).θ i = (0 : ℝ) from fun _ => rfl, exp_zero, mul_one] <;>
    exact le_rfl

local notation "T₀" => change hG U same M a
local notation "A₀" => install (wave a M)

theorem expansion (hx : x ∈ conf n) (l : List (Fin n)) (hn : l.Nodup) (v : LivesP p) (k : ℕ) :
    toured hG U same M a (points x) p univ l (decode p v) k =
      coeff k (selected T₀ p (A₀ n x) l.toFinset v) := by
  induction l generalizing v k with
  | nil => rw [toured,List.toFinset_nil,WilsonSurveyedColorScore.empty,stock a M _ hx]; rfl
  | cons i l ih =>
    have hi := List.nodup_cons.mp hn
    rw [toured,List.toFinset_cons,WilsonSurveyedColorScore.add _ _ _ _ _ i (by simpa using hi.1),map_sum]
    apply sum_congr rfl
    intro z _
    rw [coeff_mul,Nat.sum_antidiagonal_eq_sum_range_succ
      (f := fun r s => coeff r (T₀ (p i).h (p i).item z) *
        coeff s (selected T₀ p (A₀ n x) l.toFinset (update v i z)))]
    apply sum_congr rfl
    intro j _
    simp only [change,coeff_mk]
    congr 1
    have e : update (decode p v) i (own z) = decode p (update v i z) := by
      funext w
      by_cases hw : w = i
      · subst w; simp [decode]
      · simp [decode,update_of_ne hw]
    rw [e]
    exact ih hi.2 _ _

def measured : Album G := fun n x p =>
  if x ∈ conf n then PowerSeries.mk (Extras.service a M
    (fun i => O.Lives.letIn (p i).h (logMass a) (field hG U same M a (p i)).inserted)
    (points x) univ) else 0

theorem rows : measured hG U same M a = marking T₀ A₀ := by
  funext n x p
  by_cases hx : x ∈ conf n
  · ext k
    simp only [measured,if_pos hx,coeff_mk]
    let v : LivesP p := fun i => (p i).item
    let l : List (Fin n) := univ.toList
    have hp : placed hG U same M a p l (decode p v) =
        fun i => O.Lives.letIn (p i).h (logMass a) (field hG U same M a (p i)).inserted := by
      funext i
      simp [placed,l]
    rw [← hp, WilsonSurveyedColorNamedTour.measured hG U same M a (points x) p univ
      (separated a x hx) l (nodup_toList _) (fun i _ => mem_univ i),
      expansion hG U same M a x p hx l (nodup_toList _)]
    simpa [l,marking] using congrArg (coeff k) (WilsonSurveyedColorScore.complete T₀ p (A₀ n x) v)
  · simp [measured,hx,marking,concert,install]

end YM.Integration.WilsonSurveyedColorMeasuredAlbum
end
