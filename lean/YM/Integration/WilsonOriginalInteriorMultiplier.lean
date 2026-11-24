import YM.Integration.WilsonOriginalSpatialProductRule
import YM.Integration.WilsonOriginalFourierReadback

/-! On a compact interior, multiplication by a fixed smooth function preserves
the uniform little-o estimate for every ordered spatial derivative. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalInteriorMultiplier
open Filter Set Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 Trace.Pilot PhysMS Climb
open WilsonOriginalSupportedBoxChart (Space)
open WilsonOriginalSpatialProductRule (word step Regular)
open scoped Topology ContDiff

def Priced {d : ℕ} (K : Set (Space d)) (rate : ℝ → ℝ) (f : ℝ → Space d → ℂ) :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ r in trail, ∀ x ∈ K, ‖f r x‖ ≤ ε*rate r

theorem original {d : ℕ} (s : List (Fin d)) {K O : Set (Space d)} (compact : IsCompact K)
    (closedIn : K ⊆ O) (room : IsOpen O) (rate : ℝ → ℝ)
    (g : Space d → ℂ) (sg : Regular O g) (f : ℝ → Space d → ℂ)
    (sf : ∀ᶠ r in trail, Regular O (f r))
    (small : ∀ w : List (Fin d), Priced K rate (fun r => word w (f r))) :
    Priced K rate (fun r => word s (fun x => g x*f r x)) := by
  induction s generalizing g f with
  | nil =>
    obtain ⟨C,bound⟩ := compact.exists_bound_of_continuousOn
      (show ContinuousOn g K from fun x hx => (sg x (closedIn hx)).continuousAt.continuousWithinAt)
    let B := max 1 C
    have positive : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
    intro ε eps
    filter_upwards [small [] (ε/B) (div_pos eps positive)] with r got x hx
    change ‖g x*f r x‖ ≤ _
    rw [norm_mul]
    calc
      ‖g x‖*‖f r x‖ ≤ B*((ε/B)*rate r) := mul_le_mul
        ((bound x hx).trans (le_max_right _ _)) (got x hx) (norm_nonneg _) positive.le
      _ = ε*rate r := by field_simp
  | cons i s ih =>
    have first := ih (step i g) (WilsonOriginalSpatialProductRule.regular_step sg i) f sf small
    have next : ∀ᶠ r in trail, Regular O (step i (f r)) :=
      sf.mono fun r hr => WilsonOriginalSpatialProductRule.regular_step hr i
    have second := ih g sg (fun r => step i (f r)) next (fun w => small (i::w))
    intro ε eps
    filter_upwards [first (ε/2) (half_pos eps),second (ε/2) (half_pos eps),sf]
      with r one two regular x hx
    rw [WilsonOriginalSpatialProductRule.original s i room sg regular (closedIn hx)]
    exact (norm_add_le ..).trans ((add_le_add (one x hx) (two x hx)).trans_eq (by ring))

end YM.Integration.WilsonOriginalInteriorMultiplier
