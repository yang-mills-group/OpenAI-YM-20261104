import YM.Integration.WilsonGraphStandaloneCorrelation
import YM.FVA2.Speed.Cells

/-! Shape regularity of the appointed group correlation at physical mass one. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonGraphSeparatedRegularity

open YangMills YangMills.Matching YM.Spec YM.OPE YM.OPE.Orbits
open YM.XSpace YM.XSpace.Normalize YM.MS YM.MS.Land YM.MS.Fleet YM.FVA2
open WilsonGraphStandaloneCorrelation
open scoped BigOperators Classical ContDiff

variable (g : YangMills.GaugeGroup)
variable (T : YM.MS.Land.MS_Data g.core (Position.OpenAxis.Plot (Press.portDeck g.core)))

include T in
theorem rawSmooth {n : ℕ} (a : Fin n → WilsonGraphStandaloneCorrelation.Label g) (k : ℕ) :
    ContDiffOn ℝ ∞ (fun x => bare g n k a x) (YM.conf n) := by
  have smooth : ContDiffOn ℝ ∞ (fun x => Dframe.meteor (Teller.logNu 1) T (cutoff a) x k
      (marks a (within a))) (YM.conf n) :=
    fun x hx => (Speed.Star.smooth_r (Teller.logNu 1) T (marks a (within a)) k x hx).contDiffWithinAt
  exact smooth.congr (fun x hx => identified a x hx k T)

include T in
theorem convertedSmooth {n : ℕ} (S : Conversion (maxwellReference g)) (k : ℕ)
    (a : Fin n → WilsonGraphStandaloneCorrelation.Label g) :
    ContDiffOn ℝ ∞ (fun x => converted S k a x) (YM.conf n) := by
  unfold converted
  apply ContDiffOn.sum
  intro ν _
  apply ContDiffOn.sum
  intro j _
  by_cases used : (∑ i, (ν i).val) + j.val ≤ k
  · simp only [if_pos used]
    exact contDiffOn_const.mul (rawSmooth g T (S.inputs a ν) j.val)
  · simp only [if_neg used]
    exact contDiffOn_const

include T in
theorem compactBound {n : ℕ} (S : Conversion (maxwellReference g)) (k : ℕ)
    (a : Fin n → WilsonGraphStandaloneCorrelation.Label g) {K : Set (YangMills.Points n)}
    (compact : IsCompact K) (safe : K ⊆ YM.conf n) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x ∈ K, ‖converted S k a x‖ ≤ D := by
  have cont := (convertedSmooth g T S k a).continuousOn.norm.mono safe
  obtain ⟨D,upper⟩ := compact.bddAbove_image cont
  exact ⟨max 0 D,le_max_left _ _,fun x hx =>
    (upper (Set.mem_image_of_mem _ hx)).trans (le_max_right _ _)⟩

end YM.Integration.WilsonGraphSeparatedRegularity
end

