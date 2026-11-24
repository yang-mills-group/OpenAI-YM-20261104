import YM.Integration.WilsonOriginalStableCoverInput
import YM.Integration.WilsonOriginalCoverJetColors
import YM.Integration.WilsonOriginalJoinedCopyBank

/-! Replacing a deposited source by its independently computed angular germ inside the entire next finite log. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonOriginalCoveredJoinWick
open Function Filter Finset Lattice RG Precision Tree YM.Wilson QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Sunrise Comparison Comparison.RG02 Comparison.RG02.Bulk Comparison.RG02.Assembly
open Exterior Next.SectorChange Marker Multi FVA1Physical.TwoReset
open scoped Classical ContDiff BigOperators
open private field_step from YM.Integration.WilsonOriginalStableCoverInput

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {W : Census V}
  {f c : Side} {B : StepData c f} {P : Clip} {Y : PathData G} {O : ChartRatio G}
  (K : Kernel B P Y O) (F : Forest B.ratio) (tag : B.Choices)
  (p : ℕ) (left fresh : Finset V) (apart : Disjoint left fresh) (grades : V → ℕ)
  (old new : Colors W G f) (quiet : ℝ → Config G f → ℝ) (powers : Multi.Hot W → ℕ)
  (head : Multi.Hot W → ℕ → fieldDir G f 1 → ℂ)

local notation "canonical" => WilsonOriginalCoverJetColors.colors quiet powers p head
local notation "joined" => WilsonOriginalJoinedCopyBank.joined left fresh grades

include apart in
/-- The independently reconstructed old source gives the same complete contraction even with a fresh source attached. -/
theorem finite (vac : old.vac = quiet) (hpow : old.power = powers)
    (oldGrades : ∀ s : Multi.Hot W, s.val.val ⊆ left → Launch.index W grades s.val+1 = powers s)
    (regular : ∀ s, GradeAt (old.power s) (Bulk.projected (old.mark s)))
    (registered : ∀ s j, j≤p → ∀ z, (Air.discharge old j z).part s.val = head s j z)
    (x : fieldDir G c 1) : Bulk.Fk K F tag (joined old new) x p = Bulk.Fk K F tag (joined canonical new) x p := by
  have bounds (s : Multi.Hot W) (j : ℕ) (hj : j≤p) :
      Valence.Level ((powers s+j:ℕ):ℤ) (head s j) := by
    rw [← funext (registered s j hj), ← hpow]
    exact WilsonOriginalCoverJetColors.occupied_degree old regular s j
  have conform : ∀ j≤p, ∀ v, Air.discharge old j (Stationary.arm G f 1 v) =
      Air.discharge canonical j (Stationary.arm G f 1 v) := by
    intro j hj v
    rw [WilsonOriginalCoverJetColors.angular quiet powers p head bounds j hj]
    apply congrArg (lit W)
    funext s
    simpa only [Air.discharge, part_lit] using registered s j hj (Stationary.arm G f 1 v)
  apply same_prescription K F tag (joined old new) (joined canonical new) p _ _ x
  · intro j _ z
    rcases old with ⟨u,h,k⟩
    change u = quiet at vac
    subst u
    rfl
  · intro s j hj z
    by_cases active : s.val.val ⊆ left
    · have miss : ¬s.val.val ⊆ fresh := by
        obtain ⟨v,hv⟩ := s.prop
        exact fun cover => Finset.disjoint_left.mp apart (active hv) (cover hv)
      have driver := field_step F old canonical p hpow regular
        (WilsonOriginalCoverJetColors.grade quiet powers p head bounds) conform s j hj z
      simpa only [markLetter, markFn, WilsonOriginalJoinedCopyBank.joined, if_pos active, if_neg miss,
        add_zero, oldGrades s active, hpow, WilsonOriginalCoverJetColors.colors] using driver
    · simp only [markLetter, markFn, WilsonOriginalJoinedCopyBank.joined, if_neg active, zero_add]

end YM.Integration.WilsonOriginalCoveredJoinWick
