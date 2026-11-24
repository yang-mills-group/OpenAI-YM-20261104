import YM.Integration.WilsonOriginalCoveredPlainStep
/-! A paid whole input at its first retained order determines the next finite forest
contraction.  Every old proper or full marked coefficient is read on the same quiet. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonOriginalRetainedForest
open Function Filter Finset Lattice RG Precision Tree YM.Wilson QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Sunrise Comparison Comparison.RG02 Comparison.RG02.Bulk Comparison.RG02.Assembly
open Exterior Next.SectorChange Marker Multi FVA1Physical.TwoReset
open scoped Classical ContDiff BigOperators
open private plain from YM.Integration.WilsonOriginalCoveredPlainStep


variable {G:Gauge}{V:Type}[DecidableEq V][Fintype V]{W:Census V}
  {f c:Side}{B:StepData c f}{P:Clip}{Y:PathData G}{O:ChartRatio G}
  (K:Kernel B P Y O)(F:Forest B.ratio)(tag:B.Choices)(r:ℕ)(grades:V → ℕ)
  (old:Colors W G f)(head:Multi.Hot W → ℕ → fieldDir G f 1 → ℂ)

theorem original (power:∀s,old.power s=Launch.index W grades s.val+1)
    (regular:∀s,GradeAt (old.power s) (Bulk.projected (old.mark s)))
    (registered:∀s j,j≤r → ∀z,(Air.discharge old j z).part s.val=head s j z)(x:fieldDir G c 1):
    Bulk.Fk K F tag old x r =
      Bulk.Fk K F tag (WilsonOriginalCoverJetColors.colors old.vac (fun s=>Launch.index W grades s.val+1) r head) x r:=by
  let powers:=fun s:Multi.Hot W=>Launch.index W grades s.val+1
  let bank:=WilsonOriginalCoverJetColors.colors old.vac powers r head
  have full:=WilsonOriginalCoveredJoinWick.finite K F tag r Finset.univ ∅ (Finset.disjoint_empty_right _)
    grades old old old.vac powers head rfl (funext power) (fun _ _=>rfl) regular registered x
  rw [plain grades old old power,plain grades bank old (fun _=>rfl)] at full
  exact full

end YM.Integration.WilsonOriginalRetainedForest
