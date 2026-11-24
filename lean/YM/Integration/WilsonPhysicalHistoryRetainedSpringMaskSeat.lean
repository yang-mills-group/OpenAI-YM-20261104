import YM.Integration.WilsonPhysicalHistoryRetainedSpringMaskSeries
import YM.Integration.WilsonVacuumPreResetLiftedPiece

/-! The true registered support and value of every earlier rank-two or higher
period entry at one fixed signed seat. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.OriginalMarkedRunAction
open Extra.Iteration Function Finset MeasureTheory Lattice Wilson RG StressFlux
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open Comparison.Density Comparison.Density.Render AnalyticBridge.VerifiedReset AnalyticBridge.VerifiedReset.Collection
open IterationFour.Vacuum WilsonVacuumPreResetLiftedPiece Next.Scheduling
open scoped Classical Topology BigOperators
variable {G : Gauge} {n : Side}

def maskedSeat (Q : Payload G n) (θ : ℝ) (v : Seat n) (U : Config G n) : ℝ :=
  ∑' i:ℕ, let l:=(numbering (Cycle n)).symm (v,i)
          masked θ (Q.labels l).support (Q.action l) U

theorem seat_inside (a : PrismA G) (B : BudgetPoint) (σ C θ : ℝ) (v : Seat n) (U : Config G n) :
    let F:=frame n a Frame.full
    maskedSeat (FundedCorrectedPeriod.piece n B σ C a).packet θ v U =
      ∑' i,masked θ (F.footprint i) (F.dataF i) (v.view U) := by
  intro F
  rw [←WilsonVacuumPreResetLiftedPiece.whole]
  apply tsum_congr
  intro i
  change masked θ ((F.shelf ((numbering (Cycle n)) ((numbering (Cycle n)).symm (v,i)))).support)
      (F.table ((numbering (Cycle n)) ((numbering (Cycle n)).symm (v,i)))) U=_
  rw [Equiv.apply_symm_apply]
  have swap := PhysicalNext.Repeat.Turn.vigor v.1 v.2 U (X:=F.footprint i)
    (Y:=(F.shelf (v,i)).support) θ rfl
  by_cases good : Healthy θ (F.footprint i) (v.view U)
  · rw [masked_eq _ _ _ _ (swap.mp good),masked_eq _ _ _ _ good]
    rfl
  · rw [masked_ne _ _ _ _ (mt swap.mpr good),masked_ne _ _ _ _ good]

private theorem petals_size (U : Config G n) (x : Site n) : ‖petals U x‖≤2 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤2)).mpr
  intro j
  have bound (i k : Step) : ‖plate U x i k‖≤2 :=
    (G.curvature_norm _).trans (G.chord_le_two _)
  have pair (i : Step) : ‖plate U x i (posDir j.val.2)-plate U x i (negDir j.val.2)‖≤4 :=
    (norm_sub_le ..).trans ((add_le_add (bound ..) (bound ..)).trans_eq (by norm_num))
  unfold AnalyticBridge.VerifiedReset.petals StressFlux.clover StressFlux.stencil
  rw [norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤4⁻¹)]
  exact (mul_le_mul_of_nonneg_left ((norm_sub_le ..).trans (add_le_add (pair _) (pair _)))
    (by norm_num)).trans_eq (by norm_num)

theorem seated_prism (a : PrismA G) (B : BudgetPoint) (σ C : ℝ)
    (bill : Commission a.cells σ C a.grade) {n : Side} :
    let F:=frame n a Frame.full
    (∀i,(F.footprint i).card≤((a.cells i).footprint (0:Site n)).card+625) ∧
    (∀i,Measurable (F.dataF i)) ∧
    (∀i U,‖F.dataF i U‖≤(a.cells i).magnitude*2^(a.rise+2)*2) := by
  rcases a with ⟨d,r,hd,P⟩
  cases r with
  | zero=>
    intro F
    refine ⟨fun i=>(card_union_le ..).trans (Nat.add_le_add_left ?_ _),
      fun i=>((Frame.rose_era P n 1 Frame.full bill.hue B).regular i).borel,?_⟩
    · simpa only [card_singleton,one_mul,show (2+2+1)^4=625 from rfl] using (Corona.halo_size ({0}:Support n) 2)
    · intro i U
      have pollen : ‖Render.pollen (0:Site n) (P i) U‖≤(P i).magnitude*2^2 := by
        apply (Frame.clovers _ _).trans
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (petals_size U 0) 2)
          (sum_nonneg fun _ _=>abs_nonneg _)
      have size := (norm_sub_le ((P i).unmasked U 0) (Render.pollen 0 (P i) U)).trans
        (add_le_add ((P i).unmasked_bound U 0) pollen)
      change ‖recipe 1 Frame.full i * ((P i).unmasked U 0-Render.pollen 0 (P i) U)‖≤_
      rw [show recipe 1 Frame.full i=factor by simp [recipe,Frame.full],norm_mul,Real.norm_of_nonneg factor_pos.le]
      exact (mul_le_of_le_one_left (norm_nonneg _) factor_le).trans (size.trans_eq (by ring))
  | succ r=>
    intro F
    refine ⟨fun _=>Nat.le_add_right _ _,fun i=>((bandFits (F:=P) (n:=n) (a:=1) (h:=Frame.full) bill.hue B).regular i).borel,?_⟩
    intro i U
    change ‖recipe 1 Frame.full i * (P i).unmasked U 0‖≤_
    rw [show recipe 1 Frame.full i=factor by simp [recipe,Frame.full],norm_mul,Real.norm_of_nonneg factor_pos.le]
    exact (mul_le_of_le_one_left (norm_nonneg _) factor_le).trans (((P i).unmasked_bound U 0).trans
      (le_mul_of_one_le_right (mul_nonneg (sum_nonneg fun _ _=>abs_nonneg _) (by positivity)) (by norm_num)))

end YM.Integration.OriginalMarkedRunAction
