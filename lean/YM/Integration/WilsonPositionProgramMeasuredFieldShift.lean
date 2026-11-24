import YM.Integration.WilsonPositionProgramChronologicalGaussian
import YM.Integration.WilsonMarkedRelativeGaussianCoordinates

/-! The true affine draw on a chronological fold, with the original before-period height. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramMeasuredFieldShift
open Function Lattice Wilson RG Tree Exterior RegulatorIR FormalBulk08 FormalBulk08.Flat
open Stationary WilsonMarkedRelativeGaussianCoordinates Next.Free PhysicalNext.Repeat.Legato Comparison.RG02
open scoped Classical Matrix
variable {G:Gauge}

def height (G:Gauge)(n:Side)(b M:ℝ):ℝ:=
  1+charge G+charge G*((((n.val^4*Fintype.card (Loc G 1):ℕ):ℝ))*b+1)*M

theorem draw (R:Run G)(N i per:ℕ)(hi:i<N)
    (F:Forest (R.family.path.levels.clock.op i per).ratio)
    (tag:(R.family.path.levels.clock.op i per).Choices)(b:ℝ)(hb:0≤b)
    (paid:∀v w,|WilsonMarkedRelativeGaussianBudget.mean R N i per F v w|≤b)
    (x:fieldDir G (R.family.side i per) 1)(z:(F.Free × G.ColorIndex)→ℝ):
    1+‖(Bulk.translated ((RunFormalChain.fromRun R).step N i per hi) F x z).2‖ ≤
      height G (R.family.side i per) b ‖x‖*(1+‖z‖):=by
  rw [WilsonMarkedRelativeGaussianCoordinates.original R N i per hi F tag x z]
  unfold height
  rw [←WilsonMarkedInheritedGaussianPlacement.coarseSize G (R.family.side i per)]
  apply (shifted F (WilsonMarkedRelativeGaussianBudget.mean R N i per F) b hb paid x
    (z ∘ (Reef.pines F).symm)).trans
  apply mul_le_mul_of_nonneg_left _ (by
    have hc:0≤charge G:=zero_le_one.trans (le_max_left ..)
    positivity)
  apply add_le_add_right
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg z)).2 fun a=>norm_le_pi_norm z _

theorem original (R:Run G)(N i:ℕ)(hi:i<N):
    let V:=R.family.path.levels
    ∃ b σ:ℝ,1≤b ∧ 1≤σ ∧ ∀per:ℕ,
      let S:=V.clock.op i per
      let F:=Halo.bios S
      let K:=((RunFormalChain.fromRun R).step N i per hi)
      (∀ _tag:S.Choices,∀x:fieldDir G (R.family.side i per) 1,∀z:(F.Free × G.ColorIndex)→ℝ,
        1+‖(Bulk.translated K F x z).2‖≤height G (R.family.side i per) b ‖x‖*(1+‖z‖)) ∧
      (∀tag:S.Choices,∀v w,|K.covariance F tag v w|≤σ) ∧
      Fintype.card (F.Free × G.ColorIndex)=(R.family.side i per).val^4*
        Fintype.card (Lodge.selected G (destination V N i).patch (routes (destination V N i).patch)):=by
  intro V
  obtain ⟨b,σ,hb,hσ,licensed⟩:=WilsonPositionProgramChronologicalGaussian.original R N i hi
  refine ⟨b,σ,hb,hσ,fun per=>?_⟩
  obtain ⟨m,c⟩:=licensed per
  exact ⟨fun tag x z=>draw R N i per hi _ tag b (zero_le_one.trans hb) m x z,c⟩

end YM.Integration.WilsonPositionProgramMeasuredFieldShift
end
