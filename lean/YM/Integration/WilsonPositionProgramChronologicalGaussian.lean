import YM.Integration.WilsonPositionProgramForestRoutes
import YM.Integration.WilsonConditionalTaylorWheelPhysicalSide
import YM.Integration.WilsonMarkedRelativeGaussianBudget

/-! A single pre-period Gaussian budget for the actual forest of the variable chronological program. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramChronologicalGaussian
open Function Filter Lattice RG Wilson Tree RegulatorIR FormalBulk08 FormalBulk08.Flat
open Next.Free PhysicalNext.Repeat.Legato Comparison.RG02
open scoped Classical Matrix
variable {G:Gauge}

theorem original (R:Run G)(N i:ℕ)(hi:i<N):
    let V:=R.family.path.levels
    ∃ b σ:ℝ, 1≤b ∧ 1≤σ ∧ ∀ per:ℕ,
      let S:=V.clock.op i per
      let F:=Halo.bios S
      (∀v w, |WilsonMarkedRelativeGaussianBudget.mean R N i per F v w|≤b) ∧
      (∀tag:S.Choices, ∀v w, |(((RunFormalChain.fromRun R).step N i per hi).covariance F tag) v w|≤σ) ∧
      Fintype.card (F.Free × G.ColorIndex)=(R.family.side i per).val^4*
        Fintype.card (Lodge.selected G (destination V N i).patch (routes (destination V N i).patch)):=by
  intro V
  let P:=destination V N i
  obtain ⟨b,σ,hb,hσ,book⟩:=WilsonMarkedRelativeGaussianBudget.onRun R N i hi (routes P.patch)
  refine ⟨b,σ,hb,hσ,fun per=>?_⟩
  let S:=V.clock.op i per
  obtain ⟨F,orig,mean,noise⟩:=book per
  have eq:HEq (Halo.bios S) (Reef.floor V.clock.kernel P (routes P.patch) (R.family.side i per)):=
    (heq_of_eq ((WilsonPositionProgramForestRoutes.original S).trans
      (WilsonConditionalTaylorWheelCanonicalForest.original S).symm)).trans
      (WilsonConditionalTaylorWheelPhysicalSide.forest S P.patch V.clock.kernel rfl rfl)
  have same:F=Halo.bios S:=eq_of_heq (orig.trans eq.symm)
  subst F
  exact ⟨mean,noise⟩

end YM.Integration.WilsonPositionProgramChronologicalGaussian
end
