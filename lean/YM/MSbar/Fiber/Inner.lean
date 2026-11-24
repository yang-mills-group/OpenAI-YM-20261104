import YM.Push.SECTOR_MEASURE.Output
/-! Extension of Tree.Cut; invariant under the subgroup actually being quotiented. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG.StepData
open Lattice Wilson MeasureTheory Filter Function Tree Push Push.SectorMeasure
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{c f:Side}{S:StepData c f}{V:Type*}
def Inner (S:StepData c f) (g:Config G f→ℝ) := ∀ k:Site f → G.El,(∀ i,k (S.ratio.embed i)=1) → ∀ U,g (gauge k U)=g U
-- conditional recognized invariance
variable {x W:ℝ}{g:Config G f→ℝ}
lemma pushColumns (D:SectorMeasure.Allocation G S x W) (F: Forest S.ratio) (β:ℝ) (g:Config G f→ℝ) (hm:S.patch.Branches S.kernel G)(h:Envelope g)(he:S.Inner g)(U:Config G c) : (∑ A,output D F β g A U)= S.push β g U:=by
  let L : S.Choices → F.Slice G → ℝ := fun _ a => g (F.drape a)
  obtain ⟨C,hc⟩:= h.cost
  have hi : Envelope (fun i=> g (F.drape i)):= ⟨h.meas.comp F.continuous_drape.measurable,C,fun _=>hc _⟩
  have hg k : Integrable (through S F β U L k) (F.order G) := through_integrable F β U L hm k (hi.integrable _)
  have hx : (∫ t:Config G f,S.density β t U • g t ∂prior G f) = (∫ x,S.density β (F.drape x) U • g (F.drape x) ∂ F.order G):= F.pack _ (StepData.push_slice (S.isKernel hm β) U g (h.integrable _)) (fun k hy t=>by rw [he k hy,← S.covary hm k β t U,show gauge (k ∘ S.ratio.embed) U=U from funext (fun i =>by simp [Lattice.gauge,hy])]) -- check
  change (∑ A, D.column A F U (through S F β U L)) = _
  unfold StepData.push; rw [hx,D.partitions hm F U _ hg]
  unfold tagTotal; rw [← integral_finsetSum _ fun i _ => hg i]
  apply integral_congr_ae
  filter_upwards with a
  unfold StepData.density through taggedKernel L; rw [Finset.sum_smul]
end YM.RG.StepData
