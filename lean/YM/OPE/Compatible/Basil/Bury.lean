import YM.Push.SECTOR_MEASURE.Output
/-! # Vertical payloads. Relax gauge from YM.Push.SECTOR_MEASURE.Output;
 ONLY required invariance for one-step estimates in fixed W chart. -/
set_option autoImplicit false
noncomputable section
namespace YM.Push.SectorMeasure
open Filter Function Lattice RG Wilson Pressure Pressure.Stores Tree MeasureTheory
open Next.Fluctuations.Sector
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f}
abbrev Pedal (S:StepData c f){X:Sort*}(g:Config G f→X) := ∀ k : Site f→ G.El,(∀ i,k (S.ratio.embed i)=1)→∀ U,g (Lattice.gauge k U)=g U
lemma pedal_pack {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X][CompleteSpace X](F:Forest S.ratio) (β:ℝ)(g : Config G f → X) (hm:S.patch.Branches S.kernel G)(h : Integrable g (prior G f)) (he : Pedal S g)(V : Config G c) :
 S.push β g V = ∫ x : F.Slice G, S.density β (F.drape x) V • g (F.drape x) ∂F.order G:=by
    refine F.pack _ (StepData.push_slice (S.isKernel hm β) V g h) (fun k hv U=>?_)
    have ht : Lattice.gauge (k ∘ S.ratio.embed) V=V:= by funext;simp [Lattice.gauge,hv]
    rw [he k hv, ← S.covary hm k β U V, ht]
lemma pedal_columns {x W : ℝ}(D : Allocation G S x W) (F : Forest S.ratio) (β : ℝ) (g : Config G f → ℝ) (hm:S.patch.Branches S.kernel G)(h : Envelope g) (he : Pedal S g)(V : Config G c) :
    (∑ A, output D F β g A V) = S.push β g V := by
  let L : S.Choices → F.Slice G → ℝ := fun _ a => g (F.drape a)
  have hg k : Integrable (through S F β V L k) (F.order G) :=
    through_integrable F β V L hm k ((Env.along h F.continuous_drape.measurable).integrable _)
  rw [pedal_pack F β g hm (h.integrable _) he V]
  change (∑ A, D.column A F V (through S F β V L)) = _
  rw [D.partitions hm F V _ hg]
  unfold tagTotal; rw [← integral_finsetSum _ fun i _ => hg i]
  apply integral_congr_ae
  filter_upwards with a
  unfold StepData.density through taggedKernel L; rw [Finset.sum_smul]
end YM.Push.SectorMeasure
