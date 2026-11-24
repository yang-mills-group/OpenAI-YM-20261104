import YM.Integration.WilsonReportingCellMotion
import YM.RG05Readout.Harvest.Prices

/-! The unnormalized full Haar integral of the actual spatially
translated Wilson step on any integrable roster observable. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingCellIntegral
open Function Filter Finset MeasureTheory Lattice Wilson RG Source RG12
open Extra.Histories Trace.Physical RG05Readout Address Native Harvest
open scoped Classical BigOperators Topology
variable {G:Gauge} {C:Family G} {d m N per:ℕ}

def total {n:Side} (F:Goods G n) : ℂ := ∫ U,F U ∂prior G n

theorem mean {I:Type*} [Fintype I] {n:Side} (X:I→Goods G n)
    (H:∀i,Integrable (X i) (prior G n)) :
    total (Address.average X)=Address.average (fun i=>total (X i)) := by
  unfold total Address.average
  simp only [Pi.smul_apply,Finset.sum_apply,smul_eq_mul,integral_const_mul]
  rw [integral_finsetSum _ (fun i _=>H i)]

theorem translation {n:Side} (o:Site n) (F:Goods G n) (H:Integrable F (prior G n)) :
    total (F ∘ Lattice.pull (1:Signed) o)=total F := by
  let k:=Lattice.pull (K:=G.El) (1:Signed) o
  have hp:MeasurePreserving k (prior G n) (prior G n):=prior_pull ..
  have measurable:AEStronglyMeasurable F (Measure.map k (prior G n)):=by
    rw [hp.map_eq]; exact H.aestronglyMeasurable
  change (∫ U,F (k U) ∂prior G n)=∫ U,F U ∂prior G n
  rw [← integral_map hp.aemeasurable measurable,hp.map_eq]

theorem step (F:Goods G (C.side (m+1) per)) (H:Integrable F (prior G _)) :
    total (blast C.path N per m d F)=((C.S.block m).val:ℂ)^d*total F := by
  unfold total blast
  simp only [Pi.smul_apply,smul_eq_mul,integral_const_mul,
    StepData.push_integral (C.path.levels.transition_mass ..) F H]

theorem original (F:Body→Goods G (C.side (m+1) per)) (H:BLight F) (φ:Body) :
    total (journey C per m N d F φ)=((C.S.block m).val:ℂ)^d*
      Address.average (fun s:Bud C per m=>total (F (Native.pull (displacement C per m s)
        ((C.S.block m).val:ℝ)⁻¹ φ))) := by
  let β:=(C.path.β N per (m+1))
  let ψ (s:Bud C per m):=Native.pull (displacement C per m s) ((C.S.block m).val:ℝ)⁻¹ φ
  let shifted (s:Bud C per m):=F (ψ s) ∘ Lattice.pull (1:Signed) (child C per m s)
  have integrals (s):Integrable (shifted s) (prior G _):=sail_lit F H φ s
  have bills (s):Integrable (blast C.path N per m d (shifted s)) (prior G _):=
    (StepData.push_integrable (C.path.levels.transition_mass m per β) _ (integrals s)).smul _
  change total (Address.average (fun s=>blast C.path N per m d (shifted s)))=
    ((C.S.block m).val:ℂ)^d*Address.average (fun s=>total (F (ψ s)))
  rw [mean _ bills]
  have rows (s):total (blast C.path N per m d (shifted s))=
      ((C.S.block m).val:ℂ)^d*total (F (ψ s)) :=
    (step _ (integrals s)).trans (congrArg (_ * ·) (translation _ _ (H (ψ s))))
  simp_rw [rows]
  unfold Address.average
  rw [← Finset.mul_sum]
  simp only [smul_eq_mul]
  ring

end YM.Integration.WilsonReportingCellIntegral
