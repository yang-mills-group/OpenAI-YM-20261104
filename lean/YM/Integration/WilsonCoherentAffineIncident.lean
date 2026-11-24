import YM.Integration.WilsonCoherentAffineRoster
import YM.Integration.WilsonCoherentForestReadout

/-! The chronological coupling and the saved compact crossings in the
actual local conditional. The physical sample contains unscaled angles. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentAffineIncident
open Function Lattice RG Tree Wilson Source Finset PowerSeries
open PhysicalNext.Repeat.Legato RGComparison.Core16 RGComparison.Core16.Spool
open WilsonCoherentReportingFrame WilsonCoherentAffineRoster Dict06.Series
open WilsonCoherentForestMeasure WilsonReportingForestPivots WilsonCoherentReportingForest
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

variable {G:Gauge} (R:Run G) {I:Type} [Fintype I] (d:I→ℕ) {n:Side}

private theorem live {u : Type} [Fintype u] (J:u→Lamp G) (b:Slice J→G.El)
    (z:Slice J→G.Color) : ContDiffAt ℝ ∞ (fun t:ℝ=>WilsonCoherentPivotStencil.field J b (t • z)) 0 := by
  obtain ⟨A,h,eq⟩:=WilsonCoherentPivotStencil.extension J
  have same: (fun t:ℝ=>WilsonCoherentPivotStencil.field J b (t • z))=
    fun t:ℝ=> A (fun j=>G.mat (b j),t • z):=funext fun t=>(eq b _).symm
  rw [same]
  exact ((h.comp (contDiff_const.prodMk (contDiff_id.smul contDiff_const))).contDiffAt.of_le le_top)

theorem scaled (θ:ℝ) (y:∀i,R.family.label (d i)) (o:I→Site n) (b:Config G n)
    (z:Edge (Site n)→G.Color) (a:ℝ) (k:ℕ) :
    coeff k (filed R d θ y o b (a • z))=a^k • coeff k (filed R d θ y o b z) := by
  classical
  unfold filed
  simp only [map_sum,PowerSeries.coeff_C_mul,Finset.smul_sum]
  apply sum_congr rfl
  intro v _
  let J:=roster R d v
  let F:=fun t:ℝ=>WilsonCoherentPivotStencil.field J (b ∘ legs J o) (t • (z ∘ legs J o))
  have ray : (fun t:ℝ=>WilsonCoherentPivotStencil.field J (b ∘ legs J o) (t • ((a • z) ∘ legs J o))) =
      fun t:ℝ=> F (t*a):= by
    funext t
    change WilsonCoherentPivotStencil.field J _ (t • (a • (z ∘ legs J o)))=
      WilsonCoherentPivotStencil.field J _ ((t*a) • (z ∘ legs J o))
    rw [smul_smul]
  rw [←received,←received,ray,rescale_ps F (live J _ _) a k]
  exact mul_smul_comm ..

variable {c f:Side} {S:StepData c f}

theorem measured (T:Forest S.ratio) (B:Finset T.Free) (θ:ℝ) (y:∀i,R.family.label (d i))
    (o:I→Site f) (q:ℕ) (g:ℝ) (hg:g≠0) (z:Sample T B G) :
    WilsonCoherentForestReadout.polynomial T B R d θ y o q z =
      ∑ j∈range (q+1),g^j • coeff j (filed R d θ y o (restored T B z.1 1) (g⁻¹ • drift T B z.2)) := by
  rw [WilsonCoherentForestReadout.polynomial,reported]
  apply sum_congr rfl
  intro j _
  rw [scaled,smul_smul,←mul_pow,mul_inv_cancel₀ hg]

end YM.Integration.WilsonCoherentAffineIncident
