import YM.Integration.PhysicalAffineScalarMetric
import YM.Integration.ConditionalAffineActiveInverse

/-! The complete uncut rooted scalar expressed through the independently
prescribed all-bond native Gaussian. Both the paired half-log and the
stationary square are computed on the same original signed output rows. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.PhysicalAffineScalarSpectralRoot
open Function Filter MeasureTheory Set Lattice Wilson RG Precision Exterior Tree Matrix
open Pressure Pressure.Stores Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian
open AnalyticBridge.GaussianFieldAlignment AnalyticBridge.RelativeLogdet
open FreeResolvent FreeResolvent.Affine PhysicalAffineScalarProjection PhysicalAffineScalarUncut
open PhysicalAffineScalarAperture (noHole)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f}

theorem log_reindex {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : β ≃ α) (A : Matrix α α ℝ) (i : β) : logKernel (A.submatrix e e) i i = logKernel A (e i) (e i) := by
  change (∫ u in Ioi (0:ℝ), density (A.submatrix e e) u i i) = ∫ u in Ioi (0:ℝ), density A u (e i) (e i)
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u _
  have hs : A.submatrix e e + u • (1:Matrix β β ℝ) = (A + u • 1).submatrix e e := by
    ext a b
    simp [Matrix.one_apply,e.injective.eq_iff]
  simp only [density,Matrix.sub_apply,Matrix.smul_apply,Matrix.one_apply_eq,smul_eq_mul,mul_one,
    resolve,hs,Matrix.inv_submatrix_equiv,Matrix.submatrix_apply]

private theorem shifted_unit {α : Type} [Fintype α] [DecidableEq α] (A : Matrix α α ℝ)
    (hA : A.PosDef) (u : ℝ) (hu : 0≤u) : IsUnit (A+u • 1).det :=
  IsUnit.mk0 _ (hA.add_posSemidef (Matrix.PosSemidef.one.smul hu)).det_pos.ne'

theorem log_on {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : β ↪ α) (A : Matrix α α ℝ) (h : (A.submatrix e e).PosDef) (j : β) :
    logKernel (Shell.pad e A) (e j) (e j)=logKernel (A.submatrix e e) j j := by
  change (∫ u in Ioi (0:ℝ), density (Shell.pad e A) u (e j) (e j)) = ∫ u in Ioi (0:ℝ), density (A.submatrix e e) u j j
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  simp only [density,Matrix.sub_apply,Matrix.smul_apply,Matrix.one_apply_eq,smul_eq_mul,mul_one,
    ConditionalAffineActiveInverse.on e A u hu.le (shifted_unit _ h u hu.le) j j]

theorem log_off {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : β ↪ α) (A : Matrix α α ℝ) (h : (A.submatrix e e).PosDef) (i : α) (hi : i ∉ Set.range e) :
    logKernel (Shell.pad e A) i i=0 := by
  change (∫ u in Ioi (0:ℝ), density (Shell.pad e A) u i i) = 0
  calc _ = ∫ _ in Ioi (0:ℝ), (0:ℝ) := by
             apply setIntegral_congr_fun measurableSet_Ioi
             intro u hu
             simp only [density,Matrix.sub_apply,Matrix.smul_apply,Matrix.one_apply_eq,smul_eq_mul,mul_one,
               ConditionalAffineActiveInverse.off_diagonal e A u hu.le (shifted_unit _ h u hu.le) i hi,
               attenuation,sub_self]
       _ = 0 := by simp

theorem sum_range {α β : Type} [Fintype α] [Fintype β] (e : β ↪ α) (w : α → ℝ)
    (hz : ∀ i, i∉Set.range e → w i=0) : ∑ j : β, w (e j) = ∑ i : α, w i := by
  calc _ = ∑ j : β, ∑ i : α, if e j=i then w i else 0 := by simp
       _ = ∑ i : α, w i := by
         rw [Finset.sum_comm]
         apply Finset.sum_congr rfl
         intro i _
         by_cases hi : i ∈ Set.range e
         · obtain ⟨j,rfl⟩ := hi
           simp [e.injective.eq_iff]
         · have he (j : β) : e j ≠ i := fun he => hi ⟨j,he⟩
           simp [he,hz i hi]

variable (T : Tube G S) (x : ℝ) (k : S.Choices) (F : Forest S.ratio)
local notation "Coarse" => FreeResolvent.Vec G c 1
local notation "M" => whole S F k T.high T.up FreeResolvent.Affine.all
local notation "H" => primary S F k T.high T.up FreeResolvent.Affine.all
local notation "J" => responseMatrix T k

theorem positive (b : Coarse) (h : (PhysicalAffineScalarUncut.gram T x k F b).PosDef) : ((H) b).PosDef := by
  let e : (Active (noHole S) x F × G.ColorIndex) ≃ Precision.Key F G := (Native.lineEquiv F x).symm
  have hp : (((H) b).submatrix e e).PosDef := by
    rw [PhysicalAffineScalarMetric.uncut] at h
    exact h
  have he : ((H) b) = (((H) b).submatrix e e).submatrix e.symm e.symm := by ext i j; simp
  rw [he]
  exact hp.submatrix e.symm.injective

/-- Native full-bond precision with the erased tree diagonal removed again
when computing the physical stationary mean, as required by the no-hole chart. -/
def covariance (b : Coarse) := FreeResolvent.TestD.action M 0 b - Shell.off (freeTo G S F)

def retained (b : Coarse) := PhysicalAffineScalarUncut.offset T k b -
  (J b) *ᵥ (covariance T k F b *ᵥ inputForcing T k b)

/-- Rooted paired logarithm of the independently prescribed canonical full
precision on common raw fine-bond keys, with the original subtraction order. -/
def halfLog (o : Site c) (b : Coarse) : ℝ := ∑ i : Raw G f, if S.ratio.parent i.1=o then
  (logKernel ((M) 0) i i - logKernel ((M) b) i i)/2 else 0

def stationaryScalar (g : ℝ) (o : Site c) (b : Coarse) : ℝ := halfLog T k F o b +
  ∑ i : Rows.Receipt G S, if PhysicalAffineScalarComparison.rowRoot S i=o then -(retained T k F b i)^2/(2*g^2) else 0

theorem active (b : Coarse) (h : ((H) b).PosDef) : embeddedCovariance T x k F b = covariance T k F b := by
  rw [PhysicalAffineScalarFullCovariance.original]
  exact ConditionalAffineActiveInverse.original S F k T.high T.up b (IsUnit.mk0 _ h.det_pos.ne')

theorem source (b : Coarse) (h : ((H) b).PosDef) : sourceResidual T x k F b = retained T k F b := by
  rw [projected_residual,original_projection,active T x k F b h,Matrix.sub_mulVec,Matrix.one_mulVec,
    ←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec]
  rfl

theorem root_log (o : Site c) (b : Coarse) (h0 : ((H) 0).PosDef) (hb : ((H) b).PosDef) :
    (∑ j : Active (noHole S) x F × G.ColorIndex, if S.ratio.parent j.1.1.1.1=o then
      (logKernel (PhysicalAffineScalarUncut.gram T x k F 0) j j-logKernel (PhysicalAffineScalarUncut.gram T x k F b) j j)/2 else 0) =
    halfLog T k F o b := by
  let e : (Active (noHole S) x F × G.ColorIndex) ≃ Precision.Key F G := (Native.lineEquiv F x).symm
  let f := freeTo G S F
  let w (i : Raw G _) := if S.ratio.parent i.1=o then (logKernel ((M) 0) i i - logKernel ((M) b) i i)/2 else 0
  have hon (a : Coarse) (ha : ((H) a).PosDef) (j) : logKernel ((M) a) (f j) (f j)=logKernel ((H) a) j j :=
    log_on f (block S k T.high T.up FreeResolvent.Affine.all a) ha j
  have hoff (a : Coarse) (ha : ((H) a).PosDef) (i) (hi : i ∉ Set.range f) : logKernel ((M) a) i i=0 :=
    log_off f (block S k T.high T.up FreeResolvent.Affine.all a) ha i hi
  have hw (i) (hi : i∉Set.range f) : w i=0 := by simp [w,hoff 0 h0 i hi,hoff b hb i hi]
  change _ = ∑ i : Raw G _, w i
  rw [←sum_range f w hw,←e.sum_comp (fun j => w (f j))]
  apply Finset.sum_congr rfl
  intro j _
  have hg (a : Coarse) : PhysicalAffineScalarUncut.gram T x k F a = ((H) a).submatrix e e := by
    rw [PhysicalAffineScalarMetric.uncut]; rfl
  have hp : S.ratio.parent j.1.1.1.1 = S.ratio.parent (f (e j)).1 := rfl
  simp only [hg,log_reindex,w,hp,hon 0 h0,hon b hb]

/-- Complete original no-hole scalar at one actual translation, including
its original affine source projection and its independent paired determinant. -/
theorem original (g : ℝ) (o : Site c) (b : Coarse)
    (h0 : (PhysicalAffineScalarUncut.gram T x k F 0).PosDef)
    (hb : (PhysicalAffineScalarUncut.gram T x k F b).PosDef) :
    scalarAt T x k F g o b = stationaryScalar T k F g o b := by
  let hc := positive T x k F b hb
  change _ + (∑ i : Rows.Receipt G S, if PhysicalAffineScalarComparison.rowRoot S i=o
    then -(sourceResidual T x k F b i)^2/(2*g^2) else 0) = _
  rw [root_log T x k F o b (positive T x k F 0 h0) hc,source T x k F b hc]
  rfl
end YM.Integration.PhysicalAffineScalarSpectralRoot
end
