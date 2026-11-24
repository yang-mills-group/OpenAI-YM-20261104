import YM.Comparison.RG02.Affinity.Metric
/-!
# Moving precision (rotated from full stationary torus Gaussian).

Polynomial moments through high orders do not keep this `B` rotation in actual estimates;
 can use the genuine `Q` Taylor entrywise. Full rank and determinant at zero.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Moving
open Function Filter Finset MeasureTheory
open YM.Marker YM.Multi Order Assembly Actual YM.Lattice YM.Tree
open YM.Precision YM.Next.SectorChange Gaussian Affinity Matrix
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff ENNReal
variable {G : Gauge} {V : Type} [DecidableEq V] {R : Census V}
variable {I : Type} [Fintype I] [DecidableEq I]
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
local notation "E" => House X I

/-- Keep a symmetric covariance on all formal target space, only smooth/positive *near flat*.
 No complex extension in this statement. For a stationary affine step one can take the canonical
 Hessian inverse or completed-square covariance, not assumed diagonal or density normalized outside.
-/
structure Field (X I : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [Fintype I] [DecidableEq I] where
   Q : Regulator X → Matrix I I ℝ
   smooth : ContDiffAt ℝ ω Q 0
   flat : (Q 0).PosDef
   symmetric s : (Q s).IsSymm

namespace Field
variable (C : Field X I)
local notation "Q₀"=> C.Q 0
def gram (s : Regulator X) := (C.Q s)⁻¹
lemma gram_known : ContDiffAt ℝ ω C.gram 0 := (YM.Push.Loops.inv_contDiffAt _ (IsUnit.mk0 _ C.flat.det_pos.ne')).comp _ C.smooth
lemma gram_positive : (C.gram 0).PosDef := C.flat.inv
lemma gram_symmetric s : (C.gram s).IsSymm := by unfold Matrix.IsSymm gram; rw [Matrix.transpose_nonsing_inv,(C.symmetric s).eq]
variable [FiniteDimensional ℝ X]

def B := MetricFix.blanker C.gram_known C.gram_positive
lemma B_flat : C.B 0=1 := MetricFix.blanked ..
lemma B_smooth : ContDiffAt ℝ ω C.B 0 := MetricFix.blank_smooth ..
lemma rotated : ∀ᶠ s in 𝓝 0,(C.B s).transpose*C.gram s*C.B s=C.gram 0 := MetricFix.blank_cost _ _ (Eventually.of_forall (fun s=>C.gram_symmetric s))
lemma B_lives : ∀ᶠ s in 𝓝 0,0<(C.B s).det := (YM.Push.Loops.det_contDiff.contDiffAt.comp 0 C.B_smooth).continuousAt.eventually (lt_mem_nhds (by rw [Function.comp_apply,C.B_flat, Matrix.det_one]; exact zero_lt_one))

variable {s : Regulator X}
omit [FiniteDimensional ℝ X] in
private lemma fill (U : Matrix I I ℝ) (he : IsUnit U.det) (h : U.transpose*C.gram s*U=C.gram 0) : (C.Q s).PosDef := by
   apply Matrix.posDef_inv_iff.mp; apply Matrix.IsUnit.posDef_star_left_conjugate_iff ((Matrix.isUnit_iff_isUnit_det U).mpr he) |>.mp
   simpa only [Matrix.star_eq_conjTranspose,show U.conjTranspose=U.transpose from rfl,gram] using (show (U.transpose*C.gram s*U).PosDef from h ▸ C.gram_positive)

lemma known {s : Regulator X} (h : (C.B s).det ≠ 0) (ht : (C.B s).transpose*C.gram s*C.B s=C.gram 0) : (C.Q s).PosDef := C.fill _ (IsUnit.mk0 _ h) ht
lemma positive : ∀ᶠ s in 𝓝 0,(C.Q s).PosDef := (C.B_lives.and C.rotated).mono fun _ he=> known C he.1.ne' he.2

variable {W : Matrix I I ℝ} (hQ : W.transpose*C.gram s*W=C.gram 0)
include hQ
omit [FiniteDimensional ℝ X] in
lemma force_lives (x:I→ℝ) : force (C.Q s) (W *ᵥ x)=force Q₀ x := by
   unfold force
   change _= x ⬝ᵥ (C.gram 0 *ᵥ x)
   rw [← hQ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec]
   exact dotProduct_comm .. 
variable (hw : 0 < W.det)
include hw
omit [FiniteDimensional ℝ X] in
lemma paid_D : (C.Q s).det = (Q₀).det * W.det^2 := by
   have he := (C.fill W (IsUnit.mk0 _ hw.ne') hQ).det_pos.ne'
   have hh := C.flat.det_pos.ne'
   have hx := congrArg Matrix.det hQ; unfold gram at hx; rw [Matrix.det_mul,Matrix.det_mul, Matrix.det_transpose, Matrix.det_nonsing_inv, Matrix.det_nonsing_inv,Ring.inverse_eq_inv,Ring.inverse_eq_inv] at hx
   field_simp at hx; linear_combination - hx  -- edit
omit [FiniteDimensional ℝ X] in
lemma coat_eq : coat (C.Q s)=coat Q₀ * W.det := by
   unfold coat; rw [C.paid_D hQ hw, Real.sqrt_mul C.flat.det_pos.le,Real.sqrt_sq hw.le,mul_assoc]

omit [FiniteDimensional ℝ X] in
theorem port {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f:(I→ℝ)→Y) :
    (Integrable f (cloud (C.Q s)) ↔ Integrable (f ∘ fun x=> W *ᵥ x) (cloud Q₀)) ∧
      (∫ v, f v ∂cloud (C.Q s))=(∫ v:I→ℝ,f (W *ᵥ v) ∂cloud Q₀) := by
   let p := fun v:I→ℝ=> Real.exp (-(force (C.Q s) v/2)) • f v
   let q := fun v:I→ℝ=> p (W *ᵥ v)
   have he (v : I→ℝ) : Real.exp (force (C.Q s) v/2) • p v=f v := by unfold p; rw [_root_.smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero,one_smul]
   obtain ⟨h₁,h₂⟩:= under_cloud (C.fill W (IsUnit.mk0 _ hw.ne') hQ) p; dsimp only at h₁ h₂; simp_rw [he] at h₁ h₂
   obtain ⟨h₃,h₄⟩:= linear_paid W 0 hw p; simp_rw [zero_add] at h₃ h₄
   obtain ⟨h₅,h₆⟩:= under_cloud C.flat q; dsimp only at h₅ h₆; simp_rw [← C.force_lives hQ] at h₅ h₆; unfold q at h₅ h₆; simp_rw [he] at h₅ h₆
   refine ⟨h₁.symm.trans (h₃.trans h₅),?_⟩
   rw [h₂,h₆,C.coat_eq hQ hw,mul_comm (coat _),← smul_smul] at h₄
   exact (smul_right_inj (Gaussian.coat_pos C.flat).ne').mp ((smul_right_inj hw.ne').mp h₄)
end Field
end YM.Comparison.RG02.Moving
