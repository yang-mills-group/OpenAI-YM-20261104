import YM.FVA2.GraphMaster
import YM.FVA2.Substitute

/-! Small support for writing real operations in the actual coefficient coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.ArrayMap
open Finset Function Set Filter Matrix MeasureTheory MS MS.Koszul MS.Book MS.Book.Convolve
open MS.Bare MS.Cylinder MS.Native Ends MS.Cylinder.Taylor
open scoped Topology ContDiff

variable {A P I : Type} [Fintype A] [Fintype P] [Fintype I]
  [DecidableEq A] [DecidableEq P] [DecidableEq I] {G:Gauge}

omit [Fintype A] in
lemma coord_recover (i j:Z G A) : projector i (priv j)=if i=j then 1 else 0 := by
  rcases i with ⟨i,a⟩; rcases j with ⟨j,b⟩
  rw [projector_k]; by_cases he : i=j <;> by_cases hp : a=b <;>
    simp [he,hp,baseC,priv]

def chartBasis (G:Gauge) (A:Type) [Fintype A] [DecidableEq A] :
    Links G A ≃ₗ[ℝ] (Z G A→ℝ) := {
  toFun := fun f i=> projector i f
  invFun := fun x=> ∑ i,x i • priv i
  left_inv := Native.frame
  right_inv x := by funext i; simp [map_sum,map_smul,coord_recover,mul_ite]
  map_smul' x y := funext fun i=> map_smul (projector i) x y
  map_add' x y := funext fun i=> map_add (projector i) x y }

lemma from_chart (j : Z G A) : (chartBasis G A).symm (Pi.single j 1)=priv j:= by
  apply (chartBasis G A).injective
  rw [LinearEquiv.apply_symm_apply]; funext i; simp [chartBasis,coord_recover, Pi.single_apply]

def baseChart (G:Gauge) (A:Type) [Fintype A] [DecidableEq A] : Module.Basis (Z G A) ℝ (Links G A):=
  (Pi.basisFun ℝ (Z G A)).map (chartBasis G A).symm
lemma base_at (i : Z G A) : baseChart G A i=priv i := by unfold baseChart; rw [Module.Basis.map_apply,Pi.basisFun_apply]; exact from_chart i
lemma coord_at (i:Z G A) : (baseChart G A).coord i=(projector i).toLinearMap := by
  apply (baseChart G A).ext; intro j
  rw [show ((baseChart G A).coord i) _= ((baseChart G A).repr ((baseChart G A) j)) i from rfl,Module.Basis.repr_self,base_at, ContinuousLinearMap.coe_coe,coord_recover]; simp [Finsupp.single_apply,eq_comm]

/-- Prefer `coordinate` over Matrix writing for maps via Lot. -/
def coordinate (K : Links G P→ₗ[ℝ] Links G A) : Matrix (Z G A) (Z G P) ℝ :=
  LinearMap.toMatrix (baseChart G P) (baseChart G A) K

lemma coordinate_apply (K : Links G P →ₗ[ℝ] Links G A) (i j) : coordinate K i j = projector i (K (priv j)) := by
  unfold coordinate; rw [LinearMap.toMatrix_apply]; change (baseChart G A).coord i _=_; rw [coord_at,base_at]; rfl
lemma coordinate_inj : Injective (coordinate (G:=G) (P:=P) (A:=A)) := (LinearMap.toMatrix _ _).injective
lemma coordinate_id : coordinate (G:=G) (A:=A) (P:=A) LinearMap.id=1:= LinearMap.toMatrix_id ..
lemma coordinate_mul (K : Links G I →ₗ[ℝ] Links G A) (T : Links G P→ₗ[ℝ] Links G I) :
    coordinate (K ∘ₗ T) = coordinate K * coordinate T := by unfold coordinate; rw [LinearMap.toMatrix_comp _ (baseChart G I)]
lemma coordinate_add (K J:Links G P→ₗ[ℝ] Links G A) : coordinate (K+J)=coordinate K+coordinate J:=
  (LinearMap.toMatrix _ _).map_add K J
lemma coordinate_in (K : Links G P→ₗ[ℝ] Links G A) (j : Z G P) : K (priv j) = ∑ i, coordinate K i j • priv i := by
  simp_rw [coordinate_apply]; exact (Native.frame _).symm
lemma dGraph (R : FVA2.Ends A P) : coordinate (R.flow (0:Links G A))=gradientGraph R := by
  ext i j; rw [coordinate_apply]; rfl
lemma chart_dual_apply (K : Links G P→ₗ[ℝ] Links G A) (x : Links G P) (i : Z G A) :
    ∑ j:Z G P, coordinate K i j * projector j x = projector i (K x) := by
  conv_rhs => rw [← Native.frame x]; simp only [map_sum,map_smul]
  simp_rw [coordinate_apply,smul_eq_mul,mul_comm ((projector i) _)]

/-- Real-matrix transpose in the chart metric. -/
lemma chart_adj (K : Links G A→ₗ[ℝ] Links G P) (T:Links G P→ₗ[ℝ] Links G A)
    (h : ∀ (u:Links G A) v,(∑ i: Z G P, projector i (K u)* projector i v)=∑ i:Z G A,projector i u * projector i (T v)) :
    (coordinate K)ᵀ=coordinate T := by
  ext i j; specialize h (priv i) (priv j); simp [coord_recover,mul_ite,ite_mul] at h; simpa only [transpose_apply,coordinate_apply]
lemma coord_smul (K : Links G A→ₗ[ℝ] Links G P) (r:ℝ) : coordinate (r • K)=r • coordinate K :=
  map_smul (LinearMap.toMatrix _ _) r K
lemma coord_sub (K J:Links G P→ₗ[ℝ] Links G A) : coordinate (K-J)=coordinate K-coordinate J:=
  map_sub (LinearMap.toMatrix _ _) K J
lemma coord_zero : coordinate (A:=A) (P:=P) (G:=G) 0=0:= map_zero (LinearMap.toMatrix _ _)

/-- Transposing/substituting the cost Hessian. -/
lemma costs_comp (K:Links G P→L[ℝ] Links G A)(F:Links G A→ℝ) (h:germ F) :
    costMatrix (F ∘ K)=(coordinate K.toLinearMap)ᵀ * costMatrix F * coordinate K.toLinearMap := by
  let C:= coordinate K.toLinearMap
  ext x y
  calc
    _ = -layer (K (priv y)) (layer (K (priv x)) F) 0 := ?_
    _ = _ := ?_
  · unfold costMatrix; simp only [Matrix.of_apply]
    have heq := congr_fun (Taylor.ink_ctrl_one priv K h) [x,y]
    change -layer (priv y) (layer (priv x) (F∘ K)) 0=_
    exact congr_arg Neg.neg (Complex.ofReal_injective heq)
  have ht (y:Z G P) (j:Z G A) :
      layer (K (priv y)) (layer (priv j) F) 0 = ∑ i:Z G A,C i y * layer (priv i) (layer (priv j) F) 0 := by
    rw [show K _= _ from coordinate_in K.toLinearMap y]
    unfold layer; simp only [map_sum,map_smul]; rfl
  have hx : layer (K (priv x)) F =∑ i: Z G A, C i x • layer (priv i) F := by
    rw [show K _= _ from coordinate_in K.toLinearMap x]; funext i; simp only [layer,map_sum,map_smul,Finset.sum_apply]; rfl
  rw [hx, show layer _ (∑ i:Z G A, C i x • layer (priv i) F) 0 =
      ∑ i:Z G A,C i x * layer (K (priv y)) (layer (priv i) F) 0 from ?_]
  · simp_rw [ht y, Finset.mul_sum, ← Finset.sum_neg_distrib]
    nth_rw 1 [Finset.sum_comm]; simp_rw [Matrix.mul_apply, Finset.sum_mul,transpose_apply];
    apply Finset.sum_congr rfl; intro i hi; refine Finset.sum_congr rfl fun j _=>?_
    change -(C j x * (C i y * _)) = C j x * -(layer (priv i) (layer (priv j) F) 0)* C i y
    ring
  unfold layer; rw [fderiv_sum];
  · have hk (i:Z G A): DifferentiableAt ℝ (layer (priv i) F) 0:=
      (germ_layer h (priv i)).differentiableAt (by simp)
    change _= _
    simp only [_root_.sum_apply]; apply Finset.sum_congr rfl; intro i _
    change (fderiv ℝ (_ • layer (priv i) F) 0) _=_
    rw [fderiv_const_smul (hk i)]; rfl
  exact fun i _=> ((germ_layer h (priv i)).differentiableAt (by simp)).const_smul _
lemma costs_smul (F:Links G A→ℝ) (r:ℝ) (h:germ F) : costMatrix (r • F)=r • costMatrix F := by
  ext i j
  unfold costMatrix; simp only [Matrix.of_apply,Matrix.smul_apply,smul_eq_mul]
  rw [ Filter.EventuallyEq.fderiv_eq (scale_layers (priv i) h r),
    fderiv_const_smul ((germ_layer h (priv i)).differentiableAt (by simp))]
  simp

end YM.FVA2.ArrayMap
