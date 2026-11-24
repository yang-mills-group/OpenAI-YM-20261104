import YM.MSbar.Dim.MellinLift
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Ambient *real* orthogonal space of hats in even dimensions. Every assembly comparison uses
true linear isometries, no interpolation of Taylor coefficients at integer ε. Pair dimensions
just makes the radial convolution argument nicer. -/

set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Dim
open Function Set Filter MeasureTheory Metric Symbol Submodule
open scoped Topology InnerProductSpace ContDiff BigOperators Classical

abbrev Hat (m : ℕ) := EuclideanSpace ℝ (Fin (2*m))
-- helper plane as Hat1
abbrev Plane := Hat 1
def axis : Plane:= EuclideanSpace.basisFun (Fin (2*1)) ℝ (0 : Fin (2*1))
theorem axis_norm : ‖axis‖=1:= (EuclideanSpace.basisFun (Fin (2*1)) ℝ).norm_eq_one 0

@[simp] lemma hat_dim (m) : Module.finrank ℝ (Hat m)=2*m:=finrank_euclideanSpace_fin

variable {m n : ℕ}
abbrev Move (m n : ℕ) := Hat m →ₗᵢ[ℝ] Hat n
lemma aligns (V W : Move m n) : ∃ F : Hat n ≃ₗᵢ[ℝ] Hat n, ∀ x,F (V x)=W x:=by
   let e:= V.equivRange
   let L: (LinearMap.range V.toLinearMap) →ₗᵢ[ℝ] Hat n:= W.comp e.symm.toLinearIsometry
   exact ⟨L.extend.toLinearIsometryEquiv rfl,fun x=> by change L.extend ((e x).val)=_; rw [LinearIsometry.extend_apply]; change W (e.symm (e x))=_; rw [LinearIsometryEquiv.symm_apply_apply]⟩
lemma norm_action {E:Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {x y:E} (h:‖x‖=‖y‖) : ∃ U:E≃ₗᵢ[ℝ] E,U x=y:= ⟨reflection (ℝ ∙ (x-y))ᗮ, Submodule.reflection_sub h⟩

-- any fixed assembly dictionary
def assemble (m n t : ℕ) (h:m+n=t) : WithLp 2 (Hat m × Hat n) ≃ₗᵢ[ℝ] Hat t:=by
   let b:= stdOrthonormalBasis ℝ (WithLp 2 (Hat m × Hat n));let c:=stdOrthonormalBasis ℝ (Hat t)
   have hE : Module.finrank ℝ (WithLp 2 (Hat m × Hat n))=Module.finrank ℝ (Hat t):=by
       rw [(WithLp.linearEquiv 2 ℝ (Hat m × Hat n)).finrank_eq]; simp [← h,Module.finrank_prod,Nat.mul_add]
   exact (b.reindex (finCongr hE)).equiv c (Equiv.refl _)

def grow (m:ℕ): (Hat m × Plane) ≃L[ℝ] Hat (m+1):= (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.trans (assemble m 1 (m+1) rfl).toContinuousLinearEquiv
lemma grow_eq (y : Hat m × Plane) : grow m y=assemble m 1 _ rfl (WithLp.toLp 2 y):=rfl
lemma grow_sq (y : Hat m × Plane) : ‖grow m y‖^2=‖y.1‖^2+‖y.2‖^2:= by rw [grow_eq, LinearIsometryEquiv.norm_map];exact WithLp.prod_norm_sq_eq_of_L2 _

def up (m:ℕ) : Move m (m+1):=
 { (grow m).toLinearEquiv.toLinearMap.comp (LinearMap.inl ℝ (Hat m) Plane) with
     -- replace
     norm_map' x := by
        change ‖grow m (x,0)‖=‖x‖; apply (sq_eq_sq₀ (by positivity) (by positivity)).mp; simp [grow_sq] }

@[simp]lemma up_is (x:Hat m) : up m x=grow m (x,0):=rfl
lemma grow_inner (x y:Hat m × Plane) : ⟪grow m x,grow m y⟫_ℝ= ⟪x.1,y.1⟫_ℝ + ⟪x.2,y.2⟫_ℝ:=by rw [grow_eq,grow_eq, LinearIsometryEquiv.inner_map_map]; exact WithLp.prod_inner_apply ..
lemma bearing (m:ℕ) : MeasurePreserving (grow m) := ((assemble m 1 _ rfl).measurePreserving).comp (WithLp.volume_preserving_toLp (Hat m) Plane)
lemma spin_growth (L:Hat m ≃ₗᵢ[ℝ] Hat m) (P:Plane ≃ₗᵢ[ℝ] Plane) : ∃ W: Hat (m+1)≃ₗᵢ[ℝ] Hat (m+1),∀ x : Hat m×Plane,W (grow m x)=grow m (L x.1,P x.2):=by
   let A:= assemble m 1 _ rfl
   refine ⟨A.symm.trans ((LinearIsometryEquiv.withLpProdCongr 2 L P).trans A),fun u=> ?_⟩
   change A ((LinearIsometryEquiv.withLpProdCongr 2 L P) (A.symm (A _))) = A _; rw [LinearIsometryEquiv.symm_apply_apply]; rfl
end YM.MSbar.Dim
