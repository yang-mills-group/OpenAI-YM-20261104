import YM.MS.Color.Invol
import Mathlib.MeasureTheory.Group.Integral
/-!
# Averaging over actual G, pointwise in kernels

`momentSpan` only for finite-dimensional subspaces of functions on all momenta;
recover coefficients by finite sampling. Avoid implicit topologies on the polymer algebra.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Color
open Function Filter Set Finset Plane Koszul Real Momentum Wire Tensor Submodule MeasureTheory
open Landau Detect
open Complex (I)
open scoped Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {A P D E : Type} {F : Score G D P}
lemma momentSpan [MeasurableSpace E] (V : Submodule ℂ (A→ℂ)) [FiniteDimensional ℂ V]
    {f : E→A→ℂ} (μ : Measure E) (hp : ∀ i, Integrable (fun x=> f x i) μ) (h : ∀ x,f x∈V) : (fun i=>∫ x,f x i ∂μ)∈V:= by
   let F : E→ V:= fun x=> ⟨f x,h x⟩; let B:= Module.finBasis ℂ V; let L (j) := B.coord j
   have he x : F x = ∑ i,L i (F x) • B i:= (B.sum_repr _).symm
   have ht i: Integrable (fun x=> L i (F x)) μ:= by
       obtain ⟨s,p,hv⟩:=Local.point_recovery V (L i); simp_rw [hv]; exact integrable_finsetSum _ fun j _=> (hp j).const_mul _
   let U : V:= ∑ i,(∫ x,L i (F x) ∂μ) • B i
   have hu : (fun i=>∫ x,f x i ∂μ)=(U.val):= by
       ext i; have hv x : f x i= ∑ j,L j (F x)*(B j).val i:= by
           change V.subtype (F x) i=_; nth_rw 1 [he]; simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,subtype_apply]
       simp_rw [hv]; rw [integral_finsetSum _ (fun j _=> (ht j).mul_const _)]; unfold U; simp_rw [integral_mul_const]; simp
   rw [hu]; exact U.property

lemma color_cont (G : Gauge) (f:G.Color): Continuous fun k:G.El=>G.adjoint k f := by
   change Continuous (fun k:G.El=> G.projectColor (G.mat k * G.colorMat f * star (G.mat k)))
   exact G.projectColor.continuous_of_finiteDimensional.comp ((G.continuous_mat.mul continuous_const).mul (G.continuous_mat.star))
lemma weight_cont (i j : CI G) : Continuous fun k:G.El=>wc k i j:= Complex.continuous_ofReal.comp ((continuous_apply j).comp ((PiLp.continuousLinearEquiv 2 ℝ _).continuous.comp (color_cont G (eb G i))))

section ops
variable {j : G.El} {y : Type} [MeasurableSpace y] {μ : Measure y} {f : y → Score G D P}
lemma passes (he: ∀ i,Integrable (fun x=> f x i) μ) w : Integrable (fun x=>repeatC j (f x) w) μ:= by
    induction w generalizing f with
    | nil=> simp [he]
    | cons a v IH=> simp_rw [repeat_cons]; refine integrable_finsetSum _ (fun i _=> Integrable.const_mul (IH (fun k=> he (setLeg a i::k))) _)
lemma rep_integral (he: ∀ i,Integrable (fun x=> f x i) μ) w : repeatC j (fun i=>∫ x,f x i ∂μ) w=∫ x,repeatC j (f x) w ∂μ:= by
    induction w generalizing f with
    | nil=> simp
    | cons a v IH=>
        have hh i : repeatC j (Koszul.D (setLeg a i) (fun i=>∫ x,f x i ∂μ)) v=∫ x,repeatC j (Koszul.D (setLeg a i) (f x)) v ∂μ:= IH (f:=fun x=>Koszul.D (setLeg a i) (f x)) (fun k=>he (setLeg a i::k))
        simp_rw [repeat_cons,hh,← integral_const_mul]; exact Eq.symm (integral_finsetSum _ (by exact fun i _=> (passes (f:=fun x=> Koszul.D (setLeg a i) (f x)) (fun y=>he (setLeg a i::y)) v).const_mul _))
end ops
lemma point_cont (w): Continuous (fun j:G.El=>repeatC j F w):= by
    induction w generalizing F with
    | nil=> exact continuous_const
    | cons a w ih=> simp_rw [repeat_cons]; exact continuous_finsetSum _ fun i _=> (weight_cont ..).mul ih
lemma point_mass (w): Integrable (fun j:G.El=>repeatC j F w) G.probHaar:= Continuous.integrable_of_hasCompactSupport (point_cont _) (HasCompactSupport.of_compactSpace _)

def mean : Score G D P→ₗ[ℂ] Score G D P where
    toFun f w:= ∫ k,repeatC k f w ∂G.probHaar
    map_add' f g:= by ext w; simp_rw [map_add, Pi.add_apply, integral_add (point_mass w) (point_mass w)]
    map_smul' c f:= by ext w; simp_rw [map_smul, Pi.smul_apply, integral_smul]; rfl
lemma mean_def (w) : mean F w=∫ k,repeatC k F w ∂G.probHaar:=rfl
lemma mean_fixed (p : G.El): repeatC p (mean F)=mean F:= by
    ext w; rw [show repeatC p (mean F) w=_ from rep_integral (j:=p) (f:=fun j=>repeatC j F) (point_mass (F:=F)) w] -- binder j
    simp_rw [walk_comp]; exact integral_mul_right_eq_self (μ:=G.probHaar) (fun x=>repeatC x F w) p
lemma mean_identity (h : ∀ p:G.El,repeatC p F=F): mean F=F:= by ext w; rw [mean_def]; simp_rw [h]; simp
end YM.MS.Color
