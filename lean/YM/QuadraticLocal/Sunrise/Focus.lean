import YM.QuadraticLocal.Sunrise.Heat
import Mathlib.LinearAlgebra.Vandermonde
/-!
# Project one copy of each SELECTED spurion, at all permitted torus scales

Weight `η`: finite-dimensional coefficient deriv. No assumption of actual budget.Location.D
 applied to price.Combined.Dec.E. tag probe polynomial. Handle any fixed marker family,
 not rough claim over arbitrary copy count. Also port true interps with V.Low.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Sunrise
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function AllOrder AllOrder.Fire AllOrder.Laplace AllOrder.Laplace.SigmaP AllOrder.Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response AllOrder.Ink AllOrder.Ink.Method GaussianScore Module Push
open scoped BigOperators Topology Classical ContDiff
variable {G: Gauge} {n m:Side}
variable {ι α β:Type}[Fintype α][Fintype β][Fintype ι][DecidableEq ι] (T:Finset ι)
variable {s : ℕ} {a C D:ℝ}
namespace Focus
abbrev Root (k:ℕ):=Fin (k+2)
def dayV (k:ℕ)(i:Root k): ℝ:= i.val
local notation "pt"=>dayV
local notation "ν" k:max => Matrix.vandermonde (dayV k)
def sign (T:Finset ι)(i:ι)(k:ℕ): Root k:= if i∈T then ⟨1, by omega⟩ else 0
def song (i:ι)(k:ℕ)(j:Root k):= (ν k)⁻¹ (sign T i k) j
abbrev Assignment (ι:Type) (k:ℕ) := ι→ Root k
variable (k:ℕ)
local notation "Λ"=> Assignment ι k
local notation "J"=> ((α⊕ι))
def cap (i:Λ):ℝ:= ∏ j:ι,song T j k (i j)
private lemma one' : IsUnit (ν k).det := isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr (by intro i j h; apply Fin.ext; unfold dayV at h; exact_mod_cast h))
lemma timing (i:ι)(t:ℕ)(h:t≤k) : (∑ j:Root k,song T i k j*(pt k j)^t)= if (t=(sign T i k).val) then 1 else 0:= by
 let T': Root k:=⟨t,by omega⟩; let R:=sign T i k; change (∑ j:Root k,(ν k)⁻¹ R j * (ν k) j T')=_; rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul (ν k) (one' k), Matrix.one_apply]; split; next ht=> have hc:(sign T i k).val=t:=congr_arg Fin.val ht; exact (if_pos hc.symm).symm
 next he=> exact (if_neg (show t ≠ _ from fun h=> he (Fin.ext h.symm))).symm
-- eval with all scaleProbe at q then survey pigments.Seeds.
local notation "U"=> rule (α⊕ι) n
def which (v:ι→ℝ)(i:α⊕ι) := i.elim (fun _=>1) v
def sustain (f:ι→ℝ) : rule (α⊕ι) n →L[ℝ] rule (α⊕ι) n:= ContinuousLinearMap.pi fun i=> which f i.2 • ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _=>ℝ) i
lemma look_at (f:ι→ℝ)(v:U)(x: Leaf n (J)): sustain f v x= which f x.2 * v x:=rfl
local notation "σ"=> sustain (α:=α) (n:=n)
local notation "mom" i:max=> pt k ∘ (i:Λ)
def lens (f:U→ℝ) : U→ℝ:=∑ w:Λ, cap T k w • (f ∘ (σ (mom w)))
lemma billK (f:U→ℝ)(x:U): lens T k f x= ∑ w:Λ,(cap T k w)*f ((σ (mom w)) x):= Finset.sum_apply ..
local notation "β'"=> (k+1:ℕ)
lemma height (v:Λ)(x:U): ‖(σ (mom v)) x‖ ≤ (β':ℝ)* ‖x‖:= by
 apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro i; rw [look_at,norm_mul]; refine mul_le_mul ?_ (norm_le_pi_norm ..) (norm_nonneg _) (by positivity); rcases i with ⟨w,i|i⟩
 · rw [show which (mom v) (Sum.inl i)=1 from rfl,norm_one]; exact Nat.one_le_cast.mpr (by omega)
 change |dayV k (v i)| ≤ _; unfold dayV; rw [abs_of_nonneg (by positivity)]; exact_mod_cast (by omega : (v i).val ≤ k+1)
def interest:= ∑ w:Λ, |cap T k w| *((β':ℝ)^k)
lemma asset :0 ≤ interest T k:= sum_nonneg fun i _=> by positivity
lemma fee {f:U→ℝ}(H:Prices k C f): Prices k (interest T k * C) (lens T k f):= by
 let f'(u:Λ):= f ∘ sustain (α:=α) (mom u); have hh u:Prices k ((β':ℝ)^k*C) (f' u):= by
    have h : 0≤C:= H.1; refine ⟨by positivity,H.2.1.lead (sustain ..),fun x=> (H.2.2 ((sustain (mom u)) x)).trans ?_⟩; calc
       _ ≤ C * (((β':ℝ))*roi x)^k:= by refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ k) h; unfold roi; rw [mul_add,mul_one]; exact add_le_add (by exact_mod_cast (show 1≤β' by omega)) (height k u x)
       _ = _:= by rw [mul_pow]; ring
 refine price_mono (price_sum (S:=Finset.univ) (fun w _=> price_scale (hh w) (cap T k w))) ?_; unfold interest; simp_rw [sum_mul,mul_assoc]; rfl
-- Linear lens Point.
lemma union (f g:U→ℝ) : lens T k (f+g)=lens T k f+lens T k g:= by funext x; simp_rw [Pi.add_apply, billK, Pi.add_apply, mul_add, Finset.sum_add_distrib] -- second simp_rw duplicate? rewrite duplicate unused errors
lemma scale (f:U→ℝ)(z:ℝ) : lens T k (z•f)= z • lens T k f:= by funext x; simp_rw [Pi.smul_apply, smul_eq_mul,billK,Pi.smul_apply,smul_eq_mul, Finset.mul_sum]; refine Finset.sum_congr rfl fun j _=>?_ ; ac_rfl
lemma less (f g:U→ℝ): lens T k (f-g)=lens T k f-lens T k g:= by rw [sub_eq_add_neg,← neg_one_smul ℝ g, Focus.union, Focus.scale, neg_one_smul,sub_eq_add_neg]; -- .1 order
-- Verify impulse.L Mark.Data.S.Vertex gauge purchases after.Time.Lens normalization.
end Focus
end YM.QuadraticLocal.Sunrise
