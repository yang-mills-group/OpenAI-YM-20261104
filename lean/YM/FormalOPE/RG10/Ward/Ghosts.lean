import YM.FormalOPE.RG10.Ward.Proxies
import YM.Gauge.Casimir
import Mathlib.Algebra.Lie.Cochain
import Mathlib.Analysis.Calculus.VectorField

/-! # Minimal BRST for Wilson even gauge.

Physical sector has no antighost/b fields. Minimal (longitudinal) differential is just
Chevalley--Eilenberg of the even-site gauge algebra (use arbitrary test ghosts in that algebra
and alternating cochains, no claim constructing all BV orders or adjoining negative ghost number).
Equations will be imposed separately by exact Haar--Ward operations in this gauge-invariant
prescription. Do NOT identify this with the full BV/MSbar complex, including dimensions and
antifield-vs-contact conventions are obligations on that extension/comparison. This file is to
supply an exact (nonlinear link) Ward check on the algebra of *representatives* before or after
formal frame and OPE operations. Since we keep even group invariance (not just lie algebra) even
if disconnected, no cohomology spanning assumption needed for that identity. The bracket sign is
fixed by passive frame action. No hard restrictions on number of marked physical operators.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.InversionWard.BRST
open Gauge Lattice RG Wilson MeasureTheory Metric
open PertExtension PertExtension.Orb Function
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
open VectorField

variable {G : Gauge} {n : Side}

def ghost (G : Gauge) (n : Side) : Submodule ℝ (Site n → G.Color) where
  carrier := {f | ∀ k, f (-k)=f k}
  add_mem' a b k := by rw [Pi.add_apply, a k,b k]; rfl
  smul_mem' r _ f k := by rw [Pi.smul_apply, f k]; rfl
  zero_mem' k := rfl

namespace ghost

def bracket (x y : ghost G n) : ghost G n := ⟨fun v => G.ad (x.val v) (y.val v),
  fun k => congr_arg₂ (fun p q => G.ad p q) (show x.val (-k) = x.val k from x.property k) (show y.val (-k)=y.val k from y.property k)⟩

instance : LieRing (ghost G n) where
  bracket := bracket
  add_lie x y z := by
    apply Subtype.ext; funext k; change G.ad (_+_) _ = G.ad _ _ + G.ad _ _; rw [map_add]; rfl
  lie_add x y z := by
    apply Subtype.ext; funext k; change G.ad _ (_+_) = G.ad _ _ + G.ad _ _; rw [map_add]
  lie_self x := by
    apply Subtype.ext; funext k; apply G.colorMat_injective
    change G.colorMat (G.ad _ _) = G.colorMat 0; rw [colorMat_ad, sub_self, map_zero]
  leibniz_lie x y z := by
    apply Subtype.ext; funext k; apply G.colorMat_injective
    change G.colorMat (G.ad _ (G.ad _ _)) = G.colorMat (G.ad (G.ad _ _) _ + G.ad _ (G.ad _ _))
    simp only [map_add, colorMat_ad]; noncomm_ring

instance : LieAlgebra ℝ (ghost G n) where
  lie_smul t x y := by
    apply Subtype.ext; funext k
    change G.ad _ (t • _) = t • G.ad _ _; rw [map_smul]

@[simp] lemma value (x y : ghost G n) (v : Site n) : ((⁅x, y⁆ : ghost G n)).val v =
    G.ad (x.val v) (y.val v) := rfl
end ghost

variable (a c : ghost G n) (U : Config G n)

/-- We use the anti-action vector field, link-head contribution has MINUS sign. -/
def chi (t : ℝ) (k : Site n) := G.lieExp (t • -(a.val k))

lemma chi_even (t : ℝ) : evenAt (chi a t) := fun k => by
  unfold chi; rw [show a.val (-k)=a.val k from a.property k]

def curve (U : Config G n) (t) := Lattice.gauge (chi a t) U
@[simp] lemma curve_zero : curve a U 0 = U := by funext i; simp [curve, chi,Lattice.gauge]

-- matrix-level vector field and genuine direction calculations.
def spin (a : ghost G n) : ArrayOf G n →ₗ[ℝ] ArrayOf G n where
  toFun A i := A i * G.colorMat (a.val (i.1 + step i.2)) - G.colorMat (a.val i.1) * A i
  map_add' x y := by funext i; simp only [Pi.add_apply,mul_add,add_mul]; abel
  map_smul' r x := by funext i; simp only [Pi.smul_apply, RingHom.id_apply, smul_mul_assoc, mul_smul_comm, smul_sub]

lemma spin_add (u : ArrayOf G n) : spin (a+c) u = spin a u + spin c u := by
  funext i; unfold spin; simp only [LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_add, Pi.add_apply, map_add, add_mul,mul_add]; abel
lemma spin_smul (t : ℝ) (u : ArrayOf G n) : spin (t • a) u=t • spin a u := by
  funext i; unfold spin; simp only [LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_smul, Pi.smul_apply, map_smul, smul_mul_assoc, mul_smul_comm, smul_sub]

lemma angle (A : ArrayOf G n) : spin ⁅a,c⁆ A = spin c (spin a A)-spin a (spin c A) := by
  funext v; dsimp only [spin,LinearMap.coe_mk,AddHom.coe_mk, Pi.sub_apply]; simp only [ghost.value,G.colorMat_ad]; noncomm_ring

def moving (a : ghost G n) : ArrayOf G n →L[ℝ] ArrayOf G n := (spin a).toContinuousLinearMap

lemma brackets : VectorField.lieBracket ℝ (moving a) (moving c) = moving ⁅a,c⁆ := by
  funext x; unfold VectorField.lieBracket
  erw [(moving c).fderiv,(moving a).fderiv]; exact (angle a c x).symm

private lemma matrix_chi (A : G.Color) : HasDerivAt (fun t : ℝ => G.mat (G.lieExp (t • (-A))))
    (- G.colorMat A) 0 := by
  simpa [WardBin.left] using WardBin.matLeft_zero (-A) 1

lemma curve_deriv : HasDerivAt (fun t => InversionWard.image (curve a U t)) (spin a (InversionWard.image U)) 0 := by
  apply hasDerivAt_pi.mpr; intro i
  unfold InversionWard.image curve Lattice.gauge chi; simp_rw [mat_mul,mat_inv]
  have he (j) := matrix_chi (a.val j)
  convert! ((he i.1).mul_const (G.mat (U i))).mul (he (i.1+step i.2)).star using 1
  simp [G.colorMat_skew, spin]
  first|rfl|abel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : ArrayOf G n → E)
-- Fréchet version for checking nilpotence

def charge (a : ghost G n) (A : ArrayOf G n → E) (x) := (fderiv ℝ A x) (moving a x)

def response (F : Config G n → E) (U) := deriv (fun t => F (curve a U t)) 0

lemma smooth (h : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (charge a F) :=
  (h.fderiv_right (by simp)).clm_apply (moving a).contDiff

lemma check (h : ContDiff ℝ ∞ F) : response a (F ∘ InversionWard.image) = (charge a F) ∘ InversionWard.image := by
  funext x; unfold response charge; rw [Function.comp_apply];
  have he:=curve_deriv a x
  exact ((((h.differentiable (by simp) _).hasFDerivAt).comp_hasDerivAt_of_eq 0 he (by rw [curve_zero])).deriv)

lemma proxy_response {F : Config G n → ℝ} (h : Proxy F) : Proxy (response a F) := by
  obtain ⟨A,hA,rfl⟩:=h; exact ⟨_,smooth a A hA, BRST.check a A hA⟩

lemma commutator {f : Config G n → E} (h : Proxy f) : response a (response c f) - response c (response a f) = response ⁅a,c⁆ f := by
  obtain ⟨A,hA,rfl⟩:=h
  rw [check a A hA, check c A hA, check _ A hA, check a _ (smooth c A hA), check c _ (smooth a A hA)]
  funext U; dsimp only [charge, Function.comp_apply, Pi.sub_apply]; rw [← show lieBracket ℝ (moving a) (moving c) (InversionWard.image U) = moving ⁅a,c⁆ _ from congr_fun (brackets a c) _]
  exact (VectorField.fderiv_apply_lieBracket hA.contDiffAt (by rw [minSmoothness_of_isRCLikeNormedField]; decide) (moving c).differentiableAt (moving a).differentiableAt).symm
end YM.FormalOPE.RG10.InversionWard.BRST
