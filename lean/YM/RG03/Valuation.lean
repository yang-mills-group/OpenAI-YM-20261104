import YM.RG03.Defects
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Increment degrees are tested on unmasked germs at the globally trivial field. The valuation of
our defect-product tails is a valuation of the actual nonlinear functions, not formal link tensors only. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG03
open Wilson RG Lattice Next.Scheduling.Wages Work.G07
open scoped ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n : Side}
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def incident (f : Config G n → E) : Directions G n → E := fun v=> f (increment 1 v)

def Vanishes (d : ℕ) (f : Config G n → E) :=
   ContDiff ℝ ∞ (incident f) ∧ ∀ j < d, iteratedFDeriv ℝ j (incident f) 0 = 0

namespace Vanishes
variable {a b : ℕ} {f g : Config G n → E} {h : Config G n → E}
lemma shorten (hf:Vanishes a f) (hab : b≤a) : Vanishes b f := ⟨hf.1,fun j hj=> hf.2 j (hj.trans_le hab)⟩
lemma flat (hf : Vanishes 1 f) : f 1=0 := by
  simpa [incident,at_zero_increment] using DFunLike.congr_fun (hf.2 0 Nat.zero_lt_one) ![]
lemma hessian (hf : Vanishes 3 (f:=h)) (x y : Directions G n) : iteratedFDeriv ℝ 2 (incident h) 0 ![x,y]=0 := by
  rw [hf.2 2 (by decide)]; simp
lemma affine {q : Config G n → ℝ} (hf:Vanishes 3 q) (x y:Directions G n) : logHessian q x y=0 := hf.hessian x y

lemma add (hf : Vanishes a f) (hg : Vanishes a g) : Vanishes a (fun U=> f U+g U) :=
    ⟨hf.1.add hg.1,fun j hj=> by
      rw [show incident (fun U => f U+g U) = incident f+incident g from rfl,
        iteratedFDeriv_add_apply (hf.1.contDiffAt.of_le (by exact_mod_cast le_top (a:=(j:ℕ∞)))) (hg.1.contDiffAt.of_le (by exact_mod_cast le_top (a:=(j:ℕ∞)))), hf.2 j hj,hg.2 j hj,add_zero]⟩
lemma negative (hf : Vanishes a f) : Vanishes a (fun U=> -f U) := ⟨hf.1.neg,fun j hj => by
   rw [show incident (fun U=> -f U) = -incident f from rfl,iteratedFDeriv_neg_apply, hf.2 j hj,neg_zero]⟩
lemma sub (hf : Vanishes a f) (hg : Vanishes a g) : Vanishes a (fun U=> f U-g U) := by
  simp_rw [sub_eq_add_neg]; exact hf.add hg.negative

lemma clm (hf : Vanishes a f) (L:E→L[ℝ] F) : Vanishes a (fun U=>L (f U)) := by
  rw [Vanishes,show incident _ = ⇑L ∘ incident f from rfl]
  refine ⟨L.contDiff.comp hf.1,fun j hj => ?_⟩
  apply norm_le_zero_iff.mp
  have h := L.norm_iteratedFDeriv_comp_left (n:=j) (x:=(0:Directions G n)) hf.1.contDiffAt (by exact_mod_cast le_top (a:=(j:ℕ∞)))
  exact le_trans h (by simp [hf.2 j hj])

lemma mul {f g: Config G n → A} (hf : Vanishes a f) (hg : Vanishes b g) : Vanishes (a+b) (fun U=> f U*g U) := by
  rw [Vanishes,show incident (fun U=> f U*g U) = (fun x=> incident f x*incident g x) from rfl]
  refine ⟨hf.1.mul hg.1,fun j hj => ?_⟩
  apply norm_le_zero_iff.mp
  apply (norm_iteratedFDeriv_mul_le hf.1 hg.1 (0:Directions G n) (n:=j) (by exact_mod_cast le_top (a:=(j:ℕ∞)))).trans
  exact Eq.le (Finset.sum_eq_zero fun i hi=> by
    have := Finset.mem_range.mp hi
    by_cases h : i<a
    · simp [hf.2 _ h]
    simp [hg.2 (j-i) (by omega)])
end Vanishes

variable (G)
lemma identity_travels (x : Site n) (w : Walk) : travel (1:Config G n) x w = 1 := by
  induction w generalizing x with
  | nil => rfl
  | cons w l ih => rw [travel,ih,mul_one]; unfold Step.read; split
                   · change (1:G.El)⁻¹=1; simp
                   rfl

-- No volume or chord estimate used here, even for signed steps.
lemma defect_vanish (o:Site n) (w:Circuit) : Vanishes 1 (w.defect (G:=G) o) := by
  rw [Vanishes,show w.defect (G:=G) o = fun v=>Path.eval (Path.tissue o w.path) v+(-1:G.Mat) from funext fun v=>by rw [Circuit.defect,Circuit.raw,Circuit.holonomy,Path.picture,sub_eq_add_neg]]
  have h := Path.soft (G:=G) (Path.tissue o w.path) 0 [] le_rfl (1:Config G n)
  refine ⟨h.add contDiff_const,fun j hj=> ?_⟩
  have : j=0 := Nat.eq_zero_of_le_zero (by omega)
  subst j; ext dirs
  dsimp [incident,iteratedFDeriv_zero_apply]; rw [at_zero_increment,←Path.picture, identity_travels, G.mat_one, add_neg_cancel]
  rfl
end YM.RG03
