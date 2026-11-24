import YM.FVA2.Wick.Analytic
import YM.PertExtension.Uniform
import Mathlib.Analysis.Analytic.IteratedFDeriv
/-!
# A homogeneous `Papers` jet is literally the rank-cut MS Taylor table

No inverse-rank step assumption: differentiate the actual analytic germs in arbitrary real color
coordinates. A rank-k component is the table of the kth homogeneous Taylor polynomial, all these
use the same origin and linear coordinates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Wick.Gem
open Function Set Finset Filter
open MS MS.Koszul MS.Plane MS.Orbit MS.Orbit.Cog MS.Swirl MS.Book Convolve MS.Cylinder Taylor
open Formal (overlay)
open PertExtension.Series.Radial
open scoped BigOperators Topology ContDiff
variable {E A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma jet_layer {f:E→ℝ}(h:germ f)(x:E)(k:ℕ): layer x (jet f (k+1)) = jet (layer x f) k := by
  let l (y : E) := fun _ : Fin (k+1)=> y
  let L : E→L[ℝ] (Fin (k+1)→E):= ContinuousLinearMap.pi (fun _=> ContinuousLinearMap.id ℝ E)
  let F := iteratedFDeriv ℝ (k+1) f 0; let c := ((k+1).factorial:ℝ)⁻¹; let w y:=Function.update (l y) (Fin.last k) x
  funext y
  have hz (i : Fin (k+1)) : F (Function.update (l y) i x) = F (w y) := by
    let J:= Equiv.swap i (Fin.last k)
    rw [← h.iteratedFDeriv_comp_perm (w y) J]; congr! 1
    · unfold w
      funext j; by_cases he : j=i
      · subst he; simp [J]
      by_cases hk:j=Fin.last k
      · subst j; simp [J,Function.update_of_ne, he, Ne.symm he,l]
      rw [comp_apply,Equiv.swap_apply_of_ne_of_ne he hk]; simp [he,hk]
  let q := (fderiv ℝ f)
  let C := ContinuousLinearMap.apply ℝ ℝ x
  have hp : F (w y) = iteratedFDeriv ℝ k (C ∘ q) 0 (fun _=>y):= by
    unfold F
    rw [iteratedFDeriv_succ_apply_right, C.iteratedFDeriv_comp_left (h.fderiv_right (m:=ω) (by simp)) (by exact le_top)]
    have hw : Fin.init (w y) = fun _=> y := by
      funext i; unfold Fin.init w l; rw [Function.update_of_ne (Fin.castSucc_ne_last i)]
    rw [hw,show w y (Fin.last k)=x from Function.update_self ..]; rfl
  have ha := ((F.hasFDerivAt (L y)).comp y L.hasFDerivAt).const_smul c
  change fderiv ℝ (fun i=> c * F (l i)) y x= _
  rw [show fderiv ℝ (fun i=> c * F (l i)) y = _ from ha.fderiv]
  rw [_root_.smul_apply, ContinuousLinearMap.comp_apply]
  change c * F.linearDeriv (l y) (l x)= _
  rw [ContinuousMultilinearMap.linearDeriv_apply]; unfold jet; change c * (∑ i:Fin (k+1), F (Function.update (l y) i x))=((k.factorial:ℝ)⁻¹)*iteratedFDeriv ℝ k (C ∘ q) 0 (fun _=> y); simp_rw [hz,hp]; simp only [Finset.sum_const, Finset.card_univ,Fintype.card_fin, nsmul_eq_mul]; unfold c; rw [Nat.factorial_succ]; push_cast; field_simp

lemma ranked (e:A→E) (f:E→ℝ)(k:ℕ)(h:germ f) : letter e f k= ink e (jet f k):= by
  induction k generalizing f with
  | zero=> rw [first, show jet f 0=fun _=> f 0 from funext fun x=> jet_zero .., ink_const]
  | succ k ih=>
    apply ext_D
    · have he : jet f (k+1) 0=0:= by rw [← show (0:ℝ) • (0:E)=0 from zero_smul ..,jet_smul, zero_pow (by omega),zero_mul]
      rw [letter,strange _ (by simp; omega), drip,he, Complex.ofReal_zero]
    intro i; unfold letter; rw [Book.conn, inktip,inktip, jet_layer h, show ((k+1:ℕ):ℤ)-1=k from (by omega)]; exact ih _ (germ_layer h _)
end YM.FVA2.Wick.Gem
