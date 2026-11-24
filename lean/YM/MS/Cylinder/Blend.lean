import YM.MS.Cylinder.Ink
import Mathlib.Analysis.Complex.Basic

/-!
# Change the directions linearly on a stencil

Real-valued jets, projected to matrix elements if desired. Ordinary (not odd).
No Jacobian or analyticity uniform assumptions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Cylinder.Taylor
open Function Filter Set Finset Koszul
open scoped Topology ContDiff
variable {A B E X : Type*}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup X][NormedSpace ℝ X]
variable {p:Sector A}

lemma timesC (c:ℝ) (f:Raw A ℂ): c • f=(c:ℂ) • f:= rfl
lemma scale_pos [Fintype A] {f:E→ℝ} (V:A→E) (W:B→E) (T:B→A→ℝ)(hf:∀ i,W i=∑ j, T i j • V j)(he:germ f):
    ink W f= shade (fun i j=>(T i j:ℂ)) (region.symm (ink V f)):= by
   funext l; induction l generalizing f with
   | nil=> simp only [shade_nil,drip]; rfl
   | cons i l ih=>
      let G:Cyl A ℂ:=region.symm (ink V f); have hx : Uses (↑(Finset.univ (α:=A)):Set A) G.val:= by rw [Finset.coe_univ]; exact Uses.entire _
      have hh (j:A): enter j G=region.symm (ink V (layer (V j) f)):= Subtype.ext (inktip ..)
      rw [deriv_lum _ i (region.symm (ink V f)) hx, D_eval i (ink _ _),inktip, show layer (W i) f=∑ j:A,T i j • layer (V j) f by ext x; rw [hf]; simp [layer]]; rw [ink_sum _ _ (fun j _=> show germ (T i j • layer _ _) from (germ_layer he (V j)).const_smul (T i j)),Finset.sum_apply]
      apply Finset.sum_congr rfl; intro j _; rw [show enter j (region.symm (ink V f))=_ from hh j, ink_smul, Pi.smul_apply,ih]; rfl; exact germ_layer he _; exact germ_layer he _
lemma ferry_pulls [Fintype A] (U:A→E) (V:B→E)(r:A→B)(hf:∀ i, V i=∑ j,way r i j (R:=ℝ) • U j) {f:E→ℝ}(h:germ f): ink V f=(Ferry r (region.symm (ink U f))).val:= by
    rw [scale_pos U V (way r (R:=ℝ)) hf h,sailed,show (fun (i:B)(j:A)=> (way r i j (R:=ℝ):ℂ))=way r by
       funext i j; by_cases hh:i=r j; subst i; simp [only r j]; simp [need _ hh]]
-- conjugation real jets
lemma uncoloured (e:A→E)(f:E→ℝ)(w:List A): star (ink e f w)=ink e f w:= by induction w generalizing f with| nil=>simp| cons i l ih=> exact ih (layer (e i) f)
end YM.MS.Cylinder.Taylor
