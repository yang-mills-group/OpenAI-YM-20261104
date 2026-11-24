import YM.SchemeConversionRG11.FirstMS.Triad.Coefficient
import YM.Pert.Triangle.Diagnostic

/-! Structure constants, placement polynomial. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.FirstMS.Triad
open Function Set Filter MeasureTheory Metric Complex DR Maxwell Maxwell.Free Pert.Triangle Analysis
open scoped Topology ContDiff BigOperators Classical InnerProductSpace Matrix.Norms.Frobenius

variable {G:Gauge}

lemma color_first (a b c:G.ColorIndex):colorF a b c= -colorF b a c := by
    have he(x y:G.Color): G.ad x y= -G.ad y x:= by apply G.colorMat_injective; simp
    unfold colorF; rw [he,inner_neg_left]
lemma color_second (a b c:G.ColorIndex):colorF a b c= -colorF a c b:= by
    unfold colorF; rw [Gauge.ad_skew]; exact congrArg Neg.neg (real_inner_comm ..)
-- C and V both use f in this full cyclic order
lemma color_rotate (a b c:G.ColorIndex):colorF a b c=colorF c a b:= by rw [color_second a b c,color_first a c b,neg_neg]
lemma color_loop (a:P→G.ColorIndex)(i:P): colorF (a i) (a (slide i)) (a (lag i))=colorF (a 0) (a 1) (a 2) := by
   fin_cases i; rfl; exact color_rotate ..; exact (color_rotate ..).symm

-- symmetry of summand coefficients; enumerate crossed & same-dual choices in F₀
-- without assigning extra boson permutation sign.
lemma epsilon_loop (w:P→Fin 3) (k:P) : eps3 (w k) (w (slide k)) (w (lag k))=eps3 (w 0) (w 1) (w 2):= by
   have he(a b c:P): eps3 a b c=eps3 c a b:=by rw [eps_swap23 a c b,eps_swap12 c a b,neg_neg]
   fin_cases k; rfl; exact he ..; exact (he ..).symm
lemma permute (w:P→Fin 3)(u:P→G.ColorIndex)(σ:Equiv.Perm P):
   (eps3 (w (σ 0)) (w (σ 1)) (w (σ 2)):ℝ)*colorF (u (σ 0)) (u (σ 1)) (u (σ 2))=(eps3 (w 0) (w 1) (w 2):ℝ)*colorF (u 0) (u 1) (u 2):=by
    rw [←epsilon_loop w (σ 0),←color_loop u (σ 0)]; have he₁ := (full_order (σ 0) (σ 1)).resolve_left (σ.injective.ne (by decide)); have he₂ := (full_order (σ 0) (σ 2)).resolve_left (σ.injective.ne (by decide)); have hk:σ 2≠σ 1:=σ.injective.ne (by decide)
    rcases he₁ with he|he <;> rcases he₂ with hr|hr <;> rw [he] at hk ⊢ <;> rw [hr] at hk ⊢ <;> try contradiction
    rw [eps_swap23,color_second]; push_cast; ring

end YM.SchemeConversionRG11.FirstMS.Triad
