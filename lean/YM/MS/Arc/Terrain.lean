import YM.MS.RapidIntegration
import YM.MS.SymbolParts
/-!
# Dimension interpolation terrain at unit cost scale

Separate the exponential cost parameter from polynomial-in-d, and
 keep arbitrary smooth external tests. `∀i,Z` because radius local or compact.
 Integration over auxiliary dimensions later. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Arc
open Function Filter Set Finset MeasureTheory Real
open scoped Topology ContDiff
variable {I E F G H A B: Type}[NormedAddCommGroup E][NormedSpace ℝ E]
 [NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup G][NormedSpace ℝ G][NormedAddCommGroup H][NormedSpace ℝ H]
abbrev UScale (I:Type):= I→ℝ
def path (z: UScale I) : Scale I:= ⟨fun _=>1,fun _=>zero_lt_one,fun i=>1+|z i|,fun _=> le_add_of_nonneg_right (abs_nonneg _)⟩
-- abbrev to avoid namespace below
abbrev veg (z: UScale I)(f: I→ E→F) := Bound (path z) f
abbrev quiet (z: UScale I) (f:I→ E×F→G):= Rapid (path z) (fun _=>univ) f

variable {z:UScale I}{a b:I→ℝ}{f g:I→ E→F} {u v:I→ (E×F)→ G} 
@[simp] lemma cheap_length (z:UScale I)(i:I): (path z).length i=1:=rfl
omit [NormedSpace ℝ E] in
lemma g_cost (z:UScale I)(i:I) (p:E): (path z).full.cheap i p=(1+|z i|)*(1+‖p‖):= by simp [Scale.full, path, Scale.weight]
lemma terrain (h:veg z f a): ∀ i,0≤a i:=fun i=> h.nonneg i 0 (mem_univ (0:E))
lemma Q.fder (h:quiet z u a): quiet z (fun i=>fderiv ℝ (u i)) a:= by simpa only [cheap_length,mul_one] using h.fderiv
lemma Q.nonneg (h:quiet z u a): ∀ i, 0≤a i:=fun i=> h.nn i 0 (mem_univ _)
lemma Q.common (h:quiet z u a): veg z u a:= by
   refine ⟨h.smooth, fun j=>?_⟩
   have hP:=h 0; obtain ⟨C,hC,b,hb⟩:=hP.quoted j; refine ⟨C,hC,b,fun i p _=> (hb i p (mem_univ _)).trans ?_⟩
   have hn:=Q.nonneg h i; have hx:=(path z).basic_pos i; have hz:=(path z).weight_pos i p.2; have he:=(path z).pos i; dsimp only
   rw [pow_zero,div_one]; change C * ((path z).basic i *(path z).weight i p.2)^_ * _≤ C*((path z).basic i*(path z).weight i p)^_*_; rw [Scale.pair_w]; gcongr; simp

variable (S:Scale I)
-- normal form integer power estimates
lemma Q.man (h:quiet z u a)(j k:ℕ): ∃ C:ℝ,0<C∧∃ l:ℕ,∀ i p q, ‖iteratedFDeriv ℝ j (u i) (p,q)‖* (1+‖p‖)^k ≤ C*((1+|z i|)*(1+‖q‖))^l*a i := by
    obtain ⟨C,hC,l,hl⟩:=(h k).quoted j; refine ⟨C,hC,l,fun i p q=>?_⟩; specialize hl i (p,q) (mem_univ _); dsimp only [path,Scale.slow,Scale.full,Scale.weight] at hl; simp only [one_mul,one_pow,mul_one,← mul_div_assoc] at hl; exact (le_div_iff₀ (by positivity)).mp hl
lemma Q.fromM (hs:∀ i,ContDiff ℝ ∞ (u i))(h: ∀ j k:ℕ,∃ C:ℝ,0<C∧∃ l:ℕ,∀ i p q, ‖iteratedFDeriv ℝ j (u i) (p,q)‖* (1+‖p‖)^k≤ C*((1+|z i|)*(1+‖q‖))^l*a i): quiet z u a:= by
    refine fun k=> ⟨hs,fun j=>?_⟩; obtain ⟨C,hC,l,H⟩:=h j k; refine ⟨C,hC,l,fun i p _=>?_⟩; obtain ⟨p,q⟩:=p; dsimp only [path,Scale.slow,Scale.full,Scale.weight]; simp only [one_mul,one_pow,mul_one,← mul_div_assoc]; exact (le_div_iff₀ (by positivity)).mpr (H i p q)
lemma ride (h:veg z f a)(j:ℕ):∃ C:ℝ,0<C∧∃ b:ℕ,∀ i p,‖iteratedFDeriv ℝ j (f i) p‖ ≤ C*((1+|z i|)*(1+‖p‖))^b*a i:= by
    obtain ⟨C,hC,l,hl⟩:= h.quoted j; refine ⟨C,hC,l,fun i p=>?_⟩; simpa only [g_cost,cheap_length,one_pow,mul_one] using hl i p (mem_univ _)
lemma hike (hs:∀ i,ContDiff ℝ ∞ (f i))(h: ∀ j, ∃ C:ℝ,0<C∧∃ l:ℕ,∀ i p,‖iteratedFDeriv ℝ j (f i) p‖ ≤ C*((1+|z i|)*(1+‖p‖))^l*a i): veg z f a:= by
    refine ⟨hs,fun j=>?_⟩; obtain ⟨C,hC,l,hl⟩:=h j; refine ⟨C,hC,l,fun i p _=>?_⟩; simpa only [g_cost,cheap_length,one_pow,mul_one] using hl i p -- direction wrong simp
end YM.MS.Arc
