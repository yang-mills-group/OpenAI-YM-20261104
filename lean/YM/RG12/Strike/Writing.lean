import YM.RG12.Strike.Rocks
import Mathlib.Analysis.InnerProductSpace.Calculus
/-! # Separated derivatives of the contracted potential line on real dimension four

Compute in Euclidean coordinates with one normalized potential propagator `1/x²`,
not a distribution or analytic regularization. Derivatives with respect to displacement,
all fixed orders excluding coincidence. Only numerator at highest degree in unit-circle x
needed (lower charge licensed arbitrary).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Strike
open Function Set Filter MeasureTheory Real
open scoped Topology InnerProductSpace ContDiff BigOperators Classical
abbrev palette (i:Axis4)(x:R)(s:ℝ):R:=x+s • bar i
abbrev hit (i:Axis4)(f:R→ℂ)(x:R):ℂ:= deriv (f ∘ palette i x) 0
abbrev blue (i:Axis4)(f:R→ℂ)(x:R):Prop:=DifferentiableAt ℝ (f ∘ palette i x) 0
-- cast real displacement norm square to complex
abbrev black (x:R):ℂ:= ↑(‖x‖^2:ℝ)
structure Stroke where
   weight : ℂ
   rate : ℕ
   deck : Cells
def drip (L:Stroke)(x:R):ℂ:= L.weight * (black x ^ L.rate)⁻¹ * sun L.deck x
def scripts (A:List Stroke)(x:R):ℂ := (A.map (fun i=>drip i x)).sum
lemma scripts_step (A:List Stroke)(a:Stroke)(x:R): scripts (a::A) x=drip a x + scripts A x:=rfl
lemma scripts_swing (A B:List Stroke)(x:R): scripts (A++B) x=scripts A x+scripts B x:=by simp [scripts]

def pluck (i:Axis4): Cells→ List Cells
 | []=>[]
 | a::l => if a=i then l::(pluck i l).map (List.cons a) else (pluck i l).map (List.cons a)
lemma trims (i:Axis4)(l:Cells): ∀ p∈ pluck i l,p.length< l.length:=by
   induction l with
   | nil=> simp [pluck]
   | cons a b he=>
     intro p h; rw [pluck] at h; split at h
     · rw [List.mem_cons] at h; rcases h with rfl|h; simp; obtain ⟨p,hq,rfl⟩:=List.mem_map.mp h; simp [he p hq]
     obtain ⟨p,hq,rfl⟩:=List.mem_map.mp h; simp [he p hq]
lemma strike_leaf (i:Axis4)(j:Axis4)(x:R): HasDerivAt (fun t:ℝ=> (palette i x t j:ℂ)) (if j=i then 1 else 0) 0:=by
   simp_rw [←project]; unfold palette; simp only [inner_add_right,real_inner_smul_right,dot_bar]
   by_cases h:j=i <;> simp only [h, ↓reduceIte,mul_one,mul_zero,Complex.ofReal_add,add_zero];
   · have he:= (hasDerivAt_const (0:ℝ) (⟪bar i,x⟫_ℝ:ℂ)).add (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (0:ℝ) (hasDerivAt_id' (x:=(0:ℝ))))
     simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one,zero_add] using! he -- fix. hasDerivAt_ofReal via Complex.ofRealCLM
   exact hasDerivAt_const ..
lemma cast_deriv (f:ℝ→ℝ){f' x:ℝ}(he:HasDerivAt f f' x):HasDerivAt (fun v:ℝ=>(↑(f v):ℂ)) (↑f':ℂ) x:= Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x he
lemma strike (i:Axis4)(L:Cells)(x:R) : HasDerivAt (sun L ∘ palette i x) (((pluck i L).map (fun p=>sun p x)).sum) 0:=by
   induction L with
   | nil=> simpa [sun_nil,pluck,Function.comp_def] using (hasDerivAt_const (0:ℝ) (1:ℂ))
   | cons a t he=>
     simp_rw [Function.comp_def,sun_step, pluck]
     let A :ℂ:=(if a=i then 1 else 0)
     let D:ℂ:=((pluck i t).map (sun · x)).sum; have hj: HasDerivAt (fun t:ℝ=>(palette i x t a:ℂ)) A 0:= strike_leaf ..
     have ht:= hj.mul he
     have hh(T:List Cells) : ((T.map (List.cons a)).map (sun · x)).sum = (x a:ℂ)* (T.map (sun · x)).sum:=by
       induction T with
       | nil=>simp
       | cons b B hi=>simp only [List.map_cons,List.sum_cons,sun_step,hi];ring
     have hy:palette i x (0:ℝ)=x:=by unfold palette; simp
     convert ht using 1 <;> try rfl
     -- only derivatives mismatch
     dsimp only [Function.comp_apply]; rw [hy]; by_cases hc:a=i<;> simp only [A,hc,if_true,if_false, one_mul,zero_mul,List.map_cons,List.sum_cons];
     · rw [hc] at hh; rw [hh]
     rw [hh,zero_add]

lemma fade_black (i:Axis4)(x:R):HasDerivAt (black ∘ palette i x) (2 * (x i:ℂ)) 0 := by
   let f:R:=bar i
   have he: HasDerivAt (palette i x) f (0:ℝ):=by
      have hf : HasDerivAt (fun s:ℝ=> s • f) ((1:ℝ) • f : R) 0:=(hasDerivAt_id' (x:=(0:ℝ))).smul_const f -- ambiguous one type
      simpa only [one_smul] using! hf.const_add x -- syntax
   have h:= he.norm_sq; -- derivative type real
   have hx:= cast_deriv (fun s :ℝ=> ‖palette i x s‖^2) h
   change HasDerivAt (fun s : ℝ=>(↑(‖palette i x s‖^2:ℝ):ℂ)) _ _
   convert hx using 1
   simp only [palette,zero_smul,add_zero, f]; rw [real_inner_comm,project]; push_cast; rfl
variable (i:Axis4)(x:R)
-- derivative diagram at one leg
def flourish (i:Axis4)(L:Stroke):List Stroke:=
    (Stroke.mk (-(2*L.rate)*L.weight) (L.rate+1) (i::L.deck))::
       (pluck i L.deck).map (fun p=> Stroke.mk L.weight L.rate p)

lemma negative (k:ℕ)(he:x≠0): HasDerivAt ((fun z=>(black z ^ k)⁻¹) ∘ palette i x)
    (-(2*k)*(black x ^ (k+1))⁻¹*(x i:ℂ)) 0:=by
   have hp:black x ≠ 0:= by unfold black;exact_mod_cast (show (‖x‖^2:ℝ) ≠ 0 from pow_ne_zero _ (norm_ne_zero_iff.mpr he))
   -- inv over C under real diff: inv' ? HasDerivAt.fun_inv ℝ ℂ? Comm division Algebra, Mathlib
   -- rw [← Function.comp_def] -- change via real reciprocal
   have hA : HasDerivAt (fun s:ℝ=> ‖palette i x s‖^2) (2*x i) (0:ℝ):=by
      -- using real eq above
      have hf := Complex.reCLM.hasFDerivAt.comp_hasDerivAt _ (fade_black i x)
      simpa only [Function.comp_def, Complex.reCLM_apply, black, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, mul_zero,sub_zero,Complex.re_ofNat] using! hf
   have hxBlack:(palette i x) 0=x:=by unfold palette;simp
   have hz : ‖palette i x 0‖^2≠0:=by rw [hxBlack]; positivity [norm_pos_iff.mpr he] -- not zero
   have hh := cast_deriv (fun s:ℝ=>((‖palette i x s‖^(2:ℕ))^k)⁻¹) ((hA.pow k).inv (pow_ne_zero _ hz))
   convert hh using 1
   · ext1 s; simp [black]
   simp only [Pi.pow_apply]; rw [hxBlack]; unfold black at *; push_cast at *
   cases k with
   | zero=>simp
   | succ j=>
     -- rewrite powers then field
     simp only [Nat.add_sub_cancel, pow_add _ j 1, pow_succ]
     field_simp
     try ring
lemma changeAt (L:Stroke)(he:x≠0): HasDerivAt (drip L ∘ palette i x) (scripts (flourish i L) x) 0:=by
   have hf:= (hasDerivAt_const (0:ℝ) L.weight).mul (negative i x L.rate he)|>.mul (strike i L.deck x)
   let w:=L.weight * (black x ^ L.rate)⁻¹
   have hl (T:List Cells) :scripts (T.map (fun p=>Stroke.mk L.weight L.rate p)) x=w* (T.map (sun · x)).sum:=by
       induction T with
       | nil=>simp [scripts]
       | cons a b hx=> simp only [List.map_cons,List.sum_cons,scripts_step,hx,drip,w]; ring
   convert hf using 1 <;> try rfl
   have hx:palette i x 0=x:=by unfold palette; simp
   rw [flourish,scripts_step,hl]; unfold drip; dsimp only [Function.comp_apply, Pi.mul_apply]; rw [sun_step,hx]; unfold w; ring
end YM.RG12.Strike
