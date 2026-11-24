import YM.SchemeRG11.Flock.Value
/-! Global color on open terms. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Outlook
open Function Lattice Pert Maxwell Flock Bare Tree Bark Haze Pile Atoll Crest Labels MvPolynomial RawLabels
open scoped Classical Matrix.Norms.Frobenius
variable {G:Gauge} {n d w:ℕ}
def recolor (u:G.El)(A:trunk G ℤ): trunk G ℤ:= G.adjoint u ∘ A
lemma tint_stops(u:G.El)(s:Signed)(A:trunk G ℤ): wideLink G s (recolor u A)=recolor u (wideLink G s A):=by funext i; rw [wideLink_apply]; unfold recolor; simp only [comp_apply,wideLink_apply,map_smul]
lemma ad_p (u:G.El)(d c:G.Color): G.adjoint u (G.ad c d)=G.ad (G.adjoint u c) (G.adjoint u d):=by
 apply G.colorMat_injective; simp [Gauge.conjugate,sub_mul,mul_sub,mul_assoc]
 simp_rw [← mul_assoc (star (G.mat u)), G.mat_star_mul,one_mul]
lemma roll_color (u:G.El)(q:Step)(z:Cover)(A:trunk G ℤ): heel q z (recolor u A)=G.adjoint u (heel q z A):=by unfold heel recolor; split; exact (map_neg ..).symm; rfl
lemma mileC (u:G.El)(w:Walk)(A:trunk G ℤ)(x:Cover): mileage x w (recolor u A)=G.adjoint u (mileage x w A):=by induction w generalizing x with
 | nil=> simp [mileage]
 | cons q t ih=> rw [mileage,mileage,ih,map_add,roll_color]
lemma cohort_p (u:G.El)(w:Walk)(A B:trunk G ℤ)(x:Cover):cohort x w (recolor u A) (recolor u B)=G.adjoint u (cohort x w A B):=by induction w generalizing x with
 | nil=> simp [cohort]
 | cons q t ih=> rw [cohort,cohort,roll_color,mileC,ih,map_add,ad_p]
lemma plodding (b:Bool)(x:Cover)(u:G.El)(A B:trunk G ℤ)(j:ℕ): starJet b 1 x j (recolor u A) (recolor u B) = Taylor.paint u (starJet b 1 x j A B):=by
 simp only [starJet,map_smul, _root_.map_sum]; congr 1; apply Finset.sum_congr rfl; intro s _; unfold style; rw [Taylor.turn_paint,map_smul,tint_stops,tint_stops]
 have ht i(a B:trunk G ℤ): Bark.part b i j (recolor u a) (recolor u B) = fun f w γ=> G.adjoint u (Bark.part b i j a B f w γ):=by funext f w γ; unfold Bark.part; cases b <;> simp only [map_smul,map_sum,angle,Bool.false_eq_true, ite_false,ite_true,mileC,cohort_p]
 rw [ht]; simp only [one_zpow,one_smul]; congr 1; exact radial_color ..
lemma soul_color (u:G.El)(A:trunk G ℤ): soul (recolor u A)=colored u (soul A):=by funext m; unfold soul colored; simp_rw [←secular 1 (0:Cover) m (recolor u A) (recolor u A),plodding false 0 u A A m, secular]
lemma lump_tu (x:Sky G n→ℝ)(u:G.El): lump (aloft n x u)=recolor u (lump x):=by
 funext i; unfold lump recolor; simp only [comp_apply, Fintype.sum_prod_type, map_sum,map_smul,Finset.sum_apply,Pi.smul_apply]; apply Finset.sum_congr rfl; intro j hj
 let C:G.Color:= WithLp.toLp 2 fun c=> x (j,c); let t:=finch j i.2 i.1
 change ∑ c:G.ColorIndex, G.adjoint u C c • t • unitColor G c =∑ c:G.ColorIndex,x (j,c) • G.adjoint u (t • unitColor G c)
 simp_rw [map_smul, smul_comm _ t,←Finset.smul_sum]; apply congrArg
 rw [Triangle.sum_color]
 change _= ∑ c:G.ColorIndex,C c • G.adjoint u _; simp_rw [← _root_.map_smul,← _root_.map_sum,Triangle.sum_color] -- prove
lemma stable {p:pLabel G} (h:Neutral p):Still (showP G n p):=by
 intro x u; rw [lens, lump_tu,soul_color,lens]; exact h _ u
lemma stow (p:pLabel G): Solid (showP G n p):=by
 intro x; rw [lens,lens]; apply congrArg (fun y:Labels.Key G→ℝ=> aeval y p); apply _root_.funext; intro i; rw [run_map,run_map]; apply Finset.sum_congr rfl; intro j _; by_cases e: lineP j
 · rw [wingline,if_pos e]
 rw [vertical _ _ _ e,mul_zero,mul_zero]
variable (n)
def horizontal : Sketch G n→ₐ[ℝ] Sketch G n:= aeval fun i:Sky G n=> if lineP i then X i else 0
lemma hor_eval (p:Sketch G n)(x:Sky G n→ℝ): aeval x (horizontal n p) = aeval (wingline n x) p:=by
 have h:(aeval (R:=ℝ) x).comp (horizontal n)=aeval (wingline n x):=by
   ext i; rw [horizontal,AlgHom.comp_apply,aeval_X,aeval_X]; by_cases e:lineP i
   · rw [wingline,if_pos e,if_pos e,aeval_X]
   rw [wingline,if_neg e,if_neg e,map_zero]
 exact DFunLike.congr_fun h p
def paintP(v:Sky G n)(u:G.El):Sketch G n:=∑ c:G.ColorIndex,G.adjoint u (unitColor G c) v.2 • X (v.1,c)
lemma paintH(v:Sky G n)(u:G.El):IsWeightedHomogeneous inkAge (paintP n v u) (inkAge v):=by unfold paintP; apply IsWeightedHomogeneous.sum; intro c _; exact Submodule.smul_mem (weightedHomogeneousSubmodule ℝ inkAge _) _ (isWeightedHomogeneous_X ℝ inkAge (v.1,c))
lemma paintEval(v:Sky G n)(u:G.El)(x:Sky G n→ℝ): aeval x (paintP n v u)=aloft n x u v:=by
 let C:G.Color:= WithLp.toLp 2 fun c=> x (v.1,c)
 unfold paintP aloft; simp only [map_sum,map_smul,aeval_X,smul_eq_mul]; change _=G.adjoint u C v.2; rw [←Triangle.sum_color C]
 simp only [map_sum,map_smul,WithLp.ofLp_sum,PiLp.smul_apply,smul_eq_mul,Finset.sum_apply]; exact Finset.sum_congr rfl fun _ _=>mul_comm ..
def rangeP(u:G.El):Sketch G n→ₐ[ℝ] Sketch G n:= aeval (fun i=>paintP n i u)
lemma range_eval(u:G.El)(x:Sky G n→ℝ)(q:Sketch G n): aeval x (rangeP n u q)=aeval (aloft n x u) q:=by
 have h:(aeval (R:=ℝ) x).comp (rangeP n u)=aeval (aloft n x u):=by ext i; rw [AlgHom.comp_apply, rangeP,aeval_X,aeval_X,paintEval]
 exact DFunLike.congr_fun h q
variable {n}
lemma isStill (q:Sketch G n):Still q↔∀u:G.El,rangeP n u q=q:=by
 constructor
 · intro h u; apply MvPolynomial.funext; intro x; simp_rw [←aeval_eq_eval,range_eval]; exact h _ _
 intro h x u; rw [←range_eval,h u]
lemma isSolid(q:Sketch G n):Solid q↔horizontal n q=q:=by
 constructor
 · intro h; apply MvPolynomial.funext; intro x; simp_rw [←aeval_eq_eval,hor_eval]; exact h _
 intro h x; rw [←hor_eval,h]
lemma still_gr {q:Sketch G n}(h:Still q): Still (weightedHomogeneousComponent inkAge w q):=by apply (isStill _).mpr; intro u; rw [teeters (rangeP n u) _ q, (isStill _).mp h u]; intro i; rw [rangeP,aeval_X]; exact paintH n i u
lemma solid_gr {q:Sketch G n}(h:Solid q):Solid (weightedHomogeneousComponent inkAge w q):=by
 apply (isSolid _).mpr; rw [teeters (horizontal n) _ q,(isSolid _).mp h]; intro i; rw [horizontal,aeval_X]; split
 · exact isWeightedHomogeneous_X ℝ inkAge _
 exact isWeightedHomogeneous_zero ..
lemma horizontally (q:Sketch G n): Solid (horizontal n q):=by
 intro x; rw [hor_eval,hor_eval]; have he:wingline n (wingline n x)=wingline n x:=_root_.funext fun i=>by by_cases h: lineP i<;>simp [wingline,h];
 rw [he]
lemma steady (q:Sketch G n)(h:Still q):Still (horizontal n q):=by
 intro x u; rw [hor_eval, hor_eval, show wingline n (aloft n x u) = aloft n (wingline n x) u from ?_, h]
 apply _root_.funext; intro i; unfold aloft wingline; by_cases hh: lineP i
 · rw [if_pos hh]; have he (v:G.ColorIndex):lineP (i.1,v):= hh; simp_rw [if_pos (he _)]
 rw [if_neg hh]; have he(v:G.ColorIndex):¬ lineP (i.1,v):=hh; simp_rw [if_neg (he _)]; rw [show WithLp.toLp 2 (fun _:G.ColorIndex=>(0:ℝ))=(0:G.Color) from rfl,(G.adjoint u).map_zero];rfl
end YM.SchemeRG11.Outlook
