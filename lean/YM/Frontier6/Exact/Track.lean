import YM.Frontier6.Exact.Look

/-! Transferring center of annihilation. No new operator derivative: use
K's filtered actual system, which works also in every phase. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6
open Spec Function Filter Set Lattice Wilson MeasureTheory Org
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable (K:Final C F S)(s:StateIndex K) {e d n:ℕ}(hL:Grill C F)

lemma clear_exterior {y:Points n}{r:ℝ}(h:clearC r y)(i:Fin n): r < ‖y i‖:=by
   simpa only [Points.cons, points_apply, Fin.cons_zero,Fin.cons_succ,sub_zero] using (show _ < ‖Points.cons 0 y i.succ - Points.cons 0 y 0‖ from h _ _ (Fin.succ_ne_zero i).symm)
lemma clear_tail {r:ℝ}{y:Points n}{x:E4}(h:minGap r (Points.cons x y)): minGap r y:=fun i j hj=> h i.succ j.succ (fun ht=> hj (Fin.succ_injective _ ht))
lemma clear_translation {r:ℝ}{p:E4}{y:Points n}(hp:‖p‖ ≤ r/2)(hc:clearC r y): minGap (r/2) (Points.cons p y):=gap_append (gap_down (clear_tail hc) (by linarith only [hp,norm_nonneg p])) p (fun i => by linarith only [norm_sub_norm_le (y i) p, clear_exterior hc i,hp])
lemma clear_move (p:E4){r:ℝ}{y:Points n}(h:minGap r y) : minGap r (Points.across p y):=by intro i j hi; specialize h i j hi; rw [Points.across_coord,Points.across_coord,add_sub_add_right_eq_sub]; exact h

/-- linear direction descendant -/
def alongField (x:E4)(d:ℕ): S.Field d →L[ℂ] S.Field (d+1):=
   ∑ i:Axis, ((x i:ℝ):ℂ) • LinearMap.toContinuousLinearMap (K.sector.derivatives.deriv d i)
theorem nspan_le {X:Type*}[NormedAddCommGroup X][NormedSpace ℂ X] (f:S.Field d →L[ℂ] X)(c:ℂ): ‖c • f‖≤ ‖c‖*‖f‖:= by
   refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg c) (norm_nonneg f)) (fun x=> ?_); rw [mul_assoc,smul_apply]
   exact (norm_smul_le c (f x)).trans (mul_le_mul_of_nonneg_left (f.le_opNorm x) (norm_nonneg c))
lemma along_bound (d:ℕ): ∃ B:ℝ,0 ≤ B ∧ ∀ x, ‖alongField K x d‖ ≤ ‖x‖* B:=by
   let F i:= LinearMap.toContinuousLinearMap (K.sector.derivatives.deriv d i)
   refine ⟨∑ i:Axis, ‖F i‖, Finset.sum_nonneg (fun i _=> norm_nonneg (F i)),fun x=>?_⟩
   rw [Finset.mul_sum]; unfold alongField; refine (norm_sum_le _ (fun i:Axis=> (↑(x i):ℂ) • F i)).trans ?_; refine Finset.sum_le_sum (fun i _=> ?_); refine (nspan_le (F i) _).trans ?_; rw [Complex.norm_real]
   exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le x i) (norm_nonneg (F i))

local instance (priority:=high) pcx (n:ℕ) : ContinuousSMul ℝ (Points (n+1)) := inferInstance
local instance (priority:=high) tcx (n:ℕ) : IsTopologicalAddGroup (Points (n+1)):=inferInstance
set_option maxHeartbeats 500000 in
private lemma ray_walk (x:E4)(q:Points n) (u:ℝ):
   let A(t:ℝ):Points (n+1):= Points.cons (t • x) q
   let Y (i:Axis):=Points.direction (n:=n+1) 0 i
   let X: Points (n+1):=∑ i:Axis, x i • Y i
   HasDerivAt A X u:=by
  intro A Y X
  have hb : ∑ i:Axis, x i • basis i=x:=by simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,basis] using (EuclideanSpace.basisFun Axis ℝ).sum_repr x
  have hX:X=Points.cons x 0:=by
    ext1 i
    let Z(j:Fin (n+1)):=PiLp.proj (𝕜:=ℝ) 2 (fun _ :Fin (n+1)=>E4) j
    change Z i X= _; refine Fin.cases ?_ (fun j=> ?_) i
    · unfold X Z; rw [map_sum];
      simp [Y,Points.direction,hb,Points.cons]
    unfold X Z; rw [map_sum]; simp [Y,Points.direction,Points.cons]
  have he : A=fun t:ℝ=> Points.cons 0 q + t • X:=by ext1 t; rw [hX]; ext1 i; refine Fin.cases ?_ (fun j=>?_) i; change t • x=0+t • x; rw [zero_add]; change q _=q _+t • 0; simp
  rw [he]; have he := (ContinuousLinearMap.toSpanSingleton ℝ X).hasDerivAt (x:=u); simpa using he.const_add (Points.cons 0 q)
lemma leads (x:E4) (q:Points n)(v:Fin n→ S.Tag)(B:S.Field d) {u:ℝ}(h:Points.cons (u • x) q ∈ conf _):
  HasDerivAt (fun t:ℝ=> reading K s (t • x) q v d B) (reading K s (u • x) q v (d+1) (alongField K x d B)) u:=by
  simp_rw [reads_at K s (x:=_ • x) (d:=d)] -- ? only function
  let A(t:ℝ):Points (n+1):= Points.cons (t • x) q; let T:=state K s
  let f:Points (n+1)→ℂ:= fun y=> S.useAt T y (Fin.cons ⟨d,B⟩ v)
  let Y (i:Axis):=Points.direction (n:=n+1) 0 i; let X: Points (n+1):=∑ i:Axis, x i • Y i
  have hA:HasDerivAt A X u:= ray_walk x q u
  have hx':DifferentiableAt ℝ f (A u):= (((S.class_smooth T (hierarchy K s).smooth _) _ h).contDiffAt ((conf_open _).mem_nhds h)).differentiableAt (by simp)
  have hh : reading K s (u • x) q v (d+1) (alongField K x d B)= fderiv ℝ f (A u) X := by
     unfold alongField X; rw [sum_apply,map_sum,map_sum]; refine Finset.sum_congr rfl fun i _=> ?_
     rw [smul_apply,map_smul,map_smul]; rw [Complex.real_smul,reads_at]; exact congr_arg (fun y:ℂ=> (x i:ℂ) • y) ((directional K s).kernels d i B h v)
  rw [hh]; exact hx'.hasFDerivAt.comp_hasDerivAt u hA

variable {I:Type*}[Fintype I]{N:I→ℕ}(v:Tuple S N)
def survey (d:ℕ)(y:Seen N)(u:I→StateIndex K)(c:I→ℂ)(x:E4): S.Field d →L[ℂ] ℂ:=∑ i:I,c i • reading K (u i) x (y i) (v i) d
lemma survey_at (d:ℕ)(y:Seen N)(u:I→StateIndex K)(c:I→ℂ)(x:E4)(B:S.Field d):
  survey K v d y u c x B= ∑ i:I,c i * reading K (u i) x (y i) (v i) d B:=by simp [survey]

include hL
lemma kills_order (hh:e ≤ d){a B:ℝ}(ha:0 < a)(hB:0 ≤ B):
  ∃ A:ℝ,0 ≤ A ∧ ∀ r:ℝ,0 ≤ r→ r≤a/2 → ∀ (x:E4),‖x‖≤r→ ∀ (y:Seen N), shapes a y→ ∀ (u:I → StateIndex K)(c:I→ℂ), (∀ i,‖c i‖ ≤ B) → kills K v y u c d →
     ‖survey K v e y u c x‖ ≤ A*r^(d-e):=by
  generalize hj:d-e=j
  induction j generalizing e with
  | zero=>
     choose M hM H using fun i:I=> reading_bounded K hL (v i) (a/2) (half_pos ha) e
     refine ⟨∑ i:I,B * M i, Finset.sum_nonneg (fun i _=> mul_nonneg hB (hM i)),fun r hr h x hx y hy u c hc hk=>?_⟩
     rw [pow_zero,mul_one]; unfold survey; refine (norm_sum_le _ (fun i=> c i • reading K (u i) x (y i) (v i) e)).trans ?_; refine Finset.sum_le_sum (fun i _=> ?_)
     let R:= reading K (u i) x (y i) (v i) e; change ‖(c i) • R‖ ≤ _; apply (nspan_le R (c i)).trans; exact mul_le_mul (hc i) (H i (u i) x (y i) (clear_translation (hx.trans h) (hy i))) (norm_nonneg R) hB
  | succ j ih=>
     have he:e+1 ≤ d:=by omega
     obtain ⟨A,hA,H⟩:=ih he (show d-(e+1)=j by omega)
     obtain ⟨V,hV,hg⟩:=along_bound K e
     refine ⟨A*V,mul_nonneg hA hV,fun r hr h x hx y hy u c hc hk=>?_⟩
     let F(e:ℕ)(t:ℝ):= survey K v e y u c (t • x)
     refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (mul_nonneg hA hV) (pow_nonneg hr _)) (fun p=> ?_)
     let q:= alongField K x e p
     have hp (t:ℝ)(ht:t∈Icc (0:ℝ) 1): ‖t • x‖ ≤ r:= by rw [norm_smul,Real.norm_of_nonneg ht.1]; exact (mul_le_mul ht.2 hx (norm_nonneg x) zero_le_one).trans (by rw [one_mul])
     have hq (t:ℝ)(ht:t∈Icc (0:ℝ) 1):HasDerivAt (fun t=> F e t p) (F (e+1) t q) t:=by
       unfold F; simp_rw [survey_at]
       exact HasDerivAt.fun_sum fun i _=> (leads K (u i) x (y i) (v i) p (gap_conf (half_pos ha).le (clear_translation ((hp t ht).trans h) (hy i)))).const_mul _
     let Z:= A*V*r^(j+1)*‖p‖
     have hW (t:ℝ)(ht:t∈Icc (0:ℝ) 1):‖F (e+1) t q‖ ≤ Z:=by
       have hq':‖q‖ ≤ r*V*‖p‖:= ((alongField K x e).le_opNorm _).trans (mul_le_mul_of_nonneg_right ((hg x).trans (mul_le_mul_of_nonneg_right hx hV)) (norm_nonneg _))
       apply ((F (e+1) t).le_opNorm _).trans
       refine (mul_le_mul (H r hr h _ (hp t ht) y hy u c hc hk) hq' (norm_nonneg q) (mul_nonneg hA (pow_nonneg hr _))).trans_eq ?_
       unfold Z; ring
     have heq:=Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f:=fun t=> F e t p) (fun i hi=> (hq i hi).hasDerivWithinAt) (fun i hi=> hW i hi) (convex_Icc (0:ℝ) 1) (show 0∈ Icc (0:ℝ) 1 by simp) (show 1∈ Icc (0:ℝ) 1 by simp)
     have hu:F e 0 p=0:=by unfold F; rw [zero_smul,survey_at]; exact hk e (by omega) p
     rw [hu,sub_zero,sub_zero,norm_one,mul_one] at heq; simpa only [F,one_smul] using heq
end YM.Frontier6
