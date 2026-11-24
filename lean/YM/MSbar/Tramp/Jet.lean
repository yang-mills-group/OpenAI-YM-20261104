import YM.MSbar.Tramp.May
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Tramp
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Wave MvPolynomial
open AnalyticBridge.VerifiedReset Native.Chart Tensor
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {σ X:Type} [Fintype σ][DecidableEq σ][NormedAddCommGroup X][NormedSpace ℝ X]
local notation "Π!"=> Positions σ
-- path of Logs.Line.R.Convenience.Schema derivatives.W.Use signs test and FTC first.
variable (F:ℝ × X → ℝ)(p:List X)
noncomputable def back (v:X) : X→L[ℝ]ℝ× X:= (0: X→L[ℝ]ℝ).prod (ContinuousLinearMap.id ℝ X) -- v unused
noncomputable def ice (F:ℝ × X→ℝ)(p:List X)(t:ℝ)(x:X):=Lis.roc (fun y=>F (t,y)) p x
noncomputable def pD (F: ℝ× X→ℝ)(x:X)(t:ℝ):= fderiv ℝ F (t,x) ((1:ℝ),0)
variable (h: ContDiff ℝ ω F)
include h
lemma froz (x:X)(t:ℝ): ice F p t x=Lis.roc F (p.map (fun v=>((0:ℝ),v))) (t,x):=by
    let f(l:List X)(x):=ice F l t x; let L(x:X):=(t,x); change f p _=_; induction p generalizing x with
    | nil=>rfl
    | cons a p ih=>
       unfold f ice; rw [List.map_cons,Lis.roc,Lis.roc]; let Q:= p.map (fun v=>((0:ℝ),v)); change fderiv ℝ (f p) x a=_
       rw [show f p=Lis.roc F Q ∘ L from funext fun x=> ih x]
       have hf: HasFDerivAt L (back x) x:=(hasFDerivAt_const _ _ |>.prodMk (hasFDerivAt_id ..))
       have hh : DifferentiableAt ℝ (roc F Q) (L x):=(Lis.smooth (1+Q.length) 1 Q (h.contDiffAt.of_le le_top) le_rfl).differentiableAt (by simp)
       rw [fderiv_comp _ hh hf.differentiableAt, hf.fderiv];rfl
lemma sparkleV (x:X)(t:ℝ): HasDerivAt (fun t=> F (t,x)) (pD F x t) t:=by exact (((h.differentiable (by simp) (t,x)).hasFDerivAt).comp_hasDerivAt t ((hasDerivAt_id' t).prodMk (hasDerivAt_const t x)))
lemma blaze (x:X)(t:ℝ): HasDerivAt (fun t=>ice F p t x) (roc (fun x=>pD F x t) p x) t:=by
    let Q:= p.map (fun v=>((0:ℝ),v))
    have hv:DifferentiableAt ℝ (roc F Q) (t,x):= (smooth (1+Q.length) 1 Q (h.contDiffAt.of_le le_top) le_rfl).differentiableAt (by simp)
    let k:=(1+Q.length); let u:ℝ × X:= (1,0); let Z:=fun i:ℝ×X=> fderiv ℝ F i u
    have hx: ContDiff ℝ ω Z:= (h.fderiv_right (m:=ω) (by simp)).clm_apply contDiff_const
    have hs:HasDerivAt (fun t=> roc F Q (t,x)) (roc F (u::Q) (t,x)) t:= hv.hasFDerivAt.comp_hasDerivAt _ ((hasDerivAt_id' t).prodMk (hasDerivAt_const t x))
    have he:roc (fun x=>pD F x t) p x= roc Z Q (t,x):=froz Z p hx x t
    rw [he,← takeG k (h.contDiffAt.of_le le_top) Q u (by omega)]; simp_rw [froz F p h]; exact hs
omit h
variable {n:Side}{l:σ→Site n}{a b w:ℝ}{p':ℕ}{q:ℕ}
-- conversion integral sign trick positivity. paths smooth. need f.C.
lemma glean (F:ℝ× Positions σ→ℝ) (h:ContDiff ℝ ω F) (g:ℝ→ Pot σ)(hp:∀ x t, HasDerivAt (fun t:ℝ=> F (t,x)) (clue (g t) x) t)
    (A:Pot σ) (he:∀ x, clue A x=F (1,x)-F (0,x))(hv:0<w)
    (H:∀ t:ℝ,t∈ Set.Icc (0:ℝ) 1 → Tin l a p' q w (g t) b): Tin l a p' q w A b :=by
     have h0b:= (H 0 (by simp)).1; refine ⟨h0b,fun j hj i=>?_⟩; rw [← scored]
     let Z(k:List σ):= List.map Uniform.bolt k; let X₁(k:List σ)(t:ℝ):= ice F (Z (i::k)) t 0; let B(k:List σ):=swipe l a p' (i::k); let v(k):= if 0≤ X₁ k 1-X₁ k 0 then B k else -B k
     let f(t):=Yarn j (fun k:List σ=> v k* X₁ k t); let g'(t):=Yarn j (fun k:List σ=> v k*buoy (clue (g t)) 0 (i::k))
     have hp'(k:List σ)(t:ℝ): HasDerivAt (X₁ k) (buoy (clue (g t)) 0 (i::k)) t:=by
         have ht:= blaze F (Z (i::k)) h 0 t; have he:pD F=fun x t=>clue (g t) x:=funext fun x=>funext fun t=> (sparkleV F h x t).unique (hp x t); rw [he] at ht; exact ht
     have hc(k:List σ): buoy (clue A) 0 (i::k)= X₁ k 1-X₁ k 0:=by
         rw [funext he]; unfold buoy; let hB(i:ℝ)(x:Positions σ):=F (i,x); let B:ℕ:= (Z (i::k)).length; have hs(i:ℝ): ContDiffAt ℝ B (hB i) 0:=((h.contDiffAt.comp (f:=fun t:Positions σ=>(i,t)) (0:Positions σ) (contDiffAt_const.prodMk contDiffAt_id)).of_le le_top)
         rw [show (fun i:Π!=> _)= hB 1+(fun i=> (-1:ℝ)*hB 0 i) from funext (fun x=>by change _=_+(-1:ℝ)*_; rw [neg_one_mul]; rfl)] -- sub not rfl
         rw [addedL B ((i::k).map bolt) (hB 1) (fun z=> (-1:ℝ)*hB 0 z) (hs 1) ((hs 0).const_smul (-1:ℝ)) (show ((i::k).map Uniform.bolt).length≤ B from le_rfl),wed B _ _ _ (hs 0) (show ((i::k).map Uniform.bolt).length≤ B from le_rfl)]; change _= _-_; rw [neg_one_mul]; rfl
     have hf(k:ℕ)(l:List σ)(t:ℝ) : HasDerivAt (fun t=> Yarn k (fun l'=> v (l++l')* X₁ (l++l') t)) (Yarn k (fun l'=> v (l++l')*buoy (clue (g t)) 0 (i::(l++l')))) t:=by
         induction k generalizing l with
         | zero=> exact (hp' ..).const_mul _
         | succ k ih=> simp_rw [twilled]; exact HasDerivAt.fun_sum fun c _=> by simpa only [List.append_assoc,List.cons_append,List.nil_append] using ih (l++[c])
     have hF(t):HasDerivAt f (g' t) t:= by simpa only [List.nil_append] using hf j [] t
     have hE(t:ℝ)(he:t∈Set.Icc (0:ℝ) 1): ‖g' t‖ ≤ b/w^(j+1):=by
         have hc:= ((scored (g t) i).le.trans (H _ he|>.2 j hj i)); apply (polished ..).trans ((shiny (ι:=σ) j ?_).trans hc); intro k hk; have hp : |v k|= B k:= by unfold v; split <;> simp only [abs_neg,abs_of_pos (effect ..),B,swipe] -- op
         rw [abs_mul,hp,mul_comm (B k)]
     have he : |f 1-f 0| ≤ b/w^(j+1):=by simpa only [sub_zero, Real.norm_eq_abs, abs_one,mul_one] using Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (fun i (_:i∈Set.Icc (0:ℝ) 1)=> (hF i).hasDerivWithinAt) hE (convex_Icc _ _) (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one)
     refine le_trans (le_trans (le_of_eq ?_) (le_abs_self _)) he
     let Y(k:List σ):= X₁ k 1-X₁ k 0; have Hp : f 1=Yarn j (fun k=> v k*Y k)+f 0:=by unfold f; rw [←pockets]; exact stitch _ fun k _=>by unfold Y; ring
     rw [Hp,add_sub_cancel_right]; apply stitch; intro k _; rw [hc]; change |Y k| *B k= v k*_; unfold v; split; next he=> rw [abs_of_nonneg he]; ring
     next he=> rw [abs_of_neg (show Y k<0 from lt_of_not_ge he)]; unfold Y; ring
end YM.MSbar.Tramp
