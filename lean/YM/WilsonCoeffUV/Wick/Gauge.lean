import YM.WilsonCoeffUV.Wick.Through
/-!
# Wick leading symmetry/calibration carried on normalized stencil
- gauge-linear gradients verified on all orders needed. Response equality after
π using H authority. Not requiring pre-block-to-post layout changes. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Bank.Carp
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Soil Cosmos
open Exterior Next.Free Tree Precision Power Embroider Source
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {c f n:Side}{U V α:Type*}{G:Gauge}{r e j k m D N:ℕ}{x ξ σ A' B:ℝ}
variable (A:Levels G)
lemma GammaO (w:G.El) : gammaC w*(gammaC w).transpose=1:=by
   apply mul_eq_one_comm.mp
   ext i j; let M:=gammaC w
   let V (u:G.ColorIndex):= coatC G (Pi.single u 1)
   let F: G.Color →ₗᵢ[ℝ] G.Color:=⟨G.adjoint w,G.norm_adjoint w⟩
   have he u k: F (V u) k=M k u:=by
       have hh: F (V u) k= (M *ᵥ Pi.single u 1) k:=by
          rw [show M=gammaC w from rfl,gammaC,LinearMap.toMatrix'_mulVec]; rfl
       rwa [Matrix.mulVec_single_one] at hh
   have hp:= F.inner_map_map (V i) (V j);
   simp_rw [PiLp.inner_apply,RCLike.inner_apply] at hp
   simp_rw [he] at hp; simpa [V,coatC,Pi.single_apply, Matrix.mul_apply, Matrix.one_apply,mul_ite,ite_mul,mul_comm,eq_comm] using hp
lemma bale (w:G.El)(M: Matrix (Body 1 n) (Body 1 n) ℝ): shadeS w n*tensor G M*(shadeS w n).transpose=tensor G M:=by
    let F:= shadeS w n
    have he (x y:Site n)(a b:TypeFace 1)(u v:G.ColorIndex): F (x,a,u) (y,b,v) = if (x,a)=(y,b) then gammaC w u v else 0:=by
       unfold F shadeS; rw [Matrix.of_apply]; congr 1; simp [entryS, (Equiv.injective _).eq_iff]
    have h x y a b u v: (F*tensor G M) (x,a,u) (y,b,v)= gammaC w u v * M (x,a) (y,b):= by rw [Matrix.mul_apply]; simp [Fintype.sum_prod_type,tensor,he,mul_ite,ite_mul,and_comm,ite_and]
    ext ⟨x,a,b⟩ ⟨y,e,f⟩; change (F*tensor G M*F.transpose) _ _=_; rw [Matrix.mul_apply]; simp_rw [Fintype.sum_prod_type,h,Matrix.transpose_apply,he]
    simp [Prod.mk.injEq,ite_and]
    simp_rw [mul_right_comm (gammaC w b _), ← Finset.sum_mul]; rw [show ∑ i,gammaC w b i*gammaC w f i=(1:Matrix _ _ ℝ) b f from congr_fun (congr_fun (GammaO w) b) f]; simp [tensor,Matrix.one_apply,ite_mul]
lemma mural_carve (P:Gen ℝ (Woods G n))(h:still P (k+1))(g:Pure P)(u:G.El)(q:P=fade (shadeS u n) P)(m N): let T:= carve k (blues A N m n) P; T=fade (shadeS u n) T:=by
    let X:=blues A N m n
    intro T; let V:=shadeS u n; have he: still T (k+1):=carved _ _ h; have hp: Pure T:=sculpt _ _ g
    have hx: totalR P=cord V (totalR P):= by conv_lhs=> rw [q]; exact fade_visible V P ⟨_,h⟩
    apply gen_inj ⟨_,he⟩ (fade_finite ⟨_,he⟩ V) hp (fade_pure hp V); rw [fade_visible V _ ⟨_,he⟩,show totalR T=glaze X (totalR P) from carving _ _ h g]; conv_lhs=> arg 2; rw [hx]
    rw [daystar V X (colorS_sym _ _ A.clock.kernel.penalty_pos _)]; rw [show V*X*Vᵀ=_ from bale u _]; rfl

private lemma shot {e}{T:Gen ℝ (Woods G n)} (x:G.El) (h: T=fade (shadeS x n) T) (F:Fin e→Edge (Site n))(p:Fin e→G.ColorIndex): T e (fun i=>entryS G n (F i,p i)) = ∑ q: Fin e→ G.ColorIndex,(∏ j,gammaC x (q j) (p j)) • T e (fun i=>entryS G n (F i,q i)):=by
    let M (a:Fin e→G.ColorIndex) : Fin e→Woods G n:= fun i=>entryS G n (F i,a i)
    have hs: Injective M:= fun i j h=> funext fun w=> Prod.mk.inj ((entryS G n).injective (congr_fun h w))|>.2
    conv_lhs=> rw [h]
    set P:=M p; unfold fade; rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image M))]
    · rw [Finset.sum_image (fun x _ y _ h=>hs h)]; apply Finset.sum_congr rfl; intro i _; apply congr_arg₂ (· • ·) _ rfl; apply Finset.prod_congr rfl; intro j _; unfold M shadeS; rw [Matrix.of_apply,Equiv.symm_apply_apply,Equiv.symm_apply_apply,if_pos rfl]; rfl
    intro i _ v; by_contra p'; apply v; let f j:=(entryS G n).symm (i j); have hp j: (f j).1=F j:=by by_contra hp; apply p'; rw [Finset.prod_eq_zero (Finset.mem_univ j), zero_smul]; unfold shadeS; rw [Matrix.of_apply,Equiv.symm_apply_apply]; exact if_neg hp
    exact Finset.mem_image.mpr ⟨fun j=>(f j).2, Finset.mem_univ _,funext fun i'=>by unfold M;rw [← hp];exact (entryS G n).apply_symm_apply _⟩

lemma singer (X: Single G D)(P:Estate G D)(p:Solo k P X)(v:ℕ)(h:k≤v)(r N m:ℕ):mural (paveS A m N v (X 0) r):=by
    intro f x j; ext1 u; let U:=(ContinuousLinearMap.apply ℝ ℝ u).toLinearMap; let H n:=jot u (P n); let D' n:= carve v (blues A N m n) (H n 0); let V:=paveS A m N v (X 0); let T (y:Fin r→G.ColorIndex):= fun i:Fin r=> stone (x i) (y i); let F(n:Side)(i:Fin r): Edge (Site n):= (wrap n (x i).1,(x i).2)
    have he n : D' n=fade (shadeS f n) (D' n):= mural_carve A _ (fun i hi=> (show shellK k (H n) from jot_length u (p.launch _)) _ _ (by omega)) (jot_code u (p.evenS _ _)) _ (byShade (solo_one p u n) (jot_length u (p.launch n)) (fun i=> jot_code u (p.evenS n i)) 0 f) m N
    have hh:Bends 0 (fun n=> D' n r) (tinct U (V r)):= by
        refine Bends.congr ((mason_path (P:=X 0) (Q:=fun n=>P n 0) (recruit A N m) v (p.shore 0) r).touch (ContinuousLinearMap.apply ℝ ℝ u)) (Eventually.of_forall (fun n=>?_))
        unfold D' H; rw [show jot u (P n) 0=cloaks U (P n 0) from rfl,masonmaps]; rfl
    simp_rw [_root_.sum_apply,_root_.smul_apply]; refine tendsto_nhds_unique (hh.point (T j)) ((tendsto_finsetSum (f:=fun i n=> (∏ l,gammaC f (i l) (j l)) • D' n r (slideC n (T i))) _ (fun i _=> (hh.point (T i)).const_smul _)).congr fun z=>?_)
    exact (shot f (he z) (F z) j).symm

section linear
omit A
-- directly infinite rime using vent y.
variable [NormedAddCommGroup V][NormedSpace ℝ V][CompleteSpace V]
omit [CompleteSpace V] in
lemma windsCast (x:Cover)(a:G.ColorIndex)(c:ℝ)(P: Ten V (YForest G) (r+1)): windsL x a (c • P)=c •windsL x a P:=by unfold windsL;funext i; simp only [Finset.sum_apply,Pi.smul_apply,Finset.sum_apply,Pi.sub_apply,prune,Pi.smul_apply,smul_sub,Finset.smul_sum]
lemma takeRime (Q:Gen V (YForest G)){K:ropes Cover (Hooks G) (Hooks G)}(h:Pure Q)(p:0<σ)(hp:Cork Bank.terrain 0 σ A' (Q (r+1+2)))(ht:shoulder K B)(x:Cover)(i:G.ColorIndex)(u:windsL x i (Q (r+1+2))=0): windsL x i (rime K Q (r+1))=0 := by
   funext y
   let Y:= rain K Q (r+1); let m (v:dock Cover (Hooks G) 2):= (1/2:ℝ)*K (v 0) (v 1)*(r+2:ℕ)*(r+3:ℕ)
   have hv (z): Summable (Y z):= ((soul_bill ht hp p.le).cache p le_rfl z).2.1.of_norm
   have he (u:YForest G) (v:dock Cover (Hooks G) 2): Y (Fin.cons u y) v=m v • Q _ (Fin.cons u (Fin.cons (v 1) (Fin.cons (v 0) y))):= by
       unfold m Y; rw [rain_spell]; congr 1; have e : Pure Q:= h; let P:=Q (r+1+2); have hp:=e (r+1+2)
       calc
        _ = Q _ (Fin.cons (v 1) (Fin.cons u (Fin.cons (v 0) y))) := congr_fun (prune_square (hp.prune (v 1)) (v 0) u) y
        _ = _ := congr_fun (prune_square hp (v 1) u) (Fin.cons (v 0) y)
   let W (j:Axis)(v:dock Cover (Hooks G) 2):=Y (Fin.cons (stone (x,j) i) y) v-Y (Fin.cons (stone (x-step j,j) i) y) v
   have ht j : Summable (W j):= (hv _).sub (hv _)
   unfold windsL; rw [Finset.sum_apply]
   calc
    _ = ∑ l:Axis,∑' v,W l v:=Finset.sum_congr rfl (fun j _=> Eq.symm (Summable.tsum_sub (hv _) (hv _)))
    _ = ∑' _v:dock Cover (Hooks G) 2,(0:V):=by
        rw [← Summable.tsum_finsetSum (fun i _=>ht _)]; apply tsum_congr; intro v; unfold W; simp_rw [he,← smul_sub]; rw [← Finset.smul_sum]; refine Eq.trans ?_ (smul_zero (m v)); apply congr_arg (m v • ·)
        have he:=congr_fun u (Fin.cons (v 1) (Fin.cons (v 0) y)); rw [windsL,Finset.sum_apply] at he; exact he
    _ = _ := tsum_zero
end linear
structure Hedged (P: Ten (Vote D) (YForest G) r): Prop where
   mossP: mural P
   sheen: Smooth P
   tax: Standby P
   emits:∀ s:ℝ,Wing 0 s 0 P
lemma wing_c {P:Gen (Vote D) (YForest G)}(h:∀ r x i,windsL x i (P (r+1))=0): ∀ r s,Wing 0 s 0 (P r) := by
   intro r s; cases r; exact le_rfl
   case succ r=> exact ⟨le_rfl,fun x i=> (h r x i).symm ▸ Prance.zero⟩
lemma winds_carve (X:Single G D)(P:Estate G D)(p:Solo k P X)(v:ℕ)(q:k≤v)(N m): ∀ r,Hedged (paveS A m N v (X 0) r):=by
   let Y r:=X 0 r; let t:=sea A N m; let M:= ivern t Y; let S:=recruit A N m
   have hp:=solo_upright p; have he (u r): Bends 0 (fun n=> iceberg (blues A N m n) (P n 0) u r) (M u r):=icy S (P:=Y) (p.shore 0 _)
   have hh u: Pure (M u):= fun r=> (he u r).pure (Eventually.of_forall fun n=> ice_s _ _ (p.evenS _ _) r)
   obtain ⟨C,T⟩:=S.bound
   have hu (j r x i): windsL x i (M j (r+1))=0:=by
      induction j generalizing r with
      | zero=> exact sky_split hp (solo_pure p) 0 r (by intro _ h; omega) x i
      | succ a ih=>
        obtain ⟨s,A,hs,X⟩:=(he a (r+1+2)).land
        change windsL x i ((ivern t Y (a+1)) (r+1))=0; rw [ivern,Pi.smul_apply,windsCast,takeRime (ivern t Y a) (hh _) hs X T x i (ih (r+2)),smul_zero]
   let F:= paveS A m N v (X 0); have hx r:Bends 0 (fun n=>carve v (blues A N m n) (P n 0) r) (F r):= mason_path (P:=X 0) S v (p.shore 0) r
   have hZ r x i:windsL x i (F (r+1))=0:=by
       have he':F=∑ j∈Finset.range (v+1),M j:=rfl
       rw [he',Finset.sum_apply]
       ext1 y; apply Eq.trans _ (show ∑ j∈Finset.range (v+1), windsL x i (M j (r+1)) y = (0:Vote D) from Finset.sum_eq_zero fun j _=> congr_fun (hu j r x i) y); unfold windsL; simp only [prune,Finset.sum_apply,Pi.sub_apply]; conv_lhs => enter [2,j]; rw [← Finset.sum_sub_distrib]
       exact Finset.sum_comm
   exact fun r=>⟨singer A X P p v q _ _ _, (hx r).pure (Eventually.of_forall fun n=>sculpt v _ (p.evenS _ _) r), (hx r).land, wing_c hZ r⟩
end YM.WilsonCoeffUV.Bank.Carp
