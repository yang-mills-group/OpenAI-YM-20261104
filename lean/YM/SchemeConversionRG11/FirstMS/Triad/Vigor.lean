import YM.SchemeConversionRG11.FirstMS.Triad.Suppresses

/-! Compare d-dimensional integral projection to the unique soft cut sense. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.FirstMS.Triad
open Function Set Filter MSbar MeasureTheory Metric Complex DR Maxwell Maxwell.Free Pert.Triangle Analysis
open scoped Topology ContDiff BigOperators Classical InnerProductSpace

variable {x:Nodes} {R ρ:ℝ} (h:Box x R ρ)(l:P→Stem)(j:P)(a:Axis) (hl:∀ i,(l i).loc=i)
include h
lemma Box.confirms : x∈conf 3:= by
    intro i j hh; by_contra hr
    have hp:= h.cleft i j hr; change x i=x j at hh
    rw [hh,sub_self,norm_zero] at hp; linarith [h.mass]

def flag (x:Nodes)(R:ℝ)(i:P)(v:E4):ℝ:= bitnear x R i (v,0)
omit h in
lemma flag_smooth (i:P): ContDiff ℝ ∞ (flag x R i):= (smooth_near i).comp (contDiff_id.prodMk contDiff_const)
lemma Box.flag_support (i:P) : tsupport (flag x R i)⊆closedBall (x i) R:= by
   refine closure_minimal (fun v hv=>?_) isClosed_closedBall
   apply mem_closedBall_iff_norm.mpr; apply le_of_not_gt; intro he; apply hv
   unfold flag bitnear; apply cap_ends
   apply (one_le_div (pow_pos h.mass _)).2
   exact show R^2 ≤ ‖v-x i‖^2+(0:ℝ) by rw [add_zero]; exact pow_le_pow_left₀ h.mass.le he.le _
lemma Box.flag_cost (i:P): HasCompactSupport (flag x R i):= (isCompact_closedBall ..).of_isClosed_subset (isClosed_tsupport _) (h.flag_support i)
set_option linter.unusedSectionVars false in
lemma Box.flag_uniq (i:P): flag x R i=ᶠ[𝓝 (x i)] fun _=>1:= by
   let f(v:E4):= total (move (x i) (v,0))/R^2
   have he: f (x i)=0:=by simp [f,move,total]
   have hf : Continuous f:= (total_smooth.continuous.comp ((move_smooth _).continuous.comp (continuous_id'.prodMk continuous_const))).div_const _
   apply hf.continuousAt (x:= x i) |>.tendsto.eventually (p:=fun t=>cap t=1)
   rw [he]; exact DR.edge.eventuallyEq_one
lemma Box.flags (i:P){j:P}(he:j≠i): x j∉tsupport (flag x R i):=by
   intro hq; have ht:= mem_closedBall_iff_norm.mp (h.flag_support i hq); linarith [h.cleft _ _ he,h.mass]

include hl
omit h in
lemma bypass_value {w:E4}(hw:∀ i,i≠j→ w≠x i):
   vines l j a x (cluster l j)ᶜ 0 (w,0)=↑(bypass x l j 0 w) := by
   have hp : (cluster l j)ᶜ = Finset.univ.erase j:= by ext; simp [cluster,hl]
   rw [hp, vines,bypass,ofReal_prod]; refine Finset.prod_congr rfl (fun i hi=>?_)
   have H:=Finset.ne_of_mem_erase hi; rw [kind,if_neg H,hl]
   exact kernel_real _ _ _ (sub_ne_zero.mpr (hw _ H))

omit h in
lemma sphere_value {w:E4}(hw:∀ i,w≠x i):
   vines l j a x Finset.univ 0 (w,0)=↑(softsphere x l j a 0 w) := by
   let d(i:P):= kind l j a i 0 (move (x (l i).loc) (w,0)).1 0
   change (∏ i:P,d i)=_
   rw [← Finset.mul_prod_erase _ d (Finset.mem_univ j),softsphere, ofReal_mul]
   have he : d j=(↑(surface x l j a 0 w):ℂ) := by unfold d kind; rw [if_pos rfl,hl]; exact bar_real _ _ _ _ (sub_ne_zero.mpr (hw j))
   rw [he]; congr 1
   exact Eq.trans (show ∏ i∈Finset.univ.erase j,d i=vines l j a x (cluster l j)ᶜ 0 (w,0) by
      rw [show (cluster l j)ᶜ=Finset.univ.erase j from (by ext; simp [cluster,hl])]; rfl) (bypass_value l j a hl (fun i _=> hw i))

set_option maxHeartbeats 640000 in
theorem result (hc:x∈conf 3) :
    Tendsto (fun t=> (↑(∫ v,softsphere x l j a t v):ℂ)) (𝓝[>] (0:ℝ)) (𝓝 (multiplies l j a x R ρ 0)):=by
   let F(v:E4):= vines l j a x Finset.univ 0 (v,0); let χ:=flag x R j
   let U(i:P)(v:E4):= (flag x R i v:ℂ)*F v
   let T (i:P):= locals l j a x R i
   let A:=∫ v, (1-χ v)*softsphere x l j a 0 v; let B:=∫ v, leg x l 0 j v*grad a (piece x l j χ 0) v
   have HA : ∀ i:P,i≠j → Integrable (U i) ∧ packing l j a x R i 0=∫ v,U i v:= by
      intro i hi
      have hu(v:E4): U i (v+x i)=lane 0 (l i).dual (l i).i (l i).axis v 0*T i (0,v,0):=by
         unfold U F T; unfold locals flag bitnear
         let H(k:P):= kind l j a k 0 (v+x i-x (l k).loc) 0
         change (cap _ :ℂ) * (∏ k:P,H k)=_
         rw [← Finset.mul_prod_erase _ H (Finset.mem_univ i)]
         rw [show H i= lane 0 (l i).dual (l i).i (l i).axis v 0 by unfold H; rw [kind, if_neg hi,hl,add_sub_cancel_right]; rfl]
         rw [show move (x i) (v + x i,0)= (v,(0:ℝ)) from (by simp [move]),show move (-x i) ((0,v,(0:ℝ))).2=(v+x i,0) from (by simp [move])]
         rw [show (cluster l i)ᶜ=Finset.univ.erase i from (by ext; simp [cluster,hl])]; unfold vines H move; ring
      let f(v:E4):= U i (v+x i)
      have hh:= capacitate (l i).dual (l i).i (l i).axis (cut_local h l j a i)
      have he:Integrable f:= hh.1.congr (Eventually.of_forall fun v=> (hu v).symm)
      refine ⟨?_,?_⟩
      · simpa only [f,sub_add_cancel] using he.comp_sub_right (x i)
      rw [freezes l j a hl,subgraph, if_neg hi]; refine hh.2.trans ?_
      rw [← integral_add_right_eq_self (U i)]; exact integral_congr_ae (Eventually.of_forall fun v=> (hu v).symm)
   have HG : ↑(A-B)=multiplies l j a x R ρ 0:=by
      have hb := border h l j a; unfold multiplies
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), ← add_assoc]
      push_cast
      have hy : (A:ℂ)=pivot l j a x R ρ 0+high l j a x ρ 0+∑ i∈Finset.univ.erase j, packing l j a x R i 0:= by
         have hin(i)(hi:i∈Finset.univ.erase j) := HA i (Finset.ne_of_mem_erase hi)
         rw [middle_zero h l j a,hb.2, Finset.sum_congr (s₁:=Finset.univ.erase j) rfl (fun i hi=> (hin i hi).2), ← integral_finsetSum _ (fun i hi=> (hin i hi).1)]
         rw [← integral_add (middle_pays h l j a) hb.1]; rw [← integral_add (show Integrable (fun v:E4=> mid l j a x R ρ (0,v,0)+(↑(1-last ρ (v,0)):ℂ)* vines l j a x Finset.univ 0 (v,0)) volume from (middle_pays h l j a).add hb.1) (integrable_finsetSum (f:=U) _ (fun i hi=> (hin i hi).1))]
         unfold A; rw [← integral_complex_ofReal]
         apply integral_congr_ae
         filter_upwards [(eventually_all_finset Finset.univ).2 (fun i _=>volume.ae_ne (x i))] with v hv
         let f:= softsphere x l j a 0 v
         have he: vines l j a x Finset.univ 0 (v,0)=↑f:=sphere_value l j a hl fun i=> hv i (Finset.mem_univ i)
         change (↑((1-χ v)*f):ℂ)=_
         simp only [mid,waist,U,F, he,χ,flag,vert,cpow_zero,one_mul,ofReal_mul,ofReal_sub,ofReal_one,ofReal_sum,← Finset.sum_mul]
         rw [← Finset.sum_erase_add _ (fun i:P=> (bitnear x R i (v,0):ℂ)) (Finset.mem_univ j)]; ring
      rw [hy,sub_eq_add_neg]; congr 1
      rw [freezes (i:=j) l j a hl, subgraph,if_pos rfl,neg_inj]
      have hh:= capacitate (l j).dual (l j).i (l j).axis ((cut_local h l j a j).gradient a)
      refine Eq.trans ?_ hh.2.symm
      have ht(v:E4): T j (0,v,0)=(piece x l j χ 0 (v+x j):ℂ):= by
         unfold T locals; rw [show move (-x j) ((0,v,(0:ℝ))).2=(v+x j,0) from (by simp [move])]; unfold χ piece flag bitnear; rw [show move (x j) (v+x j, (0:ℝ))=(v,0) from by simp [move],ofReal_mul]
         by_cases hv: cap (total (v,0)/R^2)=0
         · rw [hv,ofReal_zero,zero_mul,zero_mul]
         apply congrArg (fun q:ℂ=> (↑(cap (total (v,0)/R^2)):ℂ)*q) (bypass_value l j a hl (fun i hi=>?_))
         intro he
         refine h.flags j hi (subset_tsupport _ ?_)
         change flag x R j (x i)≠0; rw [← he]; unfold flag bitnear; rwa [show move (x j) (v+x j,(0:ℝ))=(v,0) by simp [move]]
      unfold B; rw [← integral_add_right_eq_self _ (x j), ← integral_complex_ofReal]; apply integral_congr_ae
      filter_upwards [volume.ae_ne 0] with v hv
      change (↑(leg x l 0 j (v+x j)*grad a (piece x l j χ 0) (v+x j)):ℂ)= lane _ _ _ _ _ _ * grad a (fun v => T j (0,v,0)) v
      unfold leg; rw [ofReal_mul,kernel_real _ _ _ hv,add_sub_cancel_right]; congr 1
      let f:=piece x l j χ 0
      have hhH : ContDiff ℝ ∞ (uncurry (piece x l j χ)):= piece_smooth x l j (χ:=χ) (flag_smooth (x:=x) (R:=R) j) (fun i hi=>h.flags j hi)
      have hm:ContDiff ℝ ∞ f:= hhH.comp (f:=fun v:E4=> ((0:ℝ),v)) (by fun_prop)
      have he(v:E4): DifferentiableAt ℝ f v:= hm.differentiable (by simp) v
      rw [funext ht]; change (↑(fderiv ℝ f (v+x j) (basis a)):ℂ)= fderiv ℝ (fun v=> ↑(f (v+x j))) v (basis a)
      rw [fderiv_comp_add_right (f:=fun v:E4=> (↑(f v):ℂ)) (x j)]; exact Eq.symm (DFunLike.congr_fun (ofRealCLM.hasFDerivAt.comp (v+x j) (he _ |>.hasFDerivAt)).fderiv _)
   rw [←HG]; exact (continuous_ofReal.continuousAt (x:=A-B)|>.tendsto).comp (bills x l j a (χ:=χ) (flag_smooth (x:=x) (R:=R) j) (h.flag_cost j) (fun i hi=>h.flags j hi) (h.flag_uniq j) hc)

end YM.SchemeConversionRG11.FirstMS.Triad
