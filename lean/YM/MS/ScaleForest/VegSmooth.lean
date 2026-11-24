import YM.MS.ScaleForest.WaveSwipe
/-!
# Continuity facts for extending to MANY sources after the one-source forests

Aim is local uniformity, in particular
on compact-away-from-contact sets. Need
scale integrals and punctured-germ extension under control BEFORE
specializing through a pin join. We will also use continuity of chart
evaluation and with IR upper cutoff. Uses elementary price facts, in the
normalization of unit-scale co-moving charts. `general_bill`: same MVT
argument as in `Arc.House`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Function Filter Real Arc MeasureTheory Rock Metric
open scoped Topology ContDiff
variable {I E F J:Type} [NormedAddCommGroup E][NormedSpace ℝ E]
   [NormedAddCommGroup F][NormedSpace ℝ F]
   {f:I→E→F}
private theorem general_bill (h:veg 0 f 1) (x v:E): ∃ K:ℝ,0<K∧∀ y,∀ t:ℝ,0<t→t≤1→
    ‖(t:ℝ)⁻¹ • (f y (x+t • v)-f y x)-fderiv ℝ (f y) x v‖ ≤ K * t:= by
   let G : I→ E→ E→L[ℝ] F:= fun q=> fderiv ℝ (f q); let X:=‖x‖+‖v‖; have hz: veg 0 G 1:= by simpa only [cheap_length,mul_one,G] using h.fderiv
   obtain ⟨C,hC,b,hb⟩:=ride hz 1
   let M:=C*(1+X)^b; have hm:M>0:= by unfold M X; positivity
   refine ⟨1+ M*‖v‖^2,by positivity,fun y t ht he=>?_⟩
   let Z : I:= y; let ℓ:= t*‖v‖; let s:= closedBall x ℓ; have hL:0≤ℓ:=mul_nonneg ht.le (norm_nonneg _); have hx:x∈s:= mem_closedBall_self hL; have hW{p:E}(hp:p∈s): ‖p‖ ≤ X:=by
       have hE : ‖p-x‖ ≤ ℓ:=mem_closedBall_iff_norm.mp hp; unfold X; unfold ℓ at hE; apply le_trans (norm_le_insert x p); rw [norm_sub_rev]; nlinarith [norm_nonneg v]
   have hh : ∀ p∈s,‖G Z p-G Z x‖≤ M * ℓ:= by
       intro p hp; apply le_trans ((convex_closedBall x ℓ).norm_image_sub_le_of_norm_fderiv_le (fun q hq=> (hz.smooth Z).differentiable (by simp) q) (f:=G Z) (C:=M) ?_ hx hp); · gcongr; exact mem_closedBall_iff_norm.mp hp
       intro q hq; specialize hb Z q; simp only [Pi.zero_apply,Pi.one_apply,abs_zero, add_zero,one_mul,mul_one,norm_iteratedFDeriv_one] at hb; unfold M; apply le_trans hb; gcongr; exact hW hq
   let Y:=x+t • v; let Hx:= fderiv ℝ (f y) x v; have hY: Y-x=t • v:= by unfold Y; abel
   have hP: Y∈s:= by rw [mem_closedBall_iff_norm,hY,norm_smul,norm_of_nonneg ht.le]
   have hG:= (convex_closedBall x ℓ).norm_image_sub_le_of_norm_fderiv_le' (fun q hq=> (h.smooth Z).differentiable (by simp) q) hh hx hP;
   change ‖f y Y-f y x-(G Z x) (Y-x)‖≤ M*ℓ*‖Y-x‖ at hG; rw [hY,map_smul,norm_smul,norm_of_nonneg ht.le] at hG; change ‖t⁻¹ • (f y Y-f y x)-Hx‖≤_
   rw [show t⁻¹ • (f y Y-f y x)-Hx=t⁻¹ • (f y Y-f y x -t • Hx) by simp only [smul_sub, inv_smul_smul₀ ht.ne'],norm_smul,norm_of_nonneg (inv_pos.mpr ht).le]; apply le_trans (mul_le_mul_of_nonneg_left hG (inv_pos.mpr ht).le); rw [← div_eq_inv_mul,div_le_iff₀ ht]; unfold ℓ; nlinarith
variable (h : veg 0 f 1)
include h

theorem squareCost {A:E} {T:ℝ} :
    ∃ C : ℝ, 0<C∧∀ i:I,∀ p∈closedBall A |T|,∀ q∈closedBall A |T|, dist (f i p) (f i q) ≤ C*dist p q:= by
   obtain ⟨C,hC,k,hp⟩:= Arc.ride h 1; simp only [Pi.zero_apply,Pi.one_apply,abs_zero,add_zero,one_mul,mul_one,norm_iteratedFDeriv_one] at hp; let U:=C*(1+(‖A‖+|T|))^k; refine ⟨ U,(by unfold U; positivity),fun i p hp' q hq=>?_⟩; rw [dist_eq_norm,dist_eq_norm]; apply (convex_closedBall A |T|).norm_image_sub_le_of_norm_fderiv_le (fun q _=> (h.smooth i).differentiable (by simp) q) _ hq hp'
   intro r hr; apply (hp i r).trans; obtain ht:= (norm_sub_norm_le r A).trans (mem_closedBall_iff_norm.mp hr); unfold U; gcongr; linarith

variable [TopologicalSpace I] (he : ∀ p, Continuous (fun i=> f i p))
include he

theorem vegAt {x:J→I} {v:J→E} {A:E} {y:I} {s:Filter J} (hx : Tendsto x s (𝓝 y)) (hv : Tendsto v s (𝓝 A)) :
    Tendsto (fun i=> f (x i) (v i)) s (𝓝 (f y A)) := by
   obtain ⟨C,hC,hP⟩:= squareCost (A:=A) (T:=1) h; simp only [abs_one] at hP; apply Metric.tendsto_nhds.mpr; intro ε hε;
   have hp := hv.eventually (Metric.closedBall_mem_nhds A (show (0:ℝ)<1 from zero_lt_one))
   have hm : Tendsto (fun i=> C*dist (v i) A + dist (f (x i) A) (f y A)) s (𝓝 0) := by simpa only [Function.comp_def,dist_self, mul_zero,add_zero] using ((hv.dist (b:=A) tendsto_const_nhds).const_mul C).add ((((he A).tendsto y).comp hx).dist (b:=f y A) tendsto_const_nhds)
   filter_upwards [hp,hm.eventually (gt_mem_nhds hε)] with i hi hQ; exact lt_of_le_of_lt ((dist_triangle _ (f (x i) A) _).trans (add_le_add_left (hP (x i) (v i) hi A (Metric.mem_closedBall_self zero_le_one)) _)) hQ

theorem continuousVeg : Continuous (fun p : I×E=> f p.1 p.2):= continuous_iff_continuousAt.mpr (fun _=> vegAt h he continuousAt_fst continuousAt_snd)

theorem veg_cont (p:J→I) [TopologicalSpace J] (v:J→E) (hp:Continuous p) (hx:Continuous v) : Continuous (fun i=> f (p i) (v i)) := (continuousVeg h he).comp (hp.prodMk hx)

open ContinuousLinearMap
variable [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem plantAt (p v:E): Continuous (fun i=> (fderiv ℝ (f i) p) v) := by
   let U(t:ℝ)(i:I):F:= t⁻¹ • (f i (p+t • v)-f i p)
   let V(i:I):F:=(fderiv ℝ (f i) p) v
   obtain ⟨C,hC,hV⟩:= general_bill h p v
   have hp : TendstoUniformly U V (𝓝[>] (0:ℝ)) := by
      apply Metric.tendstoUniformly_iff.mpr; intro ε he; filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (gt_mem_nhds (lt_min (show (0:ℝ)<1 from zero_lt_one) (div_pos he hC)))] with t ht ht' y; rw [dist_comm, dist_eq_norm]; obtain ⟨h1,h2⟩:= lt_min_iff.mp (show t< min _ _ from ht'); exact lt_of_le_of_lt (hV y t ht h1.le) (by have hh: t*C< ε := (lt_div_iff₀ hC).mp h2; rwa [mul_comm C])
   exact hp.continuous ((Eventually.of_forall fun t:ℝ=> ((he _).sub (he _)).const_smul t⁻¹).frequently)

theorem plant (p:E) : Continuous (fun i=> fderiv ℝ (f i) p) := by
   let B:= Module.finBasis ℝ E; let L (i:Fin (Module.finrank ℝ E)):= (B.coord i).toContinuousLinearMap
   rw [show (fun i=> fderiv ℝ (f i) p)=(fun z=>∑ i:Fin (Module.finrank ℝ E), smulRightL ℝ E F (L i) (fderiv ℝ (f z) p (B i))) from funext (fun z=>?_)]
   · exact continuous_finsetSum _ (fun i _=> ((smulRightL ℝ E F (L i)).continuous).comp (plantAt h he p (B i)))
   let t:= fderiv ℝ (f z) p; ext w; obtain h:= congr_arg t (B.sum_repr w); rw [map_sum] at h; simp_rw [map_smul] at h; rw [_root_.sum_apply]; exact h.symm

theorem iteratedPlant (p:E) (j:ℕ) : Continuous (fun i=> iteratedFDeriv ℝ j (f i) p) := by
   induction j generalizing F with
   | zero=> simp_rw [iteratedFDeriv_zero_eq_comp]; exact (continuousMultilinearCurryFin0 ℝ E F).symm.continuous.comp (he p)
   | succ j ih=>
      simp_rw [iteratedFDeriv_succ_eq_comp_right]; exact (continuousMultilinearCurryRightEquiv' ℝ _ _ _).symm.continuous.comp
        (ih (f:=fun i=>fderiv ℝ (f i)) (by simpa only [cheap_length,mul_one] using h.fderiv) (plant h he))
end YM.MS.ScaleForest
