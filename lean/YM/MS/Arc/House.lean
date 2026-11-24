import YM.MS.Arc.Estate
import YM.MS.Arc.Terrain
/-!
# House: forced fderiv holomorphic by polynomial-tempered bounds

Uniform on each closedBall admitted. Use only finite-dimensional external charts
 (suffices for projected result on all charts). -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Arc
open Function Filter Set Finset MeasureTheory Real Metric
open scoped Topology ContDiff Interval
variable {E F I: Type}[NormedAddCommGroup E][NormedSpace ℝ E]
 [NormedAddCommGroup F][NormedSpace ℂ F][NormedSpace ℝ F][IsScalarTower ℝ ℂ F][CompleteSpace F]
-- local growth round complex dimension
abbrev seeing (f:ℂ→ E→F)(c:ℂ)(R:ℝ):= veg 0 (fun i:closedBall c R=> f i) 1
def hards (D:Set ℂ)(f:ℂ→ E→F): Prop:= ∀ c R,0<R→ closedBall c R⊆D→ seeing f c R
def keys (D:Set ℂ)(f:ℂ→ E→F): Prop:=∀ p, Forest D fun z=>f z p
structure Plots (D:Set ℂ)(f:ℂ→ E→F): Prop where
    span: hards D f
    root: keys D f
variable {f:ℂ→ E→ F}{D:Set ℂ}{c:ℂ}{R:ℝ}
omit [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F] in
lemma plotnear (hp:hards D f)(h:IsOpen D)(hc:c∈D): ∃ R:ℝ,0<R∧closedBall c R ⊆ D∧ seeing f c R:= by
   obtain ⟨R,hR,ht⟩:=Metric.mem_nhds_iff.mp (h.mem_nhds hc); have he:closedBall c (R/2)⊆D:=Subset.trans (closedBall_subset_ball (by linarith)) ht; exact ⟨R/2,half_pos hR,he,hp c _ (half_pos hR) he⟩
-- uniform approximate
omit [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F] in
lemma bill_2 (h:seeing f c R) (x v:E): ∃ K:ℝ,0<K∧∀ y∈closedBall c R,∀ t:ℝ,0<t→t≤1→
    ‖(t:ℝ)⁻¹ • (f y (x+t • v)-f y x)-fderiv ℝ (f y) x v‖ ≤ K * t:= by
   let G : closedBall c R → E→ E→L[ℝ] F:= fun q=> fderiv ℝ (f q.val); let X:=‖x‖+‖v‖; have hz: veg 0 G 1:= by simpa only [cheap_length,mul_one,G] using h.fderiv
   obtain ⟨C,hC,b,hb⟩:=ride hz 1
   let M:=C*(1+X)^b; have hm:M>0:= by unfold M X; positivity
   refine ⟨1+ M*‖v‖^2,by positivity,fun y hy t ht he=>?_⟩ -- wrong indent
   let Z : closedBall c R:=⟨y,hy⟩; let ℓ:= t*‖v‖; let s:= closedBall x ℓ; have hL:0≤ℓ:=mul_nonneg ht.le (norm_nonneg _); have hx:x∈s:= mem_closedBall_self hL; have hW{p:E}(hp:p∈s): ‖p‖ ≤ X:=by
       have hE : ‖p-x‖ ≤ ℓ:=mem_closedBall_iff_norm.mp hp; unfold X; unfold ℓ at hE; apply le_trans (norm_le_insert x p); rw [norm_sub_rev]; nlinarith [norm_nonneg v] -- lemma name
   have hh : ∀ p∈s,‖G Z p-G Z x‖≤ M * ℓ:= by
       intro p hp; apply le_trans ((convex_closedBall x ℓ).norm_image_sub_le_of_norm_fderiv_le (fun q hq=> (hz.smooth Z).differentiable (by simp) q) (f:=G Z) (C:=M) ?_ hx hp); · gcongr; exact mem_closedBall_iff_norm.mp hp
       intro q hq; specialize hb Z q; simp only [Pi.zero_apply,Pi.one_apply,abs_zero, add_zero,one_mul,mul_one,norm_iteratedFDeriv_one] at hb; unfold M; apply le_trans hb; gcongr; exact hW hq -- lost hb trans
   let Y:=x+t • v; let Hx:= fderiv ℝ (f y) x v; have hY: Y-x=t • v:= by unfold Y; abel
   have hP: Y∈s:= by rw [mem_closedBall_iff_norm,hY,norm_smul,norm_of_nonneg ht.le]
   have hG:= (convex_closedBall x ℓ).norm_image_sub_le_of_norm_fderiv_le' (fun q hq=> (h.smooth Z).differentiable (by simp) q) hh hx hP; -- ht shadow; rw
   change ‖f y Y-f y x-(G Z x) (Y-x)‖≤ M*ℓ*‖Y-x‖ at hG; rw [hY,map_smul,norm_smul,norm_of_nonneg ht.le] at hG; change ‖t⁻¹ • (f y Y-f y x)-Hx‖≤_
   rw [show t⁻¹ • (f y Y-f y x)-Hx=t⁻¹ • (f y Y-f y x -t • Hx) by simp only [smul_sub, inv_smul_smul₀ ht.ne'],norm_smul,norm_of_nonneg (inv_pos.mpr ht).le]; apply le_trans (mul_le_mul_of_nonneg_left hG (inv_pos.mpr ht).le); rw [← div_eq_inv_mul,div_le_iff₀ ht]; unfold ℓ; nlinarith
-- directional hol
lemma trees_at (H:Plots D f)(hD:IsOpen D)(x v:E): Forest D (fun p=> fderiv ℝ (f p) x v):= by
    intro z hz; obtain ⟨R,hR,hL,hS⟩:= plotnear H.span hD hz; obtain ⟨C,hC,hp⟩:= bill_2 hS x v
    let V: Set ℂ:= ball z R; let T (t:ℝ)(a:ℂ):= t⁻¹ • (f a (x+t • v)-f a x); let D' z:= (fderiv ℝ (f z) x v)
    have he: TendstoUniformlyOn T D' (𝓝[>] (0:ℝ)) V := by
        apply tendstoUniformlyOn_iff.mpr; intro ε he; filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds (show (0:ℝ)< min 1 (ε/C) from lt_min zero_lt_one (div_pos he hC)))] with t ht ht' a ha; rw [dist_comm, dist_eq_norm]; exact lt_of_le_of_lt (hp a (ball_subset_closedBall ha) t ht (le_of_lt (lt_min_iff.mp (show t < min _ _ from ht')|>.1))) (by have hh:= (lt_div_iff₀ hC).mp (lt_min_iff.mp (show t < min _ _ from ht')|>.2); linarith)
    refine (he.tendstoLocallyUniformlyOn.differentiableOn (Eventually.of_forall fun t=> ?_) isOpen_ball z (mem_ball_self hR)).differentiableAt (ball_mem_nhds _ hR)
    intro p hp; have hh : p∈D:=hL (ball_subset_closedBall hp); have hx : SMulCommClass ℂ ℝ F:= inferInstance; exact (( (H.root (x+t•v) p hh).sub (H.root x p hh)).const_smul (t⁻¹)).differentiableWithinAt
open ContinuousLinearMap
variable {K Q: Type}
private def grab (A:E→L[ℝ] ℝ): F→L[ℂ](E →L[ℝ] F) where
    toFun := (smulRightL ℝ E F A)
    map_add':= map_add _
    map_smul' r x:= by ext w; exact smul_comm ..
omit [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F] in
lemma side (H:hards D f): hards D (fun i=>fderiv ℝ (f i)):= fun c R h hp=>by simpa only [cheap_length,mul_one] using (H c R h hp).fderiv -- x remove
lemma Plots.tell [FiniteDimensional ℝ E] (H:Plots D f)(hD:IsOpen D): Plots D (fun i=> fderiv ℝ (f i)):= by
    refine ⟨side H.span,?_⟩; intro x i hi; let B:=Module.finBasis ℝ E; let V (i:Fin (Module.finrank ℝ E)):= (B.coord i).toContinuousLinearMap
    rw [show (fun p=> fderiv ℝ (f p) x)=(fun z=> ∑ i, grab (V i) (fderiv ℝ (f z) x (B i))) from funext (fun z=> ?_)]
    · exact DifferentiableAt.fun_sum (fun i _=> ( grab (F:=F) (V i)).differentiableAt.comp _ (trees_at H hD x (B i) _ hi)) -- check
    let t:= fderiv ℝ (f z) x; ext w; obtain H:= congr_arg t (B.sum_repr w); rw [map_sum] at H; simp_rw [map_smul] at H; rw [_root_.sum_apply]; exact H.symm
end YM.MS.Arc
