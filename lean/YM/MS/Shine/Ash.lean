import Mathlib.Analysis.Complex.RemovableSingularity
import YM.MS.Arc.Terrain
import YM.MS.Shine.Led

set_option autoImplicit false
noncomputable section
namespace YM.MS.Shine
open Set Filter Function Finset MeasureTheory Metric Arc Real Complex
open scoped Topology ContDiff
variable {A I E F:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
variable {c:ℂ} {R T:ℝ} {f:ℂ→ E→F} {x:I→ℂ}
omit [FiniteDimensional ℝ E] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] in
lemma uGrab {f:I→E→F}(h:veg 0 f 1)(φ:A→I) : veg 0 (fun i=> f (φ i)) 1:= hike (fun i=>h.smooth (φ i)) (fun j=> by obtain ⟨C,hC,b,hb⟩:= ride h j; exact ⟨C,hC,b, fun i p=> hb (φ i) p⟩ ) -- closes
omit [FiniteDimensional ℝ E] in
lemma uWore {f:I→E→F}(h:veg 0 f 1)(hc:0<T)(hp:∀ i,‖x i‖≤T): veg 0 (fun i p=>x i • f i p) 1:= by
   refine hike (fun i=> (h.smooth i).const_smul _) (fun j=> ?_); obtain ⟨C,hC,b,hb⟩:= ride h j; refine ⟨T*C,mul_pos hc hC,b,fun i p=>?_⟩; rw [iteratedFDeriv_const_smul_apply' (ContDiff.contDiffAt ( (h.smooth i).of_le (by exact_mod_cast le_top))),norm_smul]; refine (mul_le_mul (hp i) (hb i p) (norm_nonneg _) hc.le).trans ?_; rw [mul_assoc T,mul_assoc T,mul_assoc C]
lemma Stir {S: Set ℂ} (hk:IsCompact S)(hn:S.Nonempty)(ht:S⊆ball 0 R): ∃ T:ℝ,0≤T∧ T<R∧S⊆closedBall (0:ℂ) T:= by
    obtain ⟨x,hx,hM⟩:= hk.exists_isMaxOn hn continuous_norm.continuousOn; refine ⟨‖x‖,norm_nonneg x,by simpa using ht hx,fun p hp=>?_⟩; simpa using hM hp
lemma Rim {f:ℂ→ E→ℂ} (W:ℝ)(hT:T<R)(hp:W<T)(hW:0≤W)(h:keys (ball 0 R) f)(hv:veg 0 (fun i:sphere (0:ℂ) T=> f i) 1) : seeing f 0 W := by
    let G:=ball (0:ℂ) T; have hc:0<T:=hW.trans_lt hp; have hP := closedBall_subset_ball (x:=(0:ℂ)) hT; let μ:= volume.restrict (Icc (0:ℝ) (2*π)); haveI:IsFiniteMeasure μ := inferInstanceAs (IsFiniteMeasure (volume.restrict (Icc (0:ℝ) (2*π)))); let c:=circleMap 0 T; let d:= (2*π*I:ℂ)⁻¹; have hB (x:closedBall (0:ℂ) W): (x:ℂ)∈G:= closedBall_subset_ball hp x.property; have hm (s:ℝ): c s ∈ sphere (0:ℂ) T:= circleMap_mem_sphere _ hc.le s; let U (x:closedBall (0:ℂ) W)(s:ℝ) := deriv c s*(c s-x.val)⁻¹; let H (x:closedBall (0:ℂ) W)(t:ℝ)(p:E): ℂ:= U x t • f (c t) p
    have hu (p:E): DiffContOnCl ℂ (fun z=> f z p) G := ⟨fun z hz=> (h p z (hP (ball_subset_closedBall hz))).differentiableWithinAt,(by unfold G; rw [closure_ball _ hc.ne']; exact fun z hz=> (h p z (hP hz)).continuousAt.continuousWithinAt )⟩
    have hF : (fun (x:closedBall (0:ℂ) W)=> f x)=(fun x p=> d • (∫ s,H x s p ∂μ)):= by
        funext x p; obtain he:=(hu p).two_pi_i_inv_smul_circleIntegral_sub_inv_smul (hB x); rw [circleIntegral_def_Icc] at he; unfold μ H U; simp only [mul_smul]; exact he.symm
    have hU : veg 0 (fun (i:closedBall (0:ℂ) W ×ℝ)=> H i.1 i.2) 1 := by
         refine uWore (x:=fun i:closedBall (0:ℂ) W×ℝ=> U i.1 i.2) (uGrab hv fun i:closedBall (0:ℂ) W × ℝ=>(⟨c i.2,hm i.2⟩:sphere (0:ℂ) T)) (div_pos hc (sub_pos.mpr hp)) (fun ⟨x,t⟩=>?_); unfold U c; rw [norm_mul,norm_inv,deriv_circleMap,norm_mul,norm_I,norm_circleMap_zero,abs_of_pos hc,mul_one,← div_eq_mul_inv]; have he : T-W ≤ ‖c t-x.val‖:= by obtain hZ:= norm_sub_norm_le (c t) x.val; rw [show ‖c t‖=T by simp [c,norm_circleMap_zero,abs_of_nonneg hc.le]] at hZ; have hl:‖x.val‖≤ W:= (by simpa only [mem_closedBall,dist_zero_right] using x.property); linarith
         exact div_le_div_of_nonneg_left hc.le (sub_pos.mpr hp) he
    have he : veg 0 (fun x p=> ∫ t,H x t p ∂μ) 1:= by
        refine plush (integrable_const (μ:=μ) (1:ℝ)) (g:=H) (fun x=> Eventually.of_forall fun t=> hU.smooth (x,t)) (fun x p=>?_) ?_
        · have he: Continuous fun t=> U x t:= by simp_rw [U,c,deriv_circleMap]; apply Continuous.mul (by fun_prop); apply (Continuous.sub (continuous_circleMap ..) continuous_const).inv₀; intro s; exact sub_ne_zero.mpr fun h=> ((show c s∉ G from sphere_disjoint_ball.notMem_of_mem_left (hm s))) ((show _ = c s from h.symm) ▸ hB x) -- h
          exact (he.smul (( (hu p).2).comp_continuous (continuous_circleMap ..) (fun x=> by rw [show closure G=closedBall 0 T by unfold G; rw [closure_ball _ hc.ne']]; exact sphere_subset_closedBall (hm x)))).aestronglyMeasurable
        intro j; obtain ⟨C,hC,b,hb⟩:=ride hU j; exact ⟨C,hC,b,fun i=>Eventually.of_forall fun t p=>by simpa using hb (i,t) p⟩
    unfold seeing; rw [hF]; exact uWore he (T:=max 1 ‖d‖) (lt_max_of_lt_left zero_lt_one) (fun _=>le_max_right ..)
lemma Prominent {f:ℂ→ E→ℂ} (h:keys (ball 0 R) f)(he:∀ r:ℝ,0 < r → r < R → veg 0 (fun i:sphere (0:ℂ) r=>f i) 1): Plots (ball 0 R) f := by
   refine ⟨fun c T hr hu=>?_,h⟩; obtain ⟨t,ht,hR,hp⟩:= Stir (isCompact_closedBall c T) ⟨c,mem_closedBall_self hr.le⟩ hu; obtain ⟨v,hv,hT⟩:= exists_between hR; exact uGrab (Rim t hT hv ht h (he v (ht.trans_lt hv) hT)) fun i:closedBall c T=>⟨i.val,hp i.property⟩
def reb (f:ℂ→ E→F)(z:ℂ)(p:E): F:= dslope (fun s=>f s p) 0 z
omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] in
lemma reb_nn (h:c≠0): reb f c=(fun p=> c⁻¹ • (f c p-f 0 p)):= by funext p; rw [reb,dslope_of_ne _ h,slope]; simp
lemma rebot {f:ℂ→ E→ℂ} (hr:0<R)(h:Plots (ball 0 R) f): Plots (ball 0 R) (reb f):= by
   refine Prominent (fun p i hi=> ((Complex.differentiableOn_dslope (ball_mem_nhds _ hr)).mpr (fun q hq=>(h.root p q hq).differentiableWithinAt )).differentiableAt (isOpen_ball.mem_nhds hi)) ?_
   intro r hr ht; have hp:=h.span _ _ hr (closedBall_subset_ball ht); let V:=sphere (0:ℂ) r; have hm (x:V): ‖(x:ℂ)‖=r:= (by simpa only [V,mem_sphere,dist_zero_right] using x.property); have hu(i: V): (i:ℂ)≠0:= norm_ne_zero_iff.mp (Ne.symm (lt_of_lt_of_le hr (hm i).ge).ne); simp_rw [reb_nn (hu _)]; apply uWore (T:=r⁻¹) ( Costs.sub (uGrab hp (fun i:V=>(⟨i.val,sphere_subset_closedBall i.property⟩))) (uGrab hp fun i:V=>⟨(0:ℂ),mem_closedBall_self hr.le⟩)) (inv_pos.mpr hr); exact fun i=> le_of_eq (by rw [norm_inv,hm])
end YM.MS.Shine
