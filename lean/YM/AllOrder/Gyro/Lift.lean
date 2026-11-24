import YM.AllOrder.Gyro.Pulse
import YM.AllOrder.Gyro.Period
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Gyro
open Function Filter Lattice RG Wilson Push Push.AbsoluteSums Precision AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration PhysicalNext MeasureTheory
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{n m:Side}{p:BudgetPoint}(d:RegularAddress n){f:Config G n→ℝ}(g:G.Simple)(H:p.Regular d.support f) (x y:Site n) (b:PlaqAxes)
open Averaging
variable {X : Listing G n}{v:Collection.Source G n}{Y : Listing G n}{u:Collection.Source G n}{c w c' w' β ζ η α:ℝ} (h:Collection.Local X p v c w)(h':Collection.Local Y p u c' w') (R:PathData G)(F:Clip)(ht:earlyValue X R F p v β ζ α=earlyValue Y R F p u β η α)
local notation "q"=>X.read v
local notation "Q"=>Y.read u
include h g
lemma livery (v':Directions G n) (hD:∀ o,p.dirBound o v'): Tendsto (fun t:ℝ=>((q).additive p (line v' t)-(q).additive p 1)/t^2) (𝓝[≠] 0) (𝓝 ((∑' i,logHessian (v.logRead i) v' v'/2))) ∧ Summable (fun i=> logHessian (v.logRead i) v' v'/2):= by
  obtain ⟨b,hb,hV⟩:= (q).E_total h.unweighted
  let S:=fun i=>X.reg i|>.support; let x':=fun i=>X.reg i|>.site; let g' i:= v.logRead i
  let f' : ℕ→ Config G n→ℝ:= fun i=> g' i-fun _=>v.logRead i 1
  have he i : p.Regular (S i) (f' i):= VerifiedReset.reg_sub (h.smooth i) (VerifiedReset.reg_const _)
  have hm i:p.supBounds (x' i) (S i) (f' i) (b i*2):=sup_le (sup_sub (h.smooth i) (VerifiedReset.reg_const (v.logRead i 1)) (hV i) (sup_const ..)) (by have hℓ: |v.logRead i 1| ≤ b i:= (hV i).2 1 (flat_ok ..) [] (by simp) (by simp); linarith)
  obtain ⟨t₀,ht₀,he0⟩:= Metric.eventually_nhds_iff_ball.mp (Soft.rays_free p.threshold p.threshold_pos v')
  let k i : ℝ:= logHessian (g' i) v' v'/2
  have hr {t:ℝ} (ht:|t|<t₀) : ∀ Y:Support n, Healthy p.threshold Y (line v' t):= by intro Y; unfold Healthy; rw [he0 _ (by simpa [Metric.mem_ball,Real.dist_eq])]; exact disjoint_bot_right
  have hh i : Tendsto (fun t:ℝ=> f' i (line v' t)/t^2) (𝓝[≠] 0) (𝓝 (k i)):= by
     have he' : f' i 1=0:= sub_self _; convert hessian_limit g (he i) he' v' using 2; unfold k f' g'; rw [hessian_sub (h.smooth i) (reg_const _),hessian_zero,sub_zero]
  have hl : ∀ᶠ t:ℝ in 𝓝[≠] 0, ∀ i, ‖f' i (line v' t)/t^2‖ ≤ b i*2:= by
     filter_upwards [Eventually.filter_mono nhdsWithin_le_nhds (Metric.ball_mem_nhds (0:ℝ) ht₀), self_mem_nhdsWithin (a:=0) (s:=({0}:Set ℝ)ᶜ)] with t ht h₁ i
     have ht' : t ≠ (0:ℝ):= h₁; have ht₂:|t| <t₀:= by simpa [Metric.mem_ball,Real.dist_eq] using ht
     rw [norm_div,Real.norm_of_nonneg (sq_nonneg _),div_le_iff₀ (sq_pos_of_ne_zero ht')]; exact Soft.line_bound v' ht₂ (fun x hx=> hr hx _) _ (he i) (hm i) (sub_self _) g (hD _)
  refine ⟨(tendsto_tsum_of_dominated_convergence (hb.mul_right 2) hh hl).congr' ?_, Summable.of_norm_bounded (hb.mul_right 2) (fun i=>le_of_tendsto (hh i|>.norm) (hl.mono fun t ht=>ht i))⟩
  filter_upwards [Eventually.filter_mono nhdsWithin_le_nhds (Metric.ball_mem_nhds (0:ℝ) ht₀)] with t ht
  have hs x (hx:∀ i,Healthy p.threshold (S i) x):(q).additive p x=∑' i,g' i x:= tsum_congr fun i=> masked_eq _ _ _ _ (hx i)
  have hi x (hx:∀ i,Healthy p.threshold (S i) x):Summable fun i=>g' i x:= Summable.of_norm_bounded hb fun i=>(hV i).2 x (hx i) [] (by simp) (by simp)
  rw [hs _ (fun i=>hr (show |t| <t₀ from (by simpa [Metric.mem_ball,Real.dist_eq] using ht)) _),hs _ (fun _=>flat_ok ..),← (hi _ (fun i=>hr (show |t| <t₀ from (by simpa [Metric.mem_ball,Real.dist_eq] using ht)) _)).tsum_sub (hi _ (fun _=>flat_ok ..))]
  exact tsum_div_const
-- exact near orbit equality only need exponential part no path price; health global.
def parallel (X:Listing G n)(v:Collection.Source G n)(Y:Listing G n)(u:Collection.Source G n)(p:BudgetPoint):Prop:= ∃ c:ℝ, ∀ U:Config G n, flags p.threshold U=∅→ (X.read v).additive p U=(Y.read u).additive p U+c -- notation points shadow
omit g h
include ht
lemma parallel_of_equal : parallel X v Y u p:= by
 refine ⟨(ζ-η)*Fintype.card (Site n),fun U hU=>?_⟩
 have hz : Real.exp (ζ*Fintype.card (Site n)-R.inChannels F p β U-(q).additive p U)*(q).gas p U * Real.exp (-α*receipt R F p U)= Real.exp (η*Fintype.card (Site n)-R.inChannels F p β U-(Q).additive p U)*(Q).gas p U * Real.exp (-α*receipt R F p U):= congr_fun ht U
 rw [(q).gas_one _ hU,(Q).gas_one _ hU,mul_one,mul_one] at hz -- .. syntax
 linarith only [Real.exp_injective (mul_right_cancel₀ (Real.exp_pos _).ne' hz)]
variable (hp : parallel X v Y u p)
omit ht
include hp h h' g
lemma duo (D:Directions G n)(hD:∀ o,p.dirBound o D): (∑' i,logHessian (v.logRead i) D D/2)=∑' i, logHessian (u.logRead i) D D/2:= by
  refine tendsto_nhds_unique_of_eventuallyEq (livery g h D hD|>.1) (livery g h' D hD|>.1) ?_
  obtain ⟨c,hc⟩:= hp; filter_upwards [Eventually.filter_mono nhdsWithin_le_nhds (Soft.rays_free p.threshold p.threshold_pos D)] with t ht
  rw [hc _ ht,hc _ (by simp [UVNext.CouplingReset.flags_one])]; ring
lemma no_garb(x y:Site n): (∑' i, logHessian (v.logRead i) (esc G b x) (esc G b y)) = ∑' i,logHessian (u.logRead i) (esc G b x) (esc G b y):= by
 let T := p.threshold; let z x:= (T/2) • esc G b (x:Site n); let d:=z x+z y
 have he o y i: ‖z y i‖≤ (p.threshold*(1+(separation i.1 (o:Site n):ℝ))^p.power)/2:= by
    have ht:=esc_bound g b p o y i; have ht':0<T:= p.threshold_pos; unfold z; rw [Pi.smul_apply,norm_smul,Real.norm_of_nonneg (by positivity)]; rw [Pi.smul_apply,norm_smul,Real.norm_of_nonneg p.threshold_pos.le] at ht; unfold T; linarith
 have hδ o : p.dirBound o d := fun i=>(norm_add_le ..).trans (by linarith only [he o x i,he o y i]); have hv x' o:p.dirBound o (z x'):= fun i=> by linarith [he o x' i, norm_nonneg (z x' i)]
 let u0 (F:Pot G n) h:=logHessian F h h/2; let g₀ (F:Pot G n):=logHessian F (esc G b x) (esc G b y)
 have hh (F:Pot G n)(e:Support n)(H:p.Regular e F): u0 F d= u0 F (z x)+u0 F (z y)+(T/2)^2*g₀ F:= by
    unfold d u0 g₀; simp only [hessian_eq,map_add,add_apply]; unfold z; simp only [map_smul,smul_apply, ← hessian_eq,smul_eq_mul]; rw [hessian_symm H (esc G b y) (esc G b x)]; ring
 have hr := duo g h h' hp d hδ
 have he' := fun i=> hh _ _ (h.smooth i); have hu' := fun i=> hh _ _ (h'.smooth i)
 change (∑' i,u0 (v.logRead i) d) = ∑' i,u0 (u.logRead i) d at hr
 simp only [he',hu'] at hr
 unfold u0 g₀ at hr; rw [Summable.tsum_add ((livery g h _ (hv x)|>.2).add (livery g h _ (hv y)|>.2)) ((scorebill g h b x y).mul_left _), Summable.tsum_add ((livery g h' _ (hv x)|>.2).add (livery g h' _ (hv y)|>.2)) ((scorebill g h' b x y).mul_left _), Summable.tsum_add (livery g h _ (hv x)|>.2) (livery g h _ (hv y)|>.2),Summable.tsum_add (livery g h' _ (hv x)|>.2) (livery g h' _ (hv y)|>.2),tsum_mul_left,tsum_mul_left,duo g h h' hp _ (hv x),duo g h h' hp _ (hv y)] at hr
 exact mul_left_cancel₀ (show (T/2)^2≠0 from by have hw:0<T:=p.threshold_pos; positivity) (add_left_cancel hr)
end YM.AllOrder.Gyro
