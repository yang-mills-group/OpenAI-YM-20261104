import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Intrados
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Ratio
/-!
 # Crop compositions by actual double-zero. Downstream used to take brush costs at first
 power even on sensors where field symmetries permit next. One part is available uniformly
 on full `E6.Camera` ledger. Does NOT alter quota grading globally.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Orifice
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson MeasureTheory Matrix
open ConnectedActivityE6.Coat
open ConnectedActivityE6 Blaze Silica
open scoped Topology ContDiff Matrix.Norms.Frobenius Classical
section
variable {U V : Type} [NormedAddCommGroup V][NormedSpace ℝ V] [NormedAddCommGroup U][NormedSpace ℝ U]
-- reusable germ.Ready jets. Full v cost squared, no occupancy factors other axes.
variable {k:ℕ}(g:V→ℝ)(q:V→L[ℝ]V) {x:V}
lemma rescue (hf:ContDiffAt ℝ ω g 0)(h:g 0=0)(hV:fderiv ℝ g 0=0) {n:ℕ}:
   ∃ u C:ℝ,0<u ∧ u≤1 ∧ 1≤C ∧ ∀ w, 0≤w → w≤u→ ∀ v:V, ‖v‖≤1 → Brush n (C*w^2) 1 (fun v=>g (w • v)) v:=by
    obtain ⟨C,hC,hg⟩:=Brush.neighborhood (k:=n+2) (0:V) (hf.of_le le_top)
    obtain ⟨r,hr,hR⟩:=Metric.nhds_basis_closedBall.eventually_iff.mp hg
    let u:=min r (1:ℝ)
    refine ⟨u,1+C,lt_min hr zero_lt_one,min_le_right ..,le_add_of_nonneg_right hC.le,fun w hw he v hh=>?_⟩
    have hN {i:V}(ht:‖i‖≤w):Brush (n+2) C 1 g i:=hR (show i∈Metric.closedBall 0 r from Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact (ht.trans he).trans (min_le_left ..)))
    have hS {i:V}(h:i∈Metric.closedBall (0:V) w):‖i‖≤w:=by simpa only [Metric.mem_closedBall,dist_zero_right] using h
    have he'(i)(hi:i∈Metric.closedBall (0:V) w): DifferentiableAt ℝ (fderiv ℝ g) i:= (((hN (hS hi)).smaller (j:=2) (by omega)).smooth.fderiv_right (m:=(1:ℕ∞ω)) (by exact le_rfl)).differentiableAt (by simp) -- need result
    have ht(i)(hi:i∈Metric.closedBall (0:V) w): ‖fderiv ℝ (fderiv ℝ g) i‖ ≤ C:=by
       have h:= (hN (hS hi)).order 2 (by omega); rw [one_pow,mul_one] at h; rw [← norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv]; exact h -- direction
    have hV' i (hi:i∈Metric.closedBall (0:V) w): ‖fderiv ℝ g i‖≤C*w:=by
       apply le_trans _ (mul_le_mul_of_nonneg_left (hS hi) hC.le)
       simpa only [hV,sub_zero] using ((convex_closedBall (0:V) w).norm_image_sub_le_of_norm_fderiv_le he' ht (Metric.mem_closedBall_self hw) hi)
    let L:= w • ContinuousLinearMap.id ℝ V; have hL: ‖L‖≤w:=by unfold L; rw [norm_smul,Real.norm_of_nonneg hw]; exact mul_le_of_le_one_right hw ContinuousLinearMap.norm_id_le
    have hx: ‖L v‖≤w:= (ContinuousLinearMap.le_opNorm ..).trans (le_trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _)) (mul_le_of_le_one_right hw hh))
    have hy:L v∈ Metric.closedBall (0:V) w:= Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact hx)
    have hf:= (hN hx).smaller (Nat.le_add_right n 2)
    change Brush n _ 1 (g ∘ L) v
    have hh:=(Brush.reading L hf hL); rw [one_mul] at hh
    refine ⟨hh.smooth, zero_le_one,fun j hj=>?_⟩
    rw [one_pow,mul_one]; have hB : C*w^2≤(1+C)*w^2:=mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (sq_nonneg _)
    apply le_trans (b:=C*w^2) _ hB
    match j with
    | 0=>
       rw [normJ,norm_iteratedFDeriv_zero,Function.comp_apply]
       have he''(i)(hi:i∈Metric.closedBall (0:V) w): DifferentiableAt ℝ g i:=(hN (hS hi)).smooth.differentiableAt (by simp) -- edit
       have hk:=(convex_closedBall (0:V) w).norm_image_sub_le_of_norm_fderiv_le he'' hV' (Metric.mem_closedBall_self hw) hy
       rw [h,sub_zero,sub_zero] at hk; exact hk.trans ((mul_le_mul_of_nonneg_left hx (mul_nonneg hC.le hw)).trans_eq (by ring))
    | 1=>
       rw [normJ,norm_iteratedFDeriv_one,fderiv_comp v ((hf.smaller hj).smooth.differentiableAt (by simp)) L.differentiableAt,L.fderiv]
       exact (ContinuousLinearMap.opNorm_comp_le ..).trans ((mul_le_mul (hV' _ hy) hL (norm_nonneg _) (mul_nonneg hC.le hw)).trans_eq (by ring))
    | j+2=> apply (hh.order (j+2) hj).trans (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hw (he.trans (min_le_right ..)) (by omega)) hC.le)
end
section
variable {U V : Type} [NormedAddCommGroup V][NormedSpace ℝ V] [NormedAddCommGroup U][NormedSpace ℝ U]
variable {n:ℕ}(g:V→ℝ)(h:ContDiffAt ℝ ω g 0)(hG:g 0=0)(hD:fderiv ℝ g 0=0)
include h hG hD
lemma tender : ∃ u K:ℝ,0<u∧u≤1∧1≤K ∧ ∀ (U:Type)[NormedAddCommGroup U][NormedSpace ℝ U] (f:U→V)(x:U) w, 0<w→w≤u→ Brush n w 1 f x → Brush n (K * w^2) 1 (fun x=>g (f x)) x:=by
  obtain ⟨u,C,hp,hC,hM,hT⟩:= rescue g h hG hD (n:=n)
  let k : ℝ:= n.factorial*C*(1+(1+1))^n
  refine ⟨u,k,hp,hC,?_,fun U _ _ f x r hr he h=>?_⟩
  · have hn : 1 ≤ (n.factorial:ℝ):=by exact_mod_cast Nat.factorial_pos n
    unfold k; exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hn hM) (one_le_pow₀ (by norm_num))
  let g' (p:V):= g (r • p); let f' (x:U):= r⁻¹ • f x
  have hf:Brush n 1 1 f' x:=by simpa only [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr),inv_mul_cancel₀ hr.ne'] using h.smul r⁻¹
  have he:= (hf.pine (hT r hr.le he _ hf.bound)).trim
  have hR:(fun x=> g' (f' x))=fun i=>g (f i):=by ext p; simp [g',f',smul_smul,hr.ne']
  rw [(show _=_ from hR),show n.factorial * (C * r^2)*(1+((1+1)*1:ℝ))^n=k*r^2 by unfold k; ring] at he -- defeq function rewrites?
  exact he
end
-- true gauge.Haar angular cost
open Precision Next.SectorChange
lemma varnish (G:Gauge) (Ñ:ChartRatio G)(hÑ:LocalRatio Ñ):fderiv ℝ (fun x=>Real.log (Ñ.J x)) 0=0:=by
  let u (x:G.Color):=Real.log (Ñ.J x)
  have he: ContDiffAt ℝ ω u 0 := ((hÑ.germ 0 (Metric.mem_ball_self hÑ.patch)).log (by rw [hÑ.anchored]; norm_num))
  apply ContinuousLinearMap.ext; intro x
  have h': (fderiv ℝ u 0) x=0:= (YM.Push.side u he.analyticAt.differentiableAt x).unique (still_even he.analyticAt.differentiableAt (Filter.mem_of_superset (Metric.ball_mem_nhds (0:G.Color) hÑ.patch) (fun p hp=> congr_arg Real.log (ratio_even hÑ hp).symm)) x)
  exact h'

lemma puffs2 (G:Gauge)(L:Side)(χ:Push.SectorMeasure.Chi)(a:ℝ){Ñ : Precision.ChartRatio G} (hÑ:LocalRatio Ñ){V : ℝ→ℝ}(h:Rate G L (-(1/2)) V)(n:ℕ) :
    ∃ X, Rate G L (-1) X ∧ ∀ᶠ x in atTop, ∀ (c f:Side) (S : StepData c f) (T : Tube G S) (F : Forest S.ratio)
      (Q : Coat T F), Q.x=x → S.patch.L=L → Q.χ=χ → ∀ (U:Type) [NormedAddCommGroup U] [NormedSpace ℝ U]
      (z : Air f G) (β : ℝ) (y:U) (O : U→ Config G c) (f':U→ Directions G f) (W:U→ Air f G), Clutch Q z a β (V x) y n O f' W →
      ∀ i, Brush n (|X x|) 1 (fun y=> Q.gentry Ñ a (f' y) i) y :=by
  obtain ⟨A,hA,hp⟩:= Clutch.kernels G L χ h n (2*a)
  let g (x:G.Color):= Real.log (Ñ.J x)
  have he: ContDiffAt ℝ ω g 0 := ((hÑ.germ 0 (Metric.mem_ball_self hÑ.patch)).log (by rw [hÑ.anchored]; norm_num))
  obtain ⟨u,K,hu,h',hh,hG⟩:= tender (n:=n) g he (by simp [g,hÑ.anchored]) (varnish G Ñ hÑ)
  let X x:= |V x|+2*(2*a)*Pressure.fiery G x L
  have hb{r : ℝ}{X: ℝ→ℝ}(h : Rate G L r X): Rate G L r (fun x=> |X x|) := h.compare (Eventually.of_forall fun i=>(abs_abs _).le)
  let D x:=1+(|A x|+1)
  have hx : Rate G L (-(1/2)) X:= (hb h).add (Rate.flame.mul_left _)
  have hD : Rate G L 0 (fun x=> D x^n):=by simpa only [zero_mul] using! (((Rate.const 1).add ((hb hA).add (Rate.const 1))).pow n)
  refine ⟨fun x=> K*(X x)^2 * D x^n,?_,?_⟩
  · convert! (((hx.pow 2).mul_left K).mul hD) using 1; norm_num
  filter_upwards [hp,hx.below (by norm_num) _ hu] with x hp hx c f S T F Q hQ hL hχ U _ _ z β y O f' W H i
  by_cases hN: (fun y=>Q.cone (2*a) (f' y) i)=ᶠ[𝓝 y] fun _=>0
  · exact Brush.zi (hN.mono fun y h=> by change Q.cone _ _ _*_=_; rw [show Q.cone _ _ _=0 from h,zero_mul]) (abs_nonneg _) zero_le_one
  have hm:0<2*a*Q.t :=by rw [mul_assoc]; exact mul_pos (by norm_num) H.pulse
  have ht':=hp _ _ S T F Q hQ hL hχ hm U z _ β y O f' W H i
  have hf(i):0≤|V i|:=abs_nonneg _
  rw [show Q.t = Pressure.fiery G x L from by unfold Coat.t; rw [hQ,hL]] at hm
  have hT:0< X x:=by unfold X; linarith [hf x]
  have hh':Brush n (X x) 1 (fun y=>f' y i) y:=by
    have h:= (H.fostered i (show 0<2*a*Q.t from by rw [mul_assoc]; exact mul_pos (by norm_num) H.pulse) hN).2; unfold Coat.t at h; rw [hQ,hL] at h
    exact h.climb (add_le_add_left (le_abs_self _) _) le_rfl
  have hF:=hG U _ y (X x) hT ((le_abs_self _).trans hx) hh'
  exact ((ht'.paints hF).trim).climb (by simpa only [one_mul,D] using (le_abs_self (K*X x^2*D x^n))) le_rfl
end YM.RG12.Orifice
