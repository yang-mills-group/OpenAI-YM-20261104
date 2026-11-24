import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Normed.Module.FiniteDimension
/-!
## Collecting the derivative in separated slots
 -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.FVA2.Poesy.Rails
open Filter Topology Metric Function Set Asymptotics
variable {I E F:Type} [NormedAddCommGroup E][NormedAddCommGroup F][NormedSpace ℝ E][NormedSpace ℝ F][Fintype I] [FiniteDimensional ℝ E]
variable {U: Set E}{B:ℝ}{f:E→F}{F': I→E→F} {x y:E} (v: Module.Basis I ℝ E)
def canes (p:E) (x:E) (a:Finset I) : E:= p+∑ i∈a, v.coord i ( x-p ) • ( v i )
abbrev co (i:I): E→L[ℝ]ℝ:=LinearMap.toContinuousLinearMap ( v.coord i )
def worth (a:Finset I):ℝ:= ∑ i∈a, ‖co v i‖
open scoped Classical
lemma here (c:ℝ)(h:0<c): ∀ᶠ y in 𝓝 x,∀ a:Finset I, canes v x y a∈ ball x c:= by
    refine eventually_all.mpr fun a=>?_ ; have hx: Continuous (fun y=> canes v x y a):= continuous_const.add ( continuous_finsetSum a (fun i _=> ( ( ( co v i ).continuous.comp (continuous_id.sub continuous_const ) ).smul continuous_const )) ); have he: canes v x x a=x:= by simp [canes]
    exact hx.continuousAt.tendsto.eventually (isOpen_ball.mem_nhds (show canes v x x a∈_ from by rw [he]; exact mem_ball_self h)) -- enough
omit [FiniteDimensional ℝ E] in
lemma along {y r:E}{t:ℝ}{s:F}(h : HasLineDerivAt ℝ f s (y+t • r) r) : HasDerivAt (fun u:ℝ=>f (y+u • r)) s t:= by
    let X(u:ℝ):=u-t; have hx:X t=0:= sub_self _; let F(u:ℝ):= f ( y + t • r + u • r ); have hp: HasDerivAt X 1 t:= ( hasDerivAt_id' t ).sub_const t; have hg : HasDerivAt F s ( X t ) := hx.symm ▸ (show HasDerivAt F s 0 from h); obtain he:=hg.scomp _ hp;
    have ht : F ∘ X=( fun u:ℝ=>f (y+u •r)) := by unfold F X; ext u; simp only [comp_apply,sub_smul]; congr 1; abel;
    rwa [ht,one_smul] at he
omit [FiniteDimensional ℝ E] in
lemma single_step (c:ℝ){X:E}{g:E→ F}{r:E}{v0: E→F} (hu: Convex ℝ U)(he:X∈U)(hf:X+c • r∈U)(H:∀ x∈U,HasLineDerivAt ℝ g (v0 x) x r)(hM:∀ x∈U, ‖v0 x‖≤B): ‖g ( X+c • r )-g X‖≤ ‖c‖*B:= by
    let Y:=c • r; let y(t:ℝ):= X+t • Y; let S:= Set.Icc (0:ℝ) 1; have hy :∀ t∈S,y t∈ U:= by
       intro t ht; obtain ⟨ht,h⟩:= ht; have hh: (1-t) • X+t • (X+ c • r)=y t:= by unfold y Y; simp only [sub_smul,smul_add,one_smul]; abel
       exact hh ▸ hu he hf (sub_nonneg.mpr h) ht (sub_add_cancel 1 t)
    have hp : ∀ t∈S, HasDerivAt (fun t:ℝ=> g (y t)) ( c • v0 (y t) ) t:= fun t ht=>along ((H _ (hy _ ht)).smul c)
    have h : ∀ t∈ S, ‖c • v0 ( y t )‖≤ ‖c‖*B:= fun t ht=>le_trans (norm_smul .. |>.le) (mul_le_mul_of_nonneg_left (hM _ (hy _ ht)) ( norm_nonneg _ )); convert norm_image_sub_le_of_norm_deriv_le_segment' ( fun t ht=>(hp t ht).hasDerivWithinAt ) (fun t ht=> h t ⟨ht.1, ht.2.le⟩) _ ( show (1:ℝ)∈ S from ⟨zero_le_one,le_rfl⟩ ) using 1 <;> simp [y,Y]
lemma credit (hp:∀ᶠ y in 𝓝 x, ∀ i:I, HasLineDerivAt ℝ f ( F' i y ) y ( v i ) ∧ ‖F' i y‖ ≤ B ) (hB:0≤B) : ∀ᶠ y in 𝓝 x, ‖f y - f x‖ ≤ B * worth v Finset.univ * ‖y-x‖ := by
    obtain ⟨d,hD,H⟩:= Metric.mem_nhds_iff.mp hp; filter_upwards [here v ( x:=x ) d hD] with y hy;
    suffices hz : ∀ a:Finset I, ‖f (canes v x y a)-f x‖ ≤ B * worth v a * ‖y - x‖ by
        apply le_trans (le_of_eq _) (hz _); rw [ canes,show ( ∑ i:I,v.coord i ( y-x ) • v i )= _ from v.sum_repr _, add_sub_cancel .. ] -- should cancel
    intro a; induction a using Finset.induction with
    | empty=> simp [canes, worth]
    | insert i a hi ih=>
      let x':= canes v x y a; let d':= v.coord i ( y-x ); let z:= x'+d' • v i; have he : canes v x y (insert i a)= z:= by unfold z d' x' canes; rw [Finset.sum_insert hi]; abel
      have ht := single_step d' (U:=ball x d) ( B:=B ) (convex_ball _ _) ( hy a ) (show z∈_ from he ▸ ( hy ( insert i a ))) ( fun t ht=> ( H ht i ).1 ) ( fun t ht=> ( H ht i ).2 ); rw [he, show f z-f x= f z-f x'+(f x'-f x) from (by abel) ]; unfold worth; rw [Finset.sum_insert hi]; apply le_trans (norm_add_le .. ); let r:= ‖y-x‖;
      have hx : ‖d'‖≤ ‖co v i‖ * r:= ( co v i ).le_opNorm _; exact ( add_le_add (ht.trans (mul_le_mul_of_nonneg_right hx hB)) ih ).trans_eq (by unfold worth; unfold r; ring)
-- yields both continuity & derivative.
lemma continuity (h:∀ᶠ y in 𝓝 x, ∀ i:I, HasLineDerivAt ℝ f ( F' i y ) y ( v i ) ∧ ‖F' i y‖ ≤ B ) (hB:0≤B) : ContinuousAt f x:= by
   apply Metric.tendsto_nhds.mpr; intro ε hε; obtain hv:= ( show ContinuousAt (fun y=>B*worth v Finset.univ* ‖y-x‖) x from by fun_prop ).tendsto;
   filter_upwards [credit v h hB, hv.eventually (gt_mem_nhds ( show B*worth v Finset.univ * ‖x-x‖ < ε from by simpa )) ] with y hp hx; rw [ dist_eq_norm ]; exact hp.trans_lt hx
lemma deduct (hU:IsOpen U)(hx:x∈U) (L: E→L[ℝ] F)(he:∀ i:I,L ( v i )= F' i x) (H:∀ x∈U,∀ i:I, HasLineDerivAt ℝ f ( F' i x ) x ( v i ))(h:∀ i:I,ContinuousAt (F' i) x): HasFDerivAt f L x:= by
    rw [hasFDerivAt_iff_isLittleO,isLittleO_iff]; intro c hc; let p:= worth v Finset.univ; have hp:0≤p:= Finset.sum_nonneg fun i _=> norm_nonneg _; let a:=c/(1+p); have ha: 0<a:=by unfold a; positivity
    let g(x:E):= f x - L x;
    have hv : ∀ᶠ y in 𝓝 x, ∀ i:I, HasLineDerivAt ℝ g (F' i y - F' i x) y (v i) ∧ ‖F' i y-F' i x‖ ≤ a:= by
       apply eventually_all.mpr; intro i; filter_upwards [ hU.mem_nhds hx, Metric.tendsto_nhds.mp ( h i ).tendsto a ha ] with y hy H'; refine ⟨?_,(by rw [dist_eq_norm] at H'; exact H'.le)⟩; rw [← he ]; exact HasDerivAt.sub ( H _ hy i ) (L.hasFDerivAt.hasLineDerivAt (v i)|> (show HasLineDerivAt ℝ L (L (v i)) y (v i) → _ from fun x=>x) )
    filter_upwards [ credit v hv ha.le ] with y hy; have ht: a*p ≤ c:= by apply le_trans ( mul_le_mul_of_nonneg_left ( show p≤1+p from by linarith ) ha.le ) ?_; apply le_of_eq; unfold a; field_simp
    unfold g at hy; rw [map_sub ]; rw [← show f y - L y -( f x-L x)= f y-f x- ( L y-L x ) from by abel ]; exact hy.trans ( mul_le_mul_of_nonneg_right ht ( norm_nonneg _ ) )
end YM.FVA2.Poesy.Rails
