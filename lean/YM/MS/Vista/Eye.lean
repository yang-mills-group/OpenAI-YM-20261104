import YM.MS.Vista.Ship
/-!
# Oscillatory Join & mesh difference. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Vista
open Set Function Filter Finset Metric MeasureTheory Real High
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit
open scoped Topology ContDiff Interval
variable {I E:Type}{G:Gauge}[ NormedAddCommGroup E][ NormedSpace ℝ E]{S:Scale I}{μ ν:I→Measure QP}{L K:I→ Latch.Edge G}
    {X Y:I→Law G}{ A B:I→Cover}{N:I→Side}{x y z v:I→ℝ}{b:Bool}{w l r:Wire ( BH G ) E QP}
local notation "Γ"=> field ( parity ( C:=G.ColorIndex ) ( A:=Axis ))
abbrev Growth (S:Scale I)(v x:I→ℝ)(k:ℕ)(i:I):= x i*( S.length i/v i)^k
variable (h: Fund S K z) (hv:Visible X)(hx:Visible Y)(hF:Lease false true S X x)(hH: Lease false true S Y y)
  (hp: nn x)(hq:nn y)(ht:nn z)
include h hv hx hF hH hp hq ht
lemma farMesh (H:VistaQ S μ ν)(he: Radar S v B ν)(ha: Mileage S A v)(hw:∀ i,S.length i ≤ v i)(k:ℕ): Lease false false S ( Window b A B μ K X Y ) (Growth S v (z*x*y) k):= by
   have hV(i:I):0<v i:=lt_of_lt_of_le ( S.pos _ ) ( hw i ); let r(i):= S.length i / v i; have hz(i):0<r i:= div_pos ( S.pos i ) ( hV i ); apply knock H h hv hx; intro E _ _ l a w hW; let V:=Qbud w S ( z*x*y ); unfold Qbud; simp_rw [ Growth,← mul_assoc ]; refine pulseCost (g:=fun i (_:E)=> V i) (a:=r) (net l) ?_ hz (fun i=> (div_le_one (hV i)).mpr (hw i)) ?_ k
   · intro m; refine Costs.sum _ (fun i _=> Costs.sum _ (fun j _=> ?_) ?h ) ?h; swap; · exact fun i _ _=> mul_nonneg (pos_nn _ ( joy ( joy ht hp ) hq ) S i ) ( pow_nonneg (hz i|>.le) _ )
     convert ( he E _ _ ( Φmesh h hF hH hW i j (p:=b) ) m ) using 1; funext k x₁; dsimp only; rw [show HoopT S w z _ _*fee S _=_ from Cash .. ]; unfold V Qbud; congr 1; simp only [Pi.mul_apply]; ring -- maybe `(Cash)` grouping
   · convert paid_at ha (E:=E) (fun i=>(hV i).le) using 1; ext; unfold r; field_simp [(S.pos _).ne'] -- v.ne? not needed
lemma mesh_diff (he:∀ i,S.length i≤(N i).val)(k:ℕ): Lease false false S ( Window false 0 0 (fun i=>σcap ( N i )) K X Y - Window false 0 0 (fun _=>μzone) K X Y ) (Growth S (fun i=> (N i).val) (z*x*y) k):= by
   have ηz : ∀ p:QP,be 0 p=1:= fun _=> (by simp [be,show embed 0=0 from (by ext; simp [embed])]);
   intro E _ _ w _ _; unfold Cape; let U(p:BH G)(q:BH G)(l r:Wire ( BH G ) E QP):= αmesh false (tinted K) X Y p q l r; let V (l r:Wire (BH G) E QP)(u: BH G)(v:BH G):= Sugar (ψstep ∘ N) (U u v l r);
   have hz ( i:I )(p:E)(μ ν:I→Measure QP)(H:VistaQ S μ ν): Plane.Chart ( Window false 0 0 μ K X Y ) w i p=scatter Γ w ( fun l r=>∑ u:BH G,∑ v:BH G,∫ q,U u v l r i (q,p)∂ν i ):= by rw [harborK H h hv hx]; unfold hbill waveInt; simp_rw [Pi.zero_apply, ηz,one_mul ]; rfl
   have heq (t:I)(p:E): Plane.Chart ( Window false 0 0 (fun i=>σcap ( N i )) K X Y - Window false 0 0 (fun _=>μzone) K X Y ) w t p=scatter Γ w (fun l r=>∑ u:BH G,∑ v:BH G,V l r u v t p):= by
       change Plane.Chart (Window false 0 0 (fun i=>σcap ( N i )) K X Y) w t p-Plane.Chart (Window false 0 0 (fun _=>μzone) K X Y) w t p=_; rw [ hz t p _ _ ( f_cap he ),hz t p _ _ ( routineQ S ) ]; let T:= allocate Γ w ( R:=ℂ ); change T _-T _=T _; rw [← map_sub]; congr 1; ext; simp only [V, Pi.sub_apply,Sugar,TreeSum,Finset.sum_sub_distrib]; rfl
   rw [show Plane.Chart _ w = _ from funext fun t=> funext (heq t) ]; apply gather_bound w; intro l r hf; refine Costs.sum _ (fun u _=>Costs.sum _ (fun v _=>?_) ?h) ?h; swap; · exact fun i p he'=> mul_nonneg ( length_p .. ) (mul_nonneg (joy ( joy ht hp ) hq i ) ( pow_nonneg (by have h0:= S.pos i; have ht:= Bloch.side_pos ( N i ); positivity) k ))
   convert ( SectorG he ( Φmesh h hF hH hf u v (p:= false) ) k ) using 1
   funext i p; dsimp only [Growth]; rw [show HoopT S w z (x*y) i*fee S i=_ from Cash .. ]; simp only [Pi.mul_apply]; ring
end YM.MS.Vista
