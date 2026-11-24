import YM.OPE.Compatible.Grove.Lift
/-!
# Engineering comparison. Cover ray supports nonradial input. Direction small-g leading before Tate Bill.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Wilson Planned.PrimaryIntegral295.Carrier Asymptotics
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J W E X:Type*}{i j n r d m:ℕ}{G:Gauge}{s b U D:ℝ}
namespace Script
open Page
abbrev Hemi := 𝓝[>] (0:ℝ)
section limit
variable [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup X][NormedSpace ℝ X]
lemma curveD {h:Filter I} {v w:I→ E}{t:I→ℝ} {a p:E} {f:E→X}{D: E→L[ℝ] X}(H: HasStrictFDerivAt f D a) (hx:Tendsto v h (𝓝 a))(ht:Tendsto w h (𝓝 a))(hp:Tendsto (fun i=>t i • (v i-w i)) h (𝓝 p)): Tendsto (fun i=>t i • (f (v i)-f (w i))) h (𝓝 (D p)):=by
    let Y(i:I):=f (v i)-f (w i)-D (v i-w i)
    have hu: Tendsto (fun i=>t i • Y i) h (𝓝 0):=by
        rw [Metric.tendsto_nhds]; intro ε hε; let k:=‖p‖+1; have hz :0<k:=by unfold k; positivity
        have hV := ((show (fun p:E×E=> f p.1-f p.2-D (p.1-p.2)) =o[𝓝 (a,a)] (fun p=> p.1-p.2) from H.isLittleO)|>.bound (show 0<ε/k from div_pos hε hz))
        filter_upwards [(hx.prodMk_nhds ht).eventually hV,hp.norm.eventually (gt_mem_nhds (by simp [k] : ‖p‖<k))] with i hi hh
        rw [dist_zero_right,norm_smul]; apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left (show ‖Y i‖≤ _ from hi) (norm_nonneg (t i)))
        rw [mul_left_comm ‖t i‖,← norm_smul (t i)]; exact lt_of_lt_of_le (mul_lt_mul_of_pos_left hh (div_pos hε hz)) (le_of_eq (div_mul_cancel₀ _ hz.ne'))
    have hg:=hu.add (D.continuous.continuousAt.tendsto.comp hp); rw [zero_add] at hg; apply hg.congr; intro i; change t i • _+ D (t i • _)=_; unfold Y; rw [smul_sub,map_smul,sub_add_cancel]
end limit
abbrev lil {X:Type*}[TopologicalSpace X][Zero X] (p:ℝ→X):= Tendsto p Hemi (𝓝 0)
abbrev sideLimit {X:Type*}[TopologicalSpace X](p:ℝ→X)(v:X):=Tendsto p Hemi (𝓝 v)
lemma drawn (v w:ℝ→ G.Color)(hv:lil v)(hw:lil w)(t:ℝ→ℝ)(x:G.Color)(h:sideLimit (fun i=>t i • (v i-w i)) x): sideLimit (fun i=>t i • (G.mat (G.lieExp (v i))-G.mat (G.lieExp (w i)))) (G.colorMat x):=by
    have he : HasStrictFDerivAt (fun i=> G.mat (G.lieExp i)) G.colorMat.toContinuousLinearMap 0 :=by
       simp_rw [G.mat_lieExp]; let D:=G.colorMat.toContinuousLinearMap; have hp:HasStrictFDerivAt (NormedSpace.exp (𝔸:=G.Mat)) (1:G.Mat →L[ℝ] G.Mat) (D 0):= by rw [map_zero]; exact hasStrictFDerivAt_exp_zero
       exact hp.comp 0 D.hasStrictFDerivAt
    exact curveD he hv hw h
-- oriented polar colors one slot
variable [Fintype I] {k:I→ℕ}
-- Level family any V ℓ with lower polynomial. Exact difference const. Low over shoot initial.
abbrev radiantX (v:I→fieldX (Shade G)) (k:I→ℕ):Prop:=∀ i,Low (v i) (k i)
lemma strike {f:Lieu Axis→ℝ}(h:f∈Flavor Axis 0)(v w): f v=f w:= by apply flavor_elim h (fun f=> f v=f w) _ rfl (fun _ _ _ _ x y=> congr_arg₂ (·+·) x y) (fun t _ _ a=> congr_arg (t • ·) a); intro i hi; rw [List.length_eq_zero_iff.mp (by omega : i.length=0)]; rfl
omit [Fintype I]
lemma idleX (i: fieldX (Shade G))(h: Low i 0)(a b:Cover)(x:Axis):indexS (a,x) i=indexS (b,x) i:=by
    ext u; obtain ⟨f,H,hf⟩:= h (x,u); exact (hf a).trans ((strike H _ _).trans (hf b).symm)
lemma cuddle {u:fieldX (Shade G)} (h:Low u 1)(a b c:Cover)(x:Axis):indexS (a+c,x) u-indexS (a,x) u=indexS (b+c,x) u-indexS (b,x) u:=by
   ext i; obtain ⟨f,hp,hf⟩:=h (x,i); let t:= fromX (translit c); have he(p:Cover): u (p+c,x,i)-u (p,x,i)= gust t f (translit p):=by
        rw [hf,hf]; apply congr_arg (·-f (translit p)); congr 1; ext; simp [translit,t] -- coerces
   change u (a+c,x,i)-u (a,x,i)=u (b+c,x,i)-u (b,x,i); rw [he,he]; exact strike (sudden f hp t).1 _ _
end Script
end YM.OPE.Flume
