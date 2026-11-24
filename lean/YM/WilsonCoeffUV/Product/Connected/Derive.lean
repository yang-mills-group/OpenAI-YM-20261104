import YM.WilsonCoeffUV.Product.Connected.ConnectedPDE
/-!
# Reed subtraction of independent transfer
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Gauge Power PathCost Precision Embroider Fountain Cosmos Shard Realm
open PowerSeries
open scoped Topology BigOperators
variable {n:Side}{j r e k h s i a b:ℕ}{U:Type}{V E W ι D:Type*}{G:Gauge}
section
variable [Fintype U]
lemma by_flash {P Q:Pal ℝ U}{k l:ℕ}(h:shellK k P)(p:shellK l Q)(x:∀ i,Pure (P i))(y:∀ i,Pure (Q i))(e:flash P=flash Q): P=Q:=funext fun i=> gen_inj (finite_shell h i) (finite_shell p i) (x i) (y i) (by simpa only [flash,coeff_mk] using congr_arg (coeff i) e)
lemma mix_wreath (P Q:Pal ℝ U)(B:Cost)(p:shellK i P)(q:shellK j Q): Blue.mix B (woad P Q)=woad (Blue.mix B P) (Blue.mix B Q):=by
   let X:=woad P Q; let Y:=Blue.mix B P; let Z:=Blue.mix B Q; have hx:shellK (i+j) X:=woad_shell P Q p q; have h:shellK i Y:= mix_length p; have H:shellK j Z:=mix_length q
   apply by_flash (mix_length hx) (woad_shell Y Z h H) (mix_pure (woad_pure P Q)) (woad_pure Y Z); rw [← redo_stern B hx,woadap P Q (finite_shell p) (finite_shell q),map_mul, woadap Y Z (finite_shell h) (finite_shell H),redo_stern B p,redo_stern B q]
lemma fade_woad {V:Type}[Fintype V] (P Q:Pal ℝ U)(p:shellK i P)(q:shellK j Q)(M: Matrix U V ℝ) : (fun i=> Blue.fade M (woad P Q i)) = woad (fun i=>Blue.fade M (P i)) (fun i=>Blue.fade M (Q i)):=by
   let X i:=Blue.fade M (P i); let Y i:=Blue.fade M (Q i); have hx:shellK i X:= fade_shell _ p; have ht:shellK j Y:=fade_shell _ q; have ev:= woad_shell P Q p q; apply by_flash (fade_shell _ ev) (woad_shell X Y hx ht) (fun i=>fade_pure (woad_pure P Q i) M) (woad_pure X Y)
   rw [← loom_fade M _ (finite_shell ev), woadap P Q (finite_shell p) (finite_shell q),map_mul, loom_fade M P (finite_shell p),loom_fade M Q (finite_shell q)]; exact (woadap X Y (finite_shell hx) (finite_shell ht)).symm
-- time sum using upper coefficients range
abbrev finallyA (k:ℕ)(P: Layers ℝ U): Pal ℝ U:= fun e=>∑ j∈ Finset.range (1+k+3*e),P j e
omit [Fintype U] in lemma weathercode (P: Layers ℝ U)(h:stops i P): shellK i (finallyA i P):= by
    intro k r p; unfold finallyA; rw [Finset.sum_apply]; exact Finset.sum_eq_zero fun a _=> h _ _ _ (Or.inl p)
lemma close_pair (P Q: Layers ℝ U)(p:stops i P)(q:stops j Q): finallyA (i+j) (tassel P Q)= woad (finallyA i P) (finallyA j Q):=by
    let X:=finallyA i P; let Y:=finallyA j Q; let V:=tassel P Q; have hv:stops (i+j) V:= tassel_stop P Q p q; have hX:= weathercode P p; have hY:=weathercode Q q; refine by_flash (weathercode V hv) (woad_shell X Y hX hY) (fun i=> pure_sum (fun x _=> tassel_pure _ _ x i)) (woad_pure X Y) ?_
    unfold finallyA; rw [← at_one _ _ hv, ramp_joint P Q p q, map_mul,at_one _ i p,at_one _ j q]; exact (woadap X Y (finite_shell hX) (finite_shell hY)).symm
end
section
variable {c f:Side}
open Wilson Tree AnalyticNext.QuarticMatch.Sheets Exterior MultiNext.SignedSource
variable (S:StepData c f)(V:Forest S.ratio) (H:FaceRow) (Y:Matrix (Body 1 f) (Body 1 c) ℝ)(Ñ: ChartRatio G)(P:PChart G f)
-- E thermolift uses bend.
abbrev boiling (Q R:PChart G f):= estuary (fillSlots (Woods G c) (covariance G S V H)) (xray S V H Y Ñ P) (srCold Q (extractV G S V Y)) (srCold R (extractV G S V Y))
lemma boiling_eq (Q R:PChart G f)(p:shellK i Q)(q:shellK j R): boiling S V H Y Ñ P Q R = srShade S V H Y Ñ P (woad Q R)-tassel (srShade S V H Y Ñ P Q) (srShade S V H Y Ñ P R):=by
    let X:=extractV G S V Y; rw [srShade,show srCold (woad Q R) X=woad (srCold Q X) (srCold R X) from fade_woad _ _ p q _]; rfl
lemma reed_miss (Q R:PChart G f)(p:shellK i Q)(q:shellK j R)(hp:shellK 2 P)(u:LocalRatio Ñ): reed S V H Y Ñ P (i+j) (woad Q R) - woad (reed S V H Y Ñ P i Q) (reed S V H Y Ñ P j R)=fun e=> Blue.fade plug (finallyA (i+j) (boiling S V H Y Ñ P Q R) e):=by
    let X:= srShade S V H Y Ñ P Q; let W:= srShade S V H Y Ñ P R; let B:= srShade S V H Y Ñ P (woad Q R)
    have hv : stops i X:= srStops S V H Y i hp u p; have hx : stops j W:= srStops S V H Y j hp u q; let T:= finallyA (i+j) (boiling S V H Y Ñ P Q R); let D:= finallyA i X; let L:= finallyA j W
    have hT:T=finallyA (i+j) B- woad D L:=by unfold T L D; rw [boiling_eq _ _ _ _ _ _ Q R p q,← close_pair X W hv hx]; funext i; simp only [Pi.sub_apply, finallyA,Finset.sum_sub_distrib]; rfl
    change _-woad (fun i=>Blue.fade plug (D i)) (fun i=>Blue.fade plug (L i)) =_; change _-_=fun i=> Blue.fade plug (T i); rw [hT,←fade_woad D L (weathercode X hv) (weathercode W hx) plug]
    ext1 i; let E:=woad D L; change Blue.fade _ (finallyA _ B i)-Blue.fade _ (E i)=Blue.fade _ _; funext k x; simp only [Pi.sub_apply, Blue.fade]; simp only [smul_sub,Finset.sum_sub_distrib]; rfl
end
end YM.WilsonCoeffUV.Mer
