import YM.FormalOPE.RG10.Inherit.Jet
/-!
 # Chart changes for graph configurationΨ; fee coercion transferable without computing fp det.
 Use real gauge group's analytic local `mat plog`. No eternal equival demanded of log map.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Inherit
open Function Filter Topology MeasureTheory PertExtension Series Precision
open BlockGauge Series.Radial Push.Loops Chart
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge}{I J K : Type}[Fintype I][Fintype J][Fintype K]
abbrev Configuration (G:Gauge)(I:Type):= I→ G.El
abbrev Direction (G:Gauge)(I:Type):= I→ G.Color
omit [Fintype I] in
@[simp] lemma identity_zero : expLinks G I 0=1:=funext (fun _=> G.mat_lieExp_zero)
lemma neighborhood_exp : MatDiffAt (expLinks G I) 0 := fun i=> G.exp_jet.contDiffAt.comp _ (contDiffAt_apply ℝ G.Color i _)
 def down (K: Configuration G I) (i:I):= G.plog (G.mat (K i))
omit [Fintype I] in
@[simp] lemma down_one : down (G:=G) (1: Configuration G I)=0:= by ext1; simp [down]
lemma down_left : ∀ᶠ u: Direction G I in 𝓝 0, down (expLinks G I u) = u:= by
 apply Filter.Eventually.mono (p:=fun x=>∀ i, down (expLinks G I x) i=x i) ?_ fun x h=> funext h
 exact Filter.eventually_all.mpr (fun i=>((continuous_apply i).continuousAt (x:=(0:Direction G I))).eventually G.plog_left)
lemma down_right : ∀ᶠ u: Configuration G I in 𝓝 1, expLinks G I (down u) = u:= by
 apply Filter.Eventually.mono (p:=fun x=>∀ i, expLinks G I (down x) i=x i) ?_ fun x h=> funext h
 exact Filter.eventually_all.mpr (fun i=> ((continuous_apply i).continuousAt (x:=(1:Configuration G I))).eventually G.plog_right)
omit [Fintype I] in
lemma down_here : ContinuousAt (down (G:=G) (I:=I)) 1:= by
 apply continuousAt_pi.mpr; intro i; unfold down; change ContinuousAt (G.plog ∘ (G.mat ∘ fun x : Configuration G I=> x i)) 1
 exact ContinuousAt.comp (g:= G.plog) (f:= G.mat ∘ fun x : Configuration G I=> x i) (show ContinuousAt G.plog (G.mat ((1:Configuration G I) i)) by simpa using! G.plog_diff.continuousAt) (G.continuous_mat.comp (continuous_apply i)).continuousAt
lemma down_chart {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {f:E→ Configuration G I}{x:E}(hf: MatDiffAt f x)(ha: f x=1): ContDiffAt ℝ ω (down ∘ f) x:= by
 apply contDiffAt_pi.mpr; intro i
 apply ContDiffAt.comp (f:=fun u=> G.mat (f u i)) _ _ (hf i); rw [ha,Pi.one_apply,G.mat_one]; exact G.plog_diff

-- inverse continuous near identity follows from smooth criterion.Awaiting.
omit [Fintype J] in
lemma under {f: Configuration G I→ Configuration G J} (h:MatDiffAt (f ∘ expLinks G I) 0): ContinuousAt f 1:= by
 have he: f =ᶠ[𝓝 1] (f ∘ expLinks G I) ∘ down:= by filter_upwards [down_right (G:=G) (I:=I)] with u hu; exact congr_arg f hu.symm
 have hf: ContinuousAt (f ∘ expLinks G I) (down (1:Configuration G I)):= by rw [down_one]; exact h.continuousAt
 exact (hf.comp (down_here)).congr (x:=_) he.symm

structure Atelier (G:Gauge) (I J:Type)[Fintype I][Fintype J] where
 placement : Configuration G I ≃ᵐ Configuration G J
 origin : placement 1=1
 form : MatDiffAt (placement ∘ expLinks G I) 0
 recover : MatDiffAt (placement.symm ∘ expLinks G J) 0

namespace Atelier
variable (X:Atelier G I J)
lemma at_one : X.placement (expLinks G I 0)=1:= by rw [identity_zero,X.origin]
lemma dHere : ContinuousAt X.placement 1:= under X.form
lemma dOrigin : X.placement.symm 1=1:= X.origin ▸ X.placement.symm_apply_apply (1:Configuration G I) -- orientation prob
 def rev : Atelier G J I:= ⟨X.placement.symm, X.dOrigin, X.recover, X.form⟩
 def prepare := down ∘ X.placement ∘ expLinks G I
lemma prepare_form : ContDiffAt ℝ ω X.prepare 0:= down_chart X.form X.at_one
lemma prepare_zero : X.prepare 0=0:= by change down (X.placement (expLinks G I 0))=0; rw [X.at_one, down_one]
lemma prepare_apply : expLinks G J ∘ X.prepare =ᶠ[𝓝 0] (X.placement ∘ expLinks G I) := by
 have ha:= (show ContinuousAt (X.placement ∘ expLinks G I) 0 from X.form.continuousAt).tendsto
 rw [Function.comp_apply,X.at_one] at ha
 filter_upwards [ha.eventually (down_right (G:=G) (I:=J))] with u hu using hu
lemma both : X.rev.prepare ∘ X.prepare =ᶠ[𝓝 0] id:= by
 filter_upwards [X.prepare_apply, down_left (G:=G) (I:=I)] with u hu hv
 change expLinks G J (X.prepare u)=X.placement (expLinks G I u) at hu
 change down (X.placement.symm (expLinks G J (X.prepare u))) = u; rw [hu, X.placement.symm_apply_apply,hv]
lemma solo (u:Direction G I)(h:u ≠ 0): fderiv ℝ X.prepare 0 u ≠ 0:= by
 intro he; apply h; have hv: fderiv ℝ (X.rev.prepare ∘ X.prepare) 0=fderiv ℝ (@id (Direction G I)) 0:= X.both.fderiv_eq
 rw [fderiv_comp (𝕜:=ℝ) _ (by rw [X.prepare_zero]; exact X.rev.prepare_form.differentiableAt (by simp)) (X.prepare_form.differentiableAt (by simp)), fderiv_id] at hv
 have hx:= congr_arg (fun q:(Direction G I→L[ℝ] Direction G I)=> q u) hv; simpa only [ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,he,map_zero] using hx.symm
end Atelier
end YM.FormalOPE.RG10.Inherit
