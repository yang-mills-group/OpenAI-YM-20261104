import YM.RegulatorIR.Geometry.Penalty
import YM.RegulatorIR.Laplace.Aura
import YM.Work.F03.Flat

/-! Scaled links. Actual group and matrix; Haar in Outline. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Binding
open PertExtension Laplace Chart Lattice Geometry Geometry.End Geometry.Field Orb Gauge MeasureTheory Filter Function Set Metric Exterior Wilson RG Precision
open scoped ContDiff Topology NNReal ENNReal BigOperators Classical Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {f c: Side}{G:Gauge}

-- reader groups per orbit
abbrev Horizon (G:Gauge)(f:Side):= Meadow G (OEdge f)
abbrev Shape (G:Gauge)(f:Side):= spins G f
abbrev climb (x:Horizon G f): Shape G f:= Chart.expLinks G _ x

def fire (x:Horizon G f) : Edge (Site f)→G.Color:= fun i=> if eR i=i then x (index i) else -x (index i)
lemma fire_at (x:Horizon G f)(i:OEdge f) : fire x i.val=x i:=by rw [fire,if_pos i.property]; exact congr_arg x (Subtype.ext i.property)
lemma fire_swaps (x:Horizon G f)(hf:Even f.val) (i) : fire x (reflect i) = -fire x i:= by
 unfold fire;rw [eR_reflect, show index (reflect i)=index i from Subtype.ext (eR_reflect i)]
 rcases eR_spec i with h|h
 · rw [h,if_neg (Ne.symm (no_fixed_edge hf i)), if_pos rfl]
 rw [h,if_pos rfl, if_neg (no_fixed_edge hf i), neg_neg]
lemma fireL (x y:Horizon G f)(t:ℝ):fire (x+t • y) = fire x+t • fire y:=by ext1 i; unfold fire;split_ifs <;> simp [*,add_comm]

def canvas (x:Horizon G f) : Push.In G f := fun i=>fire x (i.1,Exterior.axisEquiv.symm i.2)
lemma canvas_rate (x:Horizon G f) (t:ℝ) : canvas (t • x)=t • canvas x:=by ext1 i; rw [canvas];simp only [fire];split_ifs <;> simp [canvas,fire, *]
lemma mat_expanded (x:Horizon G f): orbLift (climb x)=represent (canvas x):=by
 ext1 i; rw [Work.F03.represent_link]; unfold orbLift liftLinks canvas fire; rw [show Exterior.axisEquiv.symm (coord i.2)=i.2 from Exterior.axisEquiv.symm_apply_apply _]; split_ifs with he
 · rfl
 rw [Work.F03.exp_neg_color]; rfl
lemma canvas_origin : canvas (0:Horizon G f)=0:=by ext1 i; simp [canvas,fire]
lemma canvased : ContDiffAt ℝ ω (canvas (G:=G) (f:=f)) 0:=by
 apply contDiffAt_pi.mpr; intro i; unfold canvas fire; split_ifs
 · exact contDiffAt_apply ..
 exact ContDiffAt.neg (contDiffAt_apply ..)

-- Ascent log reads. Used for Ward and rank Hessian identification.
def lower (G: Gauge)(I:Type)(x:RoomK G I) : Meadow G I:= fun z=> G.plog (G.mat (x z))
lemma lower_zero (G:Gauge)(I:Type): lower G I 1=0:=by ext1 z; simp [lower]
lemma upper_lower (I:Type)[Fintype I]: ∀ᶠ v:RoomK G I in 𝓝 1,expLinks G I (lower G I v)=v:=by
 have h(i:I): ∀ᶠ v:RoomK G I in 𝓝 1,G.lieExp (G.plog (G.mat (v i)))=v i:= ((continuous_apply i).tendsto (1:RoomK G I)).eventually G.plog_right
 exact (eventually_all.mpr h).mono fun _ h=>funext h
lemma lower_upper (I:Type)[Fintype I]: ∀ᶠ v:Meadow G I in 𝓝 0,lower G I (expLinks G I v)=v:=by
 have h(i:I): ∀ᶠ v: Meadow G I in 𝓝 0,G.plog (G.mat (G.lieExp (v i)))=v i:= ((continuous_apply i).tendsto (0:Meadow G I)).eventually G.plog_left
 exact (eventually_all.mpr h).mono fun _ h=> funext h
lemma vertical_deriv (x:G.Color): HasDerivAt (fun t:ℝ=>G.mat (G.lieExp (t • x))) (G.colorMat x) 0:=by
 let f:= fun t:ℝ=> t • x; exact (show HasFDerivAt _ _ (f 0) from (show f 0=0 from zero_smul ℝ _) ▸ G.expDiff_zero).comp_hasDerivAt 0 (show HasDerivAt f x 0 from by simpa only [f,one_smul] using! (hasDerivAt_id' (0:ℝ)).smul_const x)
lemma plog_rotate (x:G.Color) : fderiv ℝ G.plog 1 (G.colorMat x)=x:=by
 let g:= fun t:ℝ=> t • x
 let f:= fun t:ℝ=> G.mat (G.lieExp (t • x));have hz:f 0=1:=by simp [f]
 have ht:HasDerivAt g x 0:=by simpa only [g,one_smul] using! (hasDerivAt_id' (0:ℝ)).smul_const x
 have hh : G.plog ∘ f=ᶠ[𝓝 0] g:=(show Tendsto g (𝓝 0) (𝓝 0) from by simpa [g] using ht.continuousAt.tendsto)|>.eventually G.plog_left
 have hc : HasFDerivAt G.plog (fderiv ℝ G.plog 1) (f 0):=hz ▸ (G.plog_diff.differentiableAt (by simp)).hasFDerivAt
 exact (hc.comp_hasDerivAt 0 (vertical_deriv x)|>.congr_of_eventuallyEq hh.symm).unique ht
variable (S:StepData c f) (H:S.patch.Branches S.kernel G)
def slope (G:Gauge)(S:StepData c f) (b:Horizon G f) := lower G (OEdge c) (predictor S (climb b))
def rod (G:Gauge)(S:StepData c f) : Horizon G f→L[ℝ] Horizon G c:= fderiv ℝ (slope G S) 0
include H
lemma slope_zero : slope G S 0=0:=by rw [slope,show climb _= _ from expOrigin .., predict_zero S H, lower_zero]
lemma mast (i:OEdge c) : ContDiffAt ℝ ω (fun x:Horizon G f=>G.mat (predictor S (climb x) i)) 0:=by
 unfold predictor; simp_rw [mat_expanded]
 exact (show ContDiffAt ℝ ω (fun x=>G.mat (S.prediction (represent x) (directive S) i.val)) (canvas 0) from by rw [canvas_origin]; exact Push.prediction_cont S H ..).comp 0 canvased
lemma smooth : ContDiffAt ℝ ω (slope G S) 0 := by
 apply contDiffAt_pi.mpr; intro i
 refine (show ContDiffAt ℝ ω G.plog (G.mat (predictor S (climb 0) i)) from ?_).comp (f:=fun x:Horizon G f=>G.mat (predictor S (climb x) i)) _ (mast S H i)
 rw [show climb (0:Horizon G f)=1 from expOrigin ..,predict_zero S H,Pi.one_apply,mat_one]; exact G.plog_diff
lemma bend (x:Horizon G f)(i:OEdge c) : HasDerivAt (fun t:ℝ=>G.mat (predictor S (climb (t • x)) i)) (G.colorMat ((rod G S) x i)) 0:=by
 let f (t:ℝ):= slope G S (t • x)
 have h:HasDerivAt f (rod G S x) 0:= Push.side _ ((smooth S H).differentiableAt (by simp)) x
 let g(t:ℝ):= predictor S (climb (t • x)) i
 have hv: ∀ᶠ t in 𝓝 0, g t=G.lieExp (f t i):=by
    have h': Tendsto (fun t:ℝ=> predictor S (climb (t • x))) (𝓝 0) (𝓝 1):=by
       have hg:Tendsto (fun t:ℝ=> t • x) (𝓝 0) (𝓝 0):= by simpa using (show Continuous (fun t:ℝ=> t • x) from continuous_id.smul continuous_const).tendsto 0
       have hz:= (prediction_zero_cont S H).tendsto; rw [predict_zero S H] at hz
       apply hz.comp; rw [← expOrigin]; exact ((expMeadow _).tendsto _).comp hg -- maybe
    exact (h'.eventually (upper_lower ..)).mono fun a ha=> (congr_fun ha i).symm
 have hy:= (hasDerivAt_pi ..).mp h i
 have h0:f 0=0:=by unfold f;rw [zero_smul,slope_zero S H]
 have he: HasFDerivAt (fun p=>G.mat (G.lieExp p)) G.colorMat.toContinuousLinearMap (f 0 i) := by rw [h0]; exact G.expDiff_zero
 exact (he.comp_hasDerivAt 0 hy).congr_of_eventuallyEq (hv.mono fun t ht=> congr_arg G.mat ht)
end YM.RegulatorIR.Binding
