import YM.WilsonCoeffUV.Reclosure.Paths.Ebase
import YM.WilsonCoeffUV.Kinetic.PerturbedIntegral
/-!
# Change to the prescribed replica chart, with parameter-dependent shift

Used just at flat. All tree equalities on angular real background. Uses
Haar densities ACTUALLY on free bones. Does not reinterpret StepData.total
as a normalization over these.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Power.Roam
open Lattice Laurent Bloch Exterior Wilson Precision RG Function Filter
open Blue MeasureTheory Set Metric Matrix Gauge PowerSeries
open FreeResolvent Tree Stationary Cameo Bank
open YM.PertExtension.Chart (tangent physical expLinks jacobian fee)
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {c f : Side}{G:Gauge}(S:StepData c f)(F:Forest S.ratio)

abbrev Bod (c:Side) (G:Gauge):= Stationary.Link G c
abbrev Sloc (S:StepData c f)(F:Forest S.ratio)(G:Gauge):=Lawn (Active G F⊕Woods G c)

def biker (y:Bod c G)(x:F.Free): G.El := replica S.ratio (mantle y) x.val
lemma bike0 : biker S F (G:=G) 0=1:=by
    funext i; rw [biker,show mantle (0: Lawn (Woods G c))=1 from ?_,replica_one]; rfl
    rw [← Mosaic.mantle_input]; exact input_zero _ _
lemma bikeGreen (i:F.Free): Green fun x:Bod c G=> G.mat (biker S F x i):=by
    unfold biker replica; split_ifs
    · exact contDiffAt_const
    change Green (fun x=>G.mat (mantle x _))
    simp_rw [←Mosaic.mantle_input]; unfold input
    exact ((Work.F03.represent_smooth _).contDiffAt.comp (f:=arm G c 1) 0 (arm G c 1).contDiff.contDiffAt)

-- measure-preserving right translations before log. Use old angular variables

def rack (Q:F.Slice G)(v:F.Slice G): F.Slice G := Q*v
def tip (x:AxisChart G F × Bod c G): F.Slice G:= rack S F (expLinks G F.Free x.1) (biker S F x.2)
def glow (x:AxisChart G F × Bod c G):AxisChart G F:= mapLog (S:=S) F (tip S F x)
lemma tip_o : tip S F (G:=G) 0=1:=by change _*biker _ _ 0= _; rw [bike0,mul_one]; funext i; exact G.mat_lieExp_zero
lemma tip_green (i:F.Free): ContDiffAt ℝ ω (fun x:AxisChart G F×Bod c G=> G.mat (tip S F x i)) 0 :=by
    unfold tip rack; simp_rw [Pi.mul_apply, G.mat_mul];
    have hy : ContDiffAt ℝ ω (fun x:AxisChart G F×Bod c G=> x.1 i) 0:= (contDiffAt_apply ℝ G.Color i _).comp 0 contDiffAt_fst
    have ha : ContDiffAt ℝ ω (fun x:AxisChart G F×Bod c G=>G.mat (biker S F x.2 i)) 0:= (bikeGreen (G:=G) S F i).comp (f:=fun x:AxisChart G F×Bod c G=>x.2) 0 contDiffAt_snd
    exact (G.exp_jet.contDiffAt.comp 0 hy).mul ha
lemma glow_color : ContDiffAt ℝ ω (glow S F (G:=G)) 0:=by
    apply contDiffAt_pi.mpr; intro i
    exact ContDiffAt.comp (g:=G.plog) _ (by rw [show G.mat (tip S F 0 i)=1 from by rw [tip_o]; rfl]; exact G.plog_diff) (tip_green S F i)
lemma glow_o:glow S F (G:=G) 0=0:=by unfold glow mapLog LocalH.snap; rw [tip_o]; funext i; simp
lemma glow_genuine: ∀ᶠ x:AxisChart G F×Bod c G in 𝓝 0,expLinks G F.Free (glow S F x)=tip S F x:=by
    have ht i:Tendsto (fun x=>tip S F x i) (𝓝 0) (𝓝 (1:G.El)):= by apply Push.Loops.tendsto_mat.mpr; have ht:=(tip_green (G:=G) S F i).continuousAt.tendsto; rw [tip_o] at ht; exact ht
    filter_upwards [eventually_all.mpr fun i=> (ht i).eventually G.plog_right] with x hx; exact funext hx
lemma reception (Y:Bod c G) : MeasurePreserving (fun z:F.Slice G=> rack S F z (biker S F Y)) (physical G F.Free) (physical G F.Free) := measurePreserving_pi _ _ (fun i:F.Free=> measurePreserving_mul_right G.probHaar (biker S F Y i))
theorem glowingJ {Ñ:ChartRatio G}(h:LocalRatio Ñ): ∀ᶠ x:AxisChart G F × Bod c G in 𝓝 0, |(fderiv ℝ (fun y=>glow S F (y,x.2)) x.1).det| * jacobian Ñ (glow S F x)=jacobian Ñ x.1:= areaP h _ (glow_o S F) (fun y t=>rack S F t (biker S F y)) (reception S F) (fun _ _ _ h=> mul_right_cancel h) (glow_color S F) (glow_genuine S F)
lemma glow_center (i:F.Free):∀ᶠ x : AxisChart G F in 𝓝 0,glow S F (x,0) i=x i:=by
    have hp:= (continuous_apply i).tendsto (0: AxisChart G F)
    filter_upwards [hp.eventually G.plog_left] with x hx; unfold glow tip rack; dsimp only; rw [bike0, mul_one]; exact hx

-- now shift center. Old rho from P.Kin contains Ed frame. θ actually sampled in **ordinary v** variables.
variable (M: Matrix (Woods G f) (Woods G c) ℝ) (ρ: fieldDir G c 1→ AxisChart G F)
abbrev badge (x:Sloc S F G): fieldDir G c 1:= arm G c 1 (rightArm x)

def sedan (x:Sloc S F G): AxisChart G F × Bod c G:= (vcloth S F G (leftArm x)+ρ (badge S F x),rightArm x)
def shore (x: Sloc S F G) : Lawn (Active G F):= (vcloth S F G).symm (glow S F (sedan S F ρ x))-rise S F M id (rightArm x)

lemma badge_green: Green (badge S F (G:=G)):= (arm G c 1).contDiff.contDiffAt.comp _ rightGreen
lemma sedan_green (h:ContDiffAt ℝ ω ρ 0): Green (sedan S F ρ):= (((vcloth S F G).contDiff.contDiffAt.comp _ leftGreen).add ((show ContDiffAt ℝ ω ρ (badge S F 0) from by rw [badge,rightZero,map_zero]; exact h).comp 0 (badge_green S F))).prodMk rightGreen
lemma sedan_zero (h:ρ 0=0): sedan S F ρ 0=0:= by rw [sedan,leftZero,map_zero,badge,rightZero,map_zero,h,zero_add]; rfl
lemma shore_green (h:ContDiffAt ℝ ω ρ 0)(p:ρ 0=0): Green (shore S F M ρ):=by
    have he:=sedan_green S F ρ h; have hf:ContDiffAt ℝ ω (glow S F) (sedan S F ρ 0):= by rw [sedan_zero ..]; exacts [glow_color S F,p]
    exact ((vcloth S F G).symm.contDiff.contDiffAt.comp (f:=fun v=>glow _ _ (sedan S F ρ v)) 0 (hf.comp _ he)).sub ((((reveal G S F).transpose*M).mulVecLin.toContinuousLinearMap.contDiff.contDiffAt).comp (f:=rightArm) 0 rightGreen)
lemma shore_zero (p:ρ 0=0):shore S F M ρ 0=0:=by rw [shore,sedan_zero S F _ p,glow_o,map_zero,rightZero,rise,id_eq,Matrix.mulVec_zero,sub_zero]
lemma sluggish (p:ρ 0=0) : ∀ᶠ z:Lawn (Active G F) in 𝓝 0,shore S F M ρ (Sum.elim z (0:Lawn (Woods G c)))=z:=by
    have h:= (vcloth S F G).continuous.tendsto 0; rw [map_zero] at h
    filter_upwards [h.eventually (eventually_all.mpr (glow_center (G:=G) S F))] with x hx
    change _-(rise S F M id 0)=_
    unfold rise; rw [id_eq,Matrix.mulVec_zero,sub_zero]
    let v:Lawn (Active G F⊕Woods G c):=Sum.elim x 0
    rw [show (sedan S F ρ v)=(vcloth S F G x,0) from ?_]; swap; · change (vcloth S F G x + ρ (arm G c 1 0),(0:Lawn (Woods G c)))= _; rw [map_zero,p,add_zero]
    exact congr_arg ((vcloth S F G).symm) (funext hx) |>.trans ((vcloth S F G).symm_apply_apply _)
lemma initial_edge (h:ContDiffAt ℝ ω ρ 0)(p:ρ 0=0):edgeM (shore S F M ρ) 0=1:=by
    rw [edge_fder _ 0 ((shore_green S F M ρ h p).differentiableAt (by simp)), rightZero,leftZero,(show (fun u:Lawn (Active G F)=>shore S F M ρ (Sum.elim u (0:Lawn (Woods G c))))=ᶠ[𝓝 0] id from sluggish S F M ρ p).fderiv_eq,fderiv_id]; exact LinearMap.toMatrix'_id

-- powers det equality to physical chart with translation at Y
lemma shape_det (x:Sloc S F G)(h: DifferentiableAt ℝ (shore S F M ρ) x)(p:DifferentiableAt ℝ (glow S F) (sedan S F ρ x)) :
    let u:=sedan S F ρ x
    (edgeM (shore S F M ρ) x).det=(fderiv ℝ (fun z=>glow S F (z,u.2)) u.1).det:=by
    intro u; rw [edge_det _ x h]
    let T:=vcloth S F G
    let a:=leftArm x
    let b:=ρ (badge S F x); let G' (z:AxisChart G F):=glow S F (z,u.2)
    let c (y:Lawn (Active G F)):= T y+b
    let d:= fderiv ℝ G' u.1
    have hx : c a=u.1:=rfl
    have ht : HasFDerivAt c T.toContinuousLinearMap a:= T.hasFDerivAt.add_const b
    have hu : HasFDerivAt G' d u.1:= (p.comp (f:=fun v:AxisChart G F=> (v,u.2)) u.1 (differentiableAt_id.prodMk (differentiableAt_const _))).hasFDerivAt
    have hζ: fderiv ℝ (fun z=> shore S F M ρ (Sum.elim z (rightArm x))) a= T.symm.toContinuousLinearMap ∘L (d ∘L T.toContinuousLinearMap) :=by
        have hw : HasFDerivAt G' d (c a):=by rw [hx]; exact hu
        exact (((T.symm.hasFDerivAt).comp a (hw.comp a ht)).sub_const (rise S F M id (rightArm x))).fderiv
    rw [hζ]; exact LinearMap.det_conj d.toLinearMap T.symm.toLinearEquiv

lemma shore_wave (x:Sloc S F G)(u:M=reveal G S F*((reveal G S F).transpose*M)):
    camSlice G S F M*ᵥ spider (shore S F M ρ) x=reveal G S F *ᵥ (vcloth S F G).symm (glow S F (sedan S F ρ x)) :=by
    rw [camber_tree, Matrix.add_mulVec,←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,left_hit,right_hit]
    let B:=spider (shore S F M ρ) x; rw [show leftArm B=shore S F M ρ x from rfl,show rightArm B=rightArm x from rfl]; unfold shore rise; rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec,← u]; exact sub_add_cancel ..
lemma tilted (u:M=reveal G S F*((reveal G S F).transpose*M))(h:ContDiffAt ℝ ω ρ 0)(p:ρ 0=0) :
    ∀ᶠ x:Sloc S F G in 𝓝 0, mantle (camSlice G S F M*ᵥ spider (shore S F M ρ) x)= lifting F (represent (badge S F x)) (sedan S F ρ x).1:=by
    have ht:= (sedan_green S F ρ h).continuousAt.tendsto; rw [sedan_zero S F _ p] at ht
    filter_upwards [ht.eventually (glow_genuine S F)] with x hx
    rw [shore_wave S F M ρ x u,v_extend,ContinuousLinearEquiv.apply_symm_apply,hx]
    let v:=sedan S F ρ x; unfold lifting; apply congr_arg; funext j; unfold tip rack; simp_rw [Pi.mul_apply]; unfold biker; rw [← Mosaic.mantle_input]; rfl

-- area in shifted coordinates
variable (Ñ:ChartRatio G)
def stampJ (x:Sloc S F G) := unhaar Ñ (reveal G S F*ᵥ (vcloth S F G).symm (sedan S F ρ x).1)
lemma stamp_d (h: LocalRatio Ñ)(p:ContDiffAt ℝ ω ρ 0)(hp:ρ 0=0): Green (stampJ S F ρ Ñ):=by
    let P (x:Sloc S F G) := (vcloth S F G).symm (sedan S F ρ x).1
    have hz:P 0=0:=by unfold P; rw [sedan_zero S F _ hp]; exact map_zero _
    have hv:Green P:= (vcloth S F G).symm.contDiff.contDiffAt.comp (f:=fun x=>(sedan S F ρ x).1) 0 (contDiffAt_fst.comp 0 (sedan_green S F ρ p))
    refine ContDiffAt.comp (f:=fun x=> reveal G S F *ᵥ P x) _ ?_ ?_; change ContDiffAt ℝ ω (unhaar Ñ) (reveal G S F*ᵥ P 0); rw [hz, Matrix.mulVec_zero]; exact unhaar_green h
    exact ((reveal G S F).mulVecLin.toContinuousLinearMap.contDiff.contDiffAt).comp _ hv
lemma stamp_o (h:LocalRatio Ñ)(p:ρ 0=0): stampJ S F ρ Ñ 0=0:= by rw [stampJ,sedan_zero S F _ p,show (0:AxisChart G F×Bod c G).1=0 from rfl,map_zero, Matrix.mulVec_zero,unhaar_zero h]
lemma shape_area (h:ContDiffAt ℝ ω ρ 0)(hp:ρ 0=0)(q:LocalRatio Ñ)(u:M=reveal G S F*((reveal G S F).transpose*M)):
    ∀ᶠ x:Sloc S F G in 𝓝 0, (edgeM (shore S F M ρ) x).det * Real.exp (unhaar Ñ (camSlice G S F M*ᵥ spider (shore S F M ρ) x)) = Real.exp (stampJ S F ρ Ñ x):=by
    have hg:= shore_green S F M ρ h hp; have hm: MGreen (edgeM (shore S F M ρ)):= edge_green _ hg; let d:= fun x=>(edgeM (shore S F M ρ) x).det
    have H : 0<d 0:=by unfold d; rw [initial_edge S F _ _ h hp,Matrix.det_one]; simp
    have hz:=(sedan_green S F ρ h).continuousAt.tendsto; rw [sedan_zero S F _ hp] at hz
    have hf:= glow_color S F (G:=G) |>.continuousAt.tendsto; rw [glow_o] at hf
    have hu:= log_event S F q
    filter_upwards [hm.det.continuousAt.eventually (lt_mem_nhds H), hz.eventually (glowingJ S F q), hg.eventually (by simp), hz.eventually ((glow_color S F).eventually (by simp)), (hf.comp hz).eventually hu,hz.eventually ((continuous_fst.tendsto _).eventually hu)] with x xd xy xv xw xt xz
    rw [←abs_of_pos xd,shape_det S F M ρ x (xv.differentiableAt (by simp)) (xw.differentiableAt (by simp)),shore_wave S F M ρ x u]
    unfold stampJ; apply mul_left_cancel₀ (a:=Ñ.scale^Fintype.card F.Free) (pow_ne_zero _ q.scale.ne')
    rw [mul_left_comm]; simp only [Function.comp_apply] at xt; rw [← xt,← xz] at xy; exact xy
end YM.WilsonCoeffUV.Power.Roam
