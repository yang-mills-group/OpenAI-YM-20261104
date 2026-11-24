import YM.OPE.Compatible.Glim.Pond
/-! # Jacobian derivative for both link charts, positive or left-positive under inversion. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Wilson RG Precision Metric Matrix Cascade
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
variable {r n:ℕ}(b:Bool)
-- a left motion on U^± ; when b it is on U⁻¹
noncomputable def Spark (u:G.El) : G.El ≃ₜ G.El:= if b then Homeomorph.mulRight u⁻¹ else Homeomorph.mulLeft u
lemma patron (u:G.El): MeasurePreserving (Spark b u) G.probHaar G.probHaar:=by cases b; exact measurePreserving_mul_left G.probHaar u; exact measurePreserving_mul_right G.probHaar _
variable (a:G.Color)
local notation "E"=> G.Color
noncomputable def snap (x:ℝ×E):G.El:= Spark b (G.lieExp (x.1 • a)) (G.lieExp x.2)
noncomputable def tug :ℝ×E→G.Color:=fun x=>G.plog (G.mat (snap b a x))
lemma coil (v:E): snap b a (0,v)=G.lieExp v:=by cases b<;>simp [snap,Spark]
lemma snappy : Continuous (snap b a):=by
    cases b; exact (G.lieExp_cont.comp (continuous_fst.smul continuous_const)).mul (G.lieExp_cont.comp continuous_snd); exact (G.lieExp_cont.comp continuous_snd).mul ((G.lieExp_cont.comp (continuous_fst.smul continuous_const)).inv)
lemma bark : (fun y:E=> tug b a (0,y)) =ᶠ[𝓝 0] id:=by simp only [tug,coil]; exact G.plog_left
@[simp] lemma tug_zero : tug b a 0=0:=by erw [bark b a|>.eq_of_nhds];rfl
lemma tug_live : ContDiffAt ℝ ω (tug b a) 0:=by
   let f:=fun x:ℝ×E=> snap b a x; have he:f 0=1:=by change snap b a (0,0)=_;rw [coil,G.mat_lieExp_zero];
   have hf: ContDiffAt ℝ ω (G.mat ∘ f) 0 := by
       have ht: ContDiff ℝ ω (fun x:ℝ×E=>G.mat (G.lieExp (x.1 • a))):=G.exp_jet.comp (contDiff_fst.smul contDiff_const); have hy:ContDiff ℝ ω (fun x:ℝ×E=>G.mat (G.lieExp x.2)):= G.exp_jet.comp contDiff_snd
       cases b <;> simp only[Function.comp_def,f,snap,Spark,Bool.false_eq_true,↓reduceIte,Homeomorph.coe_mulRight,Homeomorph.coe_mulLeft,G.mat_mul]
       · exact (ht.mul hy).contDiffAt
       simp only [G.mat_inv]; exact (hy.mul ((starL ℝ (A:=G.Mat)).contDiff.comp ht)).contDiffAt
   have hp:(G.mat ∘ f) 0=1:=by rw [Function.comp_apply,he,G.mat_one]
   unfold tug; exact ((hp.symm ▸ G.plog_diff : ContDiffAt ℝ ω G.plog _) |>.comp _ (f:=G.mat ∘ f) hf)
lemma snatched : ∀ᶠ v:ℝ×E in 𝓝 0, G.lieExp (tug b a v)=snap b a v:=by
    have ht:snap b a 0=1:=(coil b a 0).trans G.mat_lieExp_zero; exact (show Tendsto (snap b a) (𝓝 0) (𝓝 1) from ht ▸ (snappy b a).tendsto (0:ℝ×E)).eventually G.plog_right
noncomputable abbrev Cast(x:E):= sway (tug b a) (0,x)
lemma cast_sm : ContDiffAt ℝ ω (Cast b a) 0:= (Arch _ (tug_live b a)).comp (f:=fun i:E=> (0,i)) _ (contDiff_const.prodMk contDiff_id).contDiffAt
set_option maxHeartbeats 200000 in
lemma CastPrice (H:LocalRatio P) (B:Module.Basis G.ColorIndex ℝ G.Color):
    ∀ᶠ x:E in 𝓝 0,fderiv ℝ P.J x (Cast b a x)+duty B (fderiv ℝ (Cast b a) x)*P.J x=0:=by
       let Q:=tug b a; let J:=P.J; have ht:= tug_live b a
       have hx:∀ᶠ z:ℝ×E in 𝓝 0,z.2∈ball 0 P.radius∧ Q z∈ball 0 P.radius∧ G.lieExp (Q z)=snap b a z∧ ContDiffAt ℝ ω Q z :=by
            filter_upwards [(continuous_snd.continuousAt (x:=(0:ℝ×E))).eventually (ball_mem_nhds (0:E) H.patch), ht.continuousAt.eventually (by rw [tug_zero];exact ball_mem_nhds 0 H.patch), snatched b a, ht.eventually (by simp)] with x h₁ h₂ h₃ h₄ using ⟨h₁,h₂,h₃,h₄⟩
       filter_upwards [((ContinuousLinearMap.inr ℝ ℝ E).continuous.tendsto 0).eventually (p:=fun i:ℝ×E=> ∀ᶠ z in 𝓝 i,z.2∈ball 0 P.radius ∧ Q z∈ball 0 P.radius∧ G.lieExp (Q z)=snap b a z∧ ContDiffAt ℝ ω Q z) (eventually_eventually_nhds.mpr hx), (eventually_eventually_nhds.mpr (bark b a))] with x hx hh
       change (∀ᶠ z:ℝ×E in 𝓝 (0,x), z.2∈ball 0 P.radius ∧ Q z∈ball 0 P.radius∧ G.lieExp (Q z)=snap b a z∧ ContDiffAt ℝ ω Q z) at hx; have he:=hx.self_of_nhds
       let D(t:ℝ):= (fderiv ℝ (fun y=>Q (t,y)) x).det; have hd:D 0=1:=by unfold D; rw [show fderiv ℝ _ _=ContinuousLinearMap.id ℝ E from EventuallyEq.fderiv_eq (show (fun y:E=>Q (0,y)) =ᶠ[𝓝 x] id from hh)|>.trans fderiv_id]; exact map_one LinearMap.det
       have hz:Q (0,x)=x:= hh.self_of_nhds
       let F:=fderiv ℝ J x; have hf:HasDerivAt (fun t=> J (Q (t,x))) (F (Cast b a x)) 0:=HasFDerivAt.comp_hasDerivAt 0 (show HasFDerivAt _ F (Q (0,x)) by rw [hz]; exact ((H.germ _ he.1).differentiableAt (by simp)).hasFDerivAt) (sky Q he.2.2.2)
       have hV:= port Q he.2.2.2 B hh; have hD: HasDerivAt D (duty B (fderiv ℝ (Cast b a) x)) 0:=hV; have hv:∀ᶠ t in 𝓝 (0:ℝ),∀ᶠ z:ℝ×E in 𝓝 (t,x), z.2∈ball 0 P.radius ∧ Q z∈ball 0 P.radius ∧ G.lieExp (Q z)=snap b a z∧ ContDiffAt ℝ ω Q z:=((continuous_id.prodMk continuous_const).continuousAt (x:=(0:ℝ))).eventually (eventually_eventually_nhds.mpr hx)
       have hp:(fun _ : ℝ=> J x) =ᶠ[𝓝 0] (fun t=>D t*J (Q (t,x))):=by
            filter_upwards [hv,hD.continuousAt.eventually (lt_mem_nhds (by rw [hd];norm_num : 0 <D 0))] with t h h'; change 0 <D t at h'; have he:= h.self_of_nhds; rw [← abs_of_pos h']; have hl: ContDiffAt ℝ ω (fun y:E=>Q (t,y)) x:= he.2.2.2.comp (f:=fun y:E=>(t,y)) x (contDiffAt_const.prodMk contDiffAt_id)
            refine costsRight (f:=fun y:E=>Q (t,y)) H (patron b (G.lieExp (t • a))) he.1 he.2.1 hl ?_; filter_upwards [((continuous_const.prodMk continuous_id).continuousAt (x:=x)).eventually h] with y hy; exact hy.2.2.1
       have h:= ((hD.mul hf).congr_of_eventuallyEq hp).unique (hasDerivAt_const (0:ℝ) _); rw [hd,hz,one_mul] at h; rw [add_comm]; exact h
end YM.OPE.Variance
