import YM.FormalBulk08.Plait.Verm

/-! Critical data taken from low unmasked E-port. `AxisChart`
coordinates relative replica only here. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Hay
open Filter Set Function MeasureTheory Lattice RG Exterior Wilson Precision Tree Work.F05
open Stationary hiding shine Rays
open Reef Series Wick Jets Orb Plait
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{c f:Side}{S:StepData c f}(F:Forest S.ratio)

abbrev Rot (F:Forest S.ratio)(G:Gauge):= Jets.Rays (Pine G S F ⊕ wire G c)
-- copy chart

def copes (x:Rot F G) := exposure F (arm G c 1 (secondL x)) (stand G F (firstL x))
def rectum (x:Rot F G) := (stand G F).symm (fun i=>G.plog (G.mat (copes F x i)))
lemma cope_zero : copes F (G:=G) 0=1:= by unfold copes; rw [show secondL _=0 from rfl,show firstL _=0 from rfl,map_zero,map_zero,exposure_zero]
lemma rect_zero : rectum F (G:=G) 0=0:= by unfold rectum;rw [cope_zero]; simp only [Pi.one_apply,G.mat_one, show G.plog 1=0 from (by simp)];exact map_zero _
lemma cope_so : Army (copes F (G:=G)) 0:= by
   intro i; let q:=fun x:Rot F G=> (arm G c 1 (secondL x), stand G F (firstL x))
   have he:q 0=0:= by unfold q;rw [show secondL _=0 from rfl,show firstL _=0 from rfl,map_zero,map_zero];rfl
   exact ContDiffAt.comp (f:=q) (g:=fun z=>G.mat (exposure F z.1 z.2 i)) 0 (by rw [he]; exact exposure_jet ..) (((arm G c 1).contDiff.contDiffAt.comp _ (second_lit ..)).prodMk ((stand G F).contDiff.contDiffAt.comp _ (first_lit ..)))
lemma rect_so : ContDiffAt ℝ ω (rectum F (G:=G)) 0:= by
   refine ContDiffAt.comp (g:=⇑(stand G F).symm) _ (stand G F).symm.contDiff.contDiffAt (contDiffAt_pi.mpr fun i=>?_); exact ContDiffAt.comp (g:=G.plog) _ (by rw [cope_zero];simp only [Pi.one_apply,G.mat_one]; exact G.plog_diff) (cope_so F i) -- transport
lemma cope_pay : ∀ᶠ x: Rot F G in 𝓝 0, exposure F 0 (stand G F (rectum F x))=copes F x := by
    have he i:= (tendsto_pi_nhds.mp (show Tendsto (copes F) (𝓝 0) (𝓝 (1:F.Slice G)) from cope_zero F ▸ (cope_so (G:=G) F).cont.tendsto) i).eventually G.plog_right
    filter_upwards [eventually_all.mpr he] with x hx;rw [rectum,(stand G F).apply_symm_apply]; ext1 a; simp only [exposure,link_one, replica_one,Pi.one_apply,mul_one]; exact hx a
lemma rect_score : dollars (rectum F (G:=G)) 0=1:= by
    let X:= rectum F (G:=G); have hp : (X∘ together (0:Link G c)) =ᶠ[𝓝 0] id:= by
       have ht (i:F.Free): Tendsto (fun x=> stand G F x i) (𝓝 0) (𝓝 0):= tendsto_pi_nhds.mp (by simpa using (stand G F).continuous.tendsto 0) i
       filter_upwards [eventually_all.mpr (fun i=> (ht i).eventually G.plog_left)] with x hx
       apply (stand G F).injective; unfold X rectum; rw [Function.comp_apply, (stand G F).apply_symm_apply]; funext a; simp only [copes,unites,map_zero,pairs_with, exposure,link_one,replica_one, Pi.one_apply,mul_one]; exact hx a
    ext1 i j
    have he : (fun z=> X (together 0 z) i) =ᶠ[𝓝 0] (fun x:Pine G S F→ℝ=> x i):= hp.mono fun j hj=> congr_fun hj i
    have hk: DifferentiableAt ℝ (fun z=> X z i) 0:= differentiableAt_pi.mp ((rect_so (G:=G) F).differentiableAt (by simp)) i
    change pearlD (fun z=> X z i) (Sum.inl j) 0=_; have hy:together (0:Link G c) (0:Jets.Rays (Pine G S F))=0:= by ext i;cases i <;> rfl
    rw [←hy]; rw [tooth _ _ _ (show DifferentiableAt ℝ _ _ from (by rw [hy];exact hk))]; unfold pearlD Function.comp; rw [Filter.EventuallyEq.fderiv_eq he,show fderiv ℝ (fun x:Pine G S F→ℝ=>x i) 0= _ from (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Pine G S F=>ℝ) i).hasFDerivAt.fderiv];simp [Matrix.one_apply,dotI,Pi.single_apply]
lemma rect_wall (P: ChartRatio G)(h: LocalRatio P) :
     ∀ᶠ x:Rot F G in 𝓝 0,sap F P (firstL x)=sap F P (rectum F x)*(dollars (rectum F) x).det:= by
   let W(x:Link G c) (i:F.Free):= replica S.ratio (input G c x) i
   let f (x:Link G c)(b:F.Slice G):= b*W x; have he (x:Link G c) : MeasurePreserving (f x) (F.order G) (F.order G):= measurePreserving_pi (fun _=> G.probHaar) (fun _=> G.probHaar) (fun i=>measurePreserving_mul_right _ (W x i))
   have hi (x:Rot F G): copes F x= f (secondL x) (exposure F 0 (stand G F (firstL x))):= by funext i; simp [copes,f,exposure,W,input]
   obtain ⟨M,H,H'⟩:= bread F P h (rectum F) f he (fun i _ _ hu=>mul_right_cancel hu) ((cope_pay F).mono fun x hx=>hx.trans (hi x)) ((rect_so F).of_le le_top) (rect_zero F)
   rw [rect_score F, one_mul] at H; subst M; simp only [Matrix.det_one,one_mul] at H'; exact H'
end YM.FormalBulk08.Hay
