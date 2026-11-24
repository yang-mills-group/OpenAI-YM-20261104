import YM.WilsonCoeffUV.Kinetic.Slice
/-!
# The stationary action on the same registration
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Power.Roam
open Lattice Laurent Bloch Exterior Wilson Precision RG Function Filter
open Blue MeasureTheory Set Metric Matrix Gauge PowerSeries
open FreeResolvent Tree Stationary Cameo Bank Mosaic Work.F08
open YM.PertExtension.Chart (tangent physical expLinks jacobian fee)
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {c f n : Side}{G:Gauge}(S:StepData c f)(F:Forest S.ratio)
variable (M: Matrix (Woods G f) (Woods G c) ℝ) {ρ: fieldDir G c 1→ AxisChart G F}
variable {s A B e:ℝ}{u:Clip}{R:PathData G}

-- normalized FLASH exact from P. No masks.
lemma rye_top (K:R.Bounds u s A B)(n:Side):
   Green (intended u R (m:=n)) ∧ X^2 * Blue.flash (sprig (intended (m:=n) u R) 2)=jet (intended (m:=n) u R) :=by
    rw [intent _ _,firstTerm K n]
    let F: Link G n →ℝ:= u.direct • eWilson; let P:Stack G 0:=tides R
    have hf: Green (eWilson (G:=G) (c:=n)):= W_green
    have he: Green F:= hf.const_smul u.direct
    let H:Link G n→ℝ:= F+turnSeries P; have ht:Green (turnSeries P (m:=n)):= (turns_analytic _ K.width (tides_pay K)).contDiffAt
    have hH:Green H:= he.add ht
    have hX: Green (turnSeries R.cubic (m:=n)):= (turns_analytic _ K.width K.three).contDiffAt
    have hY: Green (turnSeries R.quartic (m:=n)):= (turns_analytic _ K.width K.four).contDiffAt
    have hp i (hx:i<2): rye (H+turnSeries R.cubic+turnSeries R.quartic) i=0:=by
        rw [rye_plus (H+turnSeries R.cubic) (turnSeries R.quartic) (hH.add hX) hY,rye_plus H _ hH hX]; unfold H; rw [rye_plus F _ he ht,rye_mu (G:=G) u.direct _ hf]
        have hz (j:ℕ) (P:ℕ→Atom G j)(v:i<j) (a:ℝ) (p:SumBudget (fun i=> (P i).budget s) a) : rye (turnSeries P (m:=n)) i=0:= by
           funext x; rw [rye,(rays_jet (turns_analytic P K.width p) j).1 (turns_low P K.width p) i v]; simp
        have ht : X^2*Blue.flash (sprig (eWilson (G:=G) (c:=n)) 2) = jet (eWilson (G:=G) (c:=n)):=sprouts_move (w_jets (G:=G) (H:= unitRow (TypeFace 2)) (Work.F08.acts_unit n)).1 (w_jets (G:=G) (H:=unitRow (TypeFace 2)) (Work.F08.acts_unit n)).2.1
        have hv: rye (eWilson (G:=G) (c:=n)) i=0:=by
           apply unique_kernel (rye_sym W_green _) Blue.Smooth.zero
           rw [map_zero,← jet_apply,← ht,coeff_X_pow_mul',if_neg (by omega)]
        rw [hv,hz 2 P hx (gramCost G A) (tides_pay K),hz 3 R.cubic (by omega) A K.three,hz 4 R.quartic (by omega) A K.four,smul_zero,zero_add,zero_add,zero_add]
    exact ⟨(hH.add hX).add hY,moves (H+turnSeries R.cubic+turnSeries R.quartic) (fun i t=>by rw [jet_apply,hp i t,map_zero])⟩
-- some easy constants before scale path
lemma loop_zero_r (K:R.Bounds u s A B)(n:Side): constantCoeff (jet (turnSeries R.loop (m:=n)))=0:=by
    rw [← coeff_zero_eq_constantCoeff_apply,jet_apply,show rye (turnSeries R.loop (m:=n)) 0=0 from ?_,map_zero]
    funext x; rw [rye,(rays_jet (turns_analytic R.loop K.width K.two) 2).1 (turns_low R.loop K.width K.two) 0 (by omega)]; simp

abbrev oldMain (K: Clip)(P:PathData G)(n:Side):PChart G n:=sprig (intended K P) 2
def last_dear (u:Clip)(R:PathData G):Blue.Ink (Active G F⊕Woods G c):=
    loom (camSlice G S F M) (Blue.flash (oldMain u R f))+loom (panSlice G S F M) (Blue.flash (sprig (jointPen G S) 2))
def dust (Ñ:ChartRatio G)(R:PathData G) : Blue.Ink (Active G F⊕Woods G c):= loom (camSlice G S F M) (jet (unhaar Ñ)-jet (turnSeries R.loop))
variable {Ñ:ChartRatio G} (H Y:FreeResolvent.FaceRow)(Q: Matrix (Body 1 f) (Body 1 c) ℝ)
lemma dust_seed (h:LocalRatio Ñ)(K:R.Bounds u s A B)(v:Inputs S Q (H.acts f) (Y.acts c))(p:(H.acts f).transpose=H.acts f)(q: S.patch.Branches S.kernel G) (a:front R u f 0=shine (orbQ (precisionC G f H))):
    let M:=extractV G S F Q
    Hearth (treeMatrix G S F H) (orbC (precisionC G c Y)) (shot S F Q Ñ (front R u f)) (last_dear S F M u R) (dust S F M Ñ R):=by
    intro M
    let P: PChart G f := front R u f
    let U':= treeMatrix G S F H; let F':= dust S F M Ñ R
    have he : constantCoeff F'=0:=by
        have he:constantCoeff (jet (unhaar (n:=f) Ñ))=0:=by rw [jet_lead,unhaar_zero h,map_zero]
        apply floor_pres (T:=loom (camSlice G S F M)) _ (by rw [map_sub,he,loop_zero_r K,sub_self]); simp [loom]
    let Z:=shot S F Q Ñ P
    have ht : constantCoeff Z=0:= by
       unfold Z shot; exact floor_pres (show loom _ X=X by simp [loom]) (flash_blank (pack_zero S h))
    let X:=orbC (precisionC G c Y)

    have hv : Z=bodyQ (Woods G c) U'+holdUp _ X-last_dear S F M u R+F':=by
        have he : Blue.flash (sprig (turnSeries R.loop (m:=f)) 0) = jet (turnSeries R.loop):= by rw [sprig_flash]; simp; rfl
        rw [show Z=_ from shot_bill S F H Y Q (stance K _) (show P 0=_ from ?_) q v p]
        · unfold unscaled last_dear F' dust
          rw [show P=oldMain u R f+sprig _ 0 from rfl,flash_add (finite_shell (sprig_count _ _)) (finite_shell (sprig_count _ _)),he,map_add,map_sub]; unfold M X U'; abel
        assumption
    refine ⟨?_,he,hv⟩; rw [hv,map_add,he,add_zero,map_sub,sub_eq_zero] at ht; exact ht.symm

def motorD (M:Matrix (Woods G f) (Woods G c) ℝ)(Ñ:ChartRatio G)(R:PathData G) (x:Sloc S F G) : ℝ := let b:= camSlice G S F M*ᵥ x; unhaar Ñ b-turnSeries R.loop b
def pointRotor (u:Clip)(R: PathData G)(ρ: fieldDir G c 1→AxisChart G F) (x:Sloc S F G) := tested F (tac S) u R (badge S F x) (sedan S F ρ x).1
def vigor (Ñ:ChartRatio G) (R:PathData G)(M:Matrix (Woods G f) (Woods G c) ℝ) (ρ:fieldDir G c 1→AxisChart G F)(x: Sloc S F G) := stampJ S F ρ Ñ x - turnSeries R.loop (camSlice G S F M *ᵥ spider (shore S F M ρ) x)

lemma badge_base (x:Stationary.Link G c): badge S F (piIn x) = arm G c 1 x:=rfl
lemma riderC (h:Critical F u R ρ): Green (pointRotor S F u R ρ):=by
   let Y (x: Sloc S F G):= (badge S F x,(sedan S F ρ x).1)
   have H : Y 0=0:=Prod.ext (map_zero _) (by unfold Y; rw [sedan_zero S F ρ h.1]; rfl)
   have hx:= (h.2.2 (tac S)).1; rw [← H] at hx; exact (hx.comp (f:=Y) 0 ((badge_green S F).prodMk (contDiffAt_fst.comp _ (sedan_green S F ρ h.2.1))))
lemma stall (h:Critical F u R ρ): ∀ i:Active G F,∀ᶠ x: Stationary.Link G c in 𝓝 0,avenue (pointRotor S F u R ρ) i x=0:=by
    let V:= arm G c 1
    have ht:=(immersion (U:=Active G F) (V:=Woods G c)).continuousAt.tendsto; rw [show piIn (U:=Active G F) (0:Lawn (Woods G c))=0 from funext fun i=>by cases i<;>rfl] at ht
    have he:=V.continuous.tendsto 0; rw [map_zero] at he
    intro i; filter_upwards [ht.eventually ((riderC S F h).eventually (by simp)), he.eventually (h.2.2 (tac S)).2] with x hX hf; let b: Sloc S F G→ℝ:=pointRotor S F u R ρ
    have hv : (b∘barL x)= (tested F (tac S) u R (V x)) ∘ (fun v=> vcloth S F G v+ρ (V x)):=rfl
    change rub b (.inl i) (barL x 0)=_
    rw [←edge_snap x _ 0 (hX.differentiableAt (by simp)),hv]
    let L:=vcloth S F G
    have hL:= (L.hasFDerivAt (x:=0)).add_const (ρ (V x));
    have hz:ρ (V x) = L 0+ρ (V x):= by rw [map_zero,zero_add]
    have hZ:= hf; rw [hz] at hZ
    unfold Blue.rub; rw [show (fun v=> vcloth S F G v+ρ (V x))= (fun v=> L v + ρ (V x)) from rfl,(hZ.comp 0 hL).fderiv]; rfl
-- Precision.ClassicalMatch implies jets via exact pull on Replica.
lemma fueled (K:R.Bounds u s A B) (h:Critical F u R ρ)(p:M=reveal G S F*((reveal G S F).transpose*M))(q:S.patch.Branches S.kernel G) :
     Fathom (pointRotor S F u R ρ) (shore S F M ρ) (last_dear S F M u R):=by
    have hx:S.patch.Branches S.kernel G:= q
    let C:=camSlice G S F M; let D:=panSlice G S F M; let Φ:=shore S F M ρ; let V:=spider Φ
    have hv :=spider_zero (shore_zero S F M _ h.1); have he:= spider_green (shore_green S F M ρ h.2.1 h.1)
    refine ⟨shore_zero S F _ _ h.1, shore_green S F _ _ h.2.1 h.1, initial_edge S F _ _ h.2.1 h.1,riderC S F h,fun i=> jet_congr (stall S F h i) |>.trans ?_,?_⟩
    · rw [jet_const,map_zero]
    let A : Sloc S F G→ℝ:= fun x=> intended u R (C*ᵥ x)
    let B : Sloc S F G→ℝ:=fun x=>jointPen G S (D*ᵥ x)
    have hf:= penSmooth G S q; have ha:=rye_top K f
    have hy:Green A:= ContDiffAt.comp (g:=intended u R) (f:=fun x=> C*ᵥ x) _ (by simp; exact ha.1) (board _)
    have hb:Green B:= ContDiffAt.comp (g:=jointPen G S) (f:=fun x=> D*ᵥ x) _ (by simp; exact hf) (board _)
    have hf₁ : PowerSeries.X^2*last_dear S F M u R= jet (A+B) := by
        have hv : PowerSeries.X^2*loom C (Blue.flash (oldMain u R f))=jet A:=by
           change PowerSeries.X^2*loom C (Blue.flash (sprig (intended u R) _))=jet A; conv_lhs=> arg 1; arg 1; rw [← show loom C X=X by simp [loom]]
           rw [← map_pow,←map_mul,ha.2,loom_jet C _ ha.1]
        unfold last_dear; rw [mul_add,hv,jet_add (f:=A) (g:=B) hy hb]; congr 1
        change PowerSeries.X^2*loom D _= _; conv_lhs=> arg 1; arg 1; rw [← show loom D X=X by simp [loom]]
        rw [← map_pow, ← map_mul,sprouts_move (pen_jets G S q).1 (pen_jets G S q).2.1,loom_jet D _ hf]
    rw [pivot]
    have hF : retool Φ X=X:=reroll_X ..; rw [pivot] at hF
    change _ * train (spool V) _= _
    conv_lhs=> arg 1; arg 1; rw [←hF]
    rw [←map_pow, ←map_mul, hf₁, traveling V he hv (A+B) (show Green (A+B) from hy.add hb)]; apply jet_congr
    filter_upwards [tilted S F M ρ p h.2.1 h.1] with x hh; change A (V x)+B (V x)=_
    unfold A B D C
    simp only [intended, Mosaic.mantle_input,arm_pan,jointPen]
    change mainTerm _ _ (mantle (C *ᵥ spider (shore S F M ρ) x)) + noiseTaylor S (mantle (rightArm x)) (mantle (C *ᵥ spider (shore S F M ρ) x)) _ = _
    unfold C; rw [hh]; rfl

lemma vigors (K:R.Bounds u s A B)(h:Critical F u R ρ)(q: LocalRatio Ñ)(p:M=reveal G S F*((reveal G S F).transpose*M))(hv:S.patch.Branches S.kernel G):
    Green (vigor S F Ñ R M ρ) ∧ vigor S F Ñ R M ρ 0=0 ∧ Cameo.blaze (shore S F M ρ) (dust S F M Ñ R) (vigor S F Ñ R M ρ):=by
    let V:= vigor S F Ñ R M ρ; let L:= motorD S F M Ñ R; let X:=camSlice G S F M
    let a: Link G f→ℝ:=turnSeries R.loop; let Θ:=shore S F M ρ
    have ht:=fueled S F M K h p hv
    have hw:Green a:= (turns_analytic _ K.width K.two).contDiffAt; have hh:=loop_zero_r K f; rw [jet_lead] at hh; have hg:a 0=0:= by exact MvPolynomial.C_injective _ _ (hh.trans (map_zero _).symm)
    have he:= unhaar_green (n:=f) q
    let w (x:Sloc S F G):= X*ᵥ x; let hc:= board X
    have hy: Green L:= by change Green ((unhaar Ñ-a) ∘ w); exact ContDiffAt.comp (f:=w) (g:=unhaar Ñ-a) 0 (by rw [show w 0=0 from Matrix.mulVec_zero _]; exact he.sub hw) hc
    have hl : L 0=0:=by change _-_=_; rw [Matrix.mulVec_zero,unhaar_zero q]; exact sub_eq_zero.mpr hg.symm
    have he' : Green V:= by
       refine (stamp_d S F ρ _ q h.2.1 h.1).sub (ContDiffAt.comp (g:=a) (f:=fun x=>w (spider Θ x)) _ ?_ ?_)
       · rw [spider_zero ht.θo, show w 0=0 from Matrix.mulVec_zero _]; exact hw
       exact ((X.mulVecLin).toContinuousLinearMap.contDiff.contDiffAt).comp _ (spider_green ht.θp)
    have hp : V 0=0:=by unfold V vigor; rw [spider_zero ht.θo,stamp_o _ _ _ _ q h.1, Matrix.mulVec_zero]; exact sub_eq_zero.mpr hg.symm
    refine ⟨he',hp,?_⟩
    have hz : jet L=dust S F M Ñ R:= by
       unfold dust; rw [← jet_sub (f:=unhaar Ñ) he hw,loom_jet X _ (by apply he.sub hw)]; rfl
    rw [←hz]; apply blaze_new (h:=he') hp ht hy hl
    filter_upwards [shape_area S F M ρ Ñ h.2.1 h.1 q p] with x hx
    unfold V vigor L motorD; rw [Real.exp_sub,Real.exp_sub,mul_div_assoc']; refine congr_arg (· / _) hx

lemma v_frame (i: Active G F): vcloth S F G (pebble i)= Precision.frame F i := by
    classical
    ext p j; change Blue.pebble i (p,j)=Pi.single (M:=fun _=> G.Color) i.1 (EuclideanSpace.basisFun G.ColorIndex ℝ i.2) p j
    obtain ⟨i,a⟩:= i; by_cases h:p=i<;>by_cases v:j=a<;> simp [Blue.pebble, h,v]
lemma ride_rootC (w:Bod c G)(u) : (sedan S F ρ (barL w u)).1= ρ (arm G c 1 w) + vcloth S F G u:=add_comm ..
lemma solid (h:Critical F u R ρ): ∀ᶠ x:Bod c G in 𝓝 0, sandH (pointRotor S F u R ρ) x=hessian F (tac S) u R (arm G c 1 x) (ρ (arm G c 1 x)):=by
    let φ:=pointRotor S F u R ρ; let L:= arm G c 1
    have he:=(immersion (U:=Active G F) (V:=Woods G c)).continuousAt.tendsto; rw [show piIn (U:=Active G F) (0: Lawn (Woods G c))=0 from funext fun i=>by cases i<;>rfl] at he
    have hB : ContDiffAt ℝ ω (fun x:Lawn (Woods G c) => (L x,ρ (L x))) 0:=by
       exact ContDiffAt.prodMk L.contDiff.contDiffAt ((show ContDiffAt ℝ ω ρ (L 0) from by rw [map_zero]; exact h.2.1).comp _ L.contDiff.contDiffAt)
    have hb:=hB.continuousAt.tendsto; change Tendsto _ _ (𝓝 (L 0,_)) at hb; rw [map_zero,h.1] at hb
    let M (w:fieldDir G c 1):=tested F (tac S) u R w
    filter_upwards [he.eventually ((riderC S F h).eventually (by simp)),hb.eventually ((h.2.2 (tac S)).1.eventually (by simp))] with x hf hv
    have ht:ContDiffAt ℝ ω (M (L x)) (ρ (L x)):= hv.comp (f:=fun z=>(L x,z)) (ρ (L x)) (contDiffAt_const.prodMk contDiffAt_id)
    let J:=(vcloth S F G).toContinuousLinearMap; let b:=L x; let V z:= M b (ρ b+z)
    have hz : Green φ:= riderC S F h
    have hg : AnalyticAt ℝ V (J 0):= by rw [map_zero]; apply ContDiffAt.analyticAt; exact ContDiffAt.comp (f:=fun z=>ρ b+z) 0 (g:=M b) (by rw [add_zero]; exact ht) (contDiffAt_const.add contDiffAt_id)
    ext1 i j; rw [rubble _ i j hf, show φ ∘ barL x = V ∘ J from ?_]; swap; · funext y; unfold φ; simp_rw [Function.comp_apply, pointRotor, ride_rootC]; rfl
    rw [wired J hg,map_zero,show J ∘ _=![Precision.frame F i,Precision.frame F j] from ?_,show iteratedFDeriv ℝ 2 V 0=_ from iteratedFDeriv_comp_add_left ..]; swap; · funext k; fin_cases k; exacts [v_frame S F i,v_frame S F j]
    rw [add_zero]; rfl

set_option maxHeartbeats 250000 in
lemma dockJ (_:R.Bounds u s A B)(h:Critical F u R ρ)(ht:M=reveal G S F*((reveal G S F).transpose*M))(p:LocalRatio Ñ): ∀ᶠ x:Link G c in 𝓝 0, baseP (vigor S F Ñ R M ρ) x = Real.log (∏ i:F.Free, Ñ.J (ρ (arm G c 1 x) i))-loop R (lifting F (represent (arm G c 1 x)) (ρ (arm G c 1 x))) :=by
    have hz: Tendsto (arm G c 1) (𝓝 0) (𝓝 0):= by simpa using (arm G c 1).continuous.tendsto 0
    have hv:Tendsto ρ (𝓝 0) (𝓝 0):=by simpa only [h.1] using h.2.1.continuousAt.tendsto
    have he:=(immersion (U:=Active G F) (V:=Woods G c)).continuousAt.tendsto; rw [show piIn (U:=Active G F) (0:Lawn (Woods G c))=0 from funext fun i=>by cases i<;>rfl] at he
    have hh i:∀ᶠ x in 𝓝 0,0< Ñ.J (ρ (arm G c 1 x) i):= ((hv.comp hz).eventually (((continuous_apply i).tendsto (0:AxisChart G F)).eventually ((show ∀ᶠ v:G.Color in 𝓝 0, v∈ Metric.ball 0 Ñ.radius from ball_mem_nhds (0:G.Color) p.patch).mono (fun u hu=>p.pos _ hu)))) -- Eventually .mono path
    filter_upwards [eventually_all.mpr hh,he.eventually (tilted S F M ρ ht h.2.1 h.1)] with x ph hy
    let a:=ρ (arm G c 1 x); let b:= piIn (U:=Active G F) x; let L:=camSlice G S F M*ᵥ spider (shore S F M ρ) b
    have hZ:(sedan S F ρ b).1=a:=by unfold sedan; change vcloth S F G (0:Lawn (Active G F))+a=a; rw [map_zero,zero_add]
    change mantle L = lifting F _ (sedan S F ρ b).1 at hy; rw [hZ] at hy
    change unhaar Ñ (reveal G S F*ᵥ (vcloth S F G).symm (sedan S F ρ b).1)-turnSeries R.loop L=_
    have hr : turnSeries R.loop L= Precision.loop R (lifting F (represent (arm G c 1 x)) (ρ (arm G c 1 x))) :=by
        change Precision.loop R (input G f L)= _; rw [mantle_input,hy]; rfl
    rw [hr]; apply congrArg₂ (· - ·) _ rfl; rw [hZ,prism S F a Ñ p]; exact (Real.log_prod fun i (_:i∈Finset.univ)=> (ph i).ne').symm
lemma thermal_tip (K:R.Bounds u s A B)(h:Critical F u R ρ)(ht:M=reveal G S F*((reveal G S F).transpose*M))(p:LocalRatio Ñ): ∀ᶠ x: Link G c in 𝓝 0, vineT (pointRotor S F u R ρ) (vigor S F Ñ R M ρ) x = thermal F (tac S) u R ρ Ñ (arm G c 1 x):= by
    filter_upwards [dockJ S F M K h ht p,solid S F h] with x hb hh; unfold vineT thermal; rw [hb,hh]; ring
end YM.WilsonCoeffUV.Power.Roam
