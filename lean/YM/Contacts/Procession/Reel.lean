import YM.Contacts.Milling.Mint
/-! Relax unmarked epoch tooling Kale/Forge/River to arbitrary roots, reproduce relevant numerical arguments (largely wholesale from Milling/*), right at the same Beam and not secretly invoking signed symmetry. -/
namespace YM.Contacts.Milling
open Function Set Filter Metric Asymptotics MeasureTheory
open Finset Lattice RG Wilson Precision Exterior PertExtension.Series Pulse YM.Stationary ConnectedActivityE6 Push.SectorMeasure
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{c f n: Side}{k:ℕ}
namespace Kale
-- Ward prerequisites for an aggregate scalar homogeneous up to the current
-- `k` in (coupling,fields). Here section invariance at *fixed loop* ℓ. The aggregate
-- periodic shadows will have this even though the finite-torus expansion differs by winding.
structure GuardsL (P:Link G n→ℝ)(k:ℕ): Prop where
  cont: Continuous P
  analytic: AnalyticAt ℝ P 0
  color u x: P (stain u x)=P x
  grade: Rays k (fun z:Swatch G n=> P (moveField z)-P z.2)
variable {P:Link G n→ℝ}
lemma fire_contL (h: GuardsL P k): Continuous (fire P):= h.cont.comp ((bevel_cont _).comp active_cont)
lemma fire_colorL (h:GuardsL P k): GaugeInvariant (fire P):= fun t U=> by rw [fire,foldGauge,bevel_conj,h.color]; rfl
private def plasterL (x:Link G n): Swatch G n:= (frameLog (bring (input G n x)),x)
lemma flameL : AnalyticAt ℝ (plasterL (G:=G) (n:=n)) 0:= ContDiffAt.analyticAt ((Army.logG troops (by simp [brings_zero])).prodMk contDiffAt_id)
lemma flashL : plasterL (0:Link G n)=0:=by simp [plasterL,brings_zero]
lemma regionL : (bevel (G:=G) n∘ alive ∘ input G n) =ᶠ[𝓝 0] (moveField ∘ plasterL):= by
  have hi: Tendsto (bring ∘ input G n) (𝓝 0) (𝓝 (1:Coats G n)):= by simpa [brings_zero] using! (troops (n:=n) (G:=G)|>.cont.tendsto)
  have hp: Tendsto (alive ∘ input G n) (𝓝 0) (𝓝 (1:Config G n)):= by
    have he:alive (1:Config G n)=1:=by unfold alive; rw [brings_zero]; funext; simp [Lattice.gauge]
    simpa [he] using (active_cont.comp (input_cont (m:=n) (G:=G))).tendsto 0
  filter_upwards [hi.eventually switch_frameLog,hp.eventually (summit n)] with i hx hu; simp only [Function.comp_apply] at *; change bevel _ _ = content (Lattice.gauge (switchSite (frameLog _)) _); rw [hu,hx]; rfl
lemma firesL (h:GuardsL P k) : AnalyticAt ℝ (fire P ∘ input G n) 0 ∧ Rays k ((fire P ∘ input G n)-P):= by
  let p:=moveField (G:=G) (m:=n); have ht:(fire P ∘ input G n) =ᶠ[𝓝 0] ((P∘p)∘plasterL):= (regionL (n:=n) (G:=G)).mono fun i hi=> congr_arg P hi
  let q:= P∘p; have hp:AnalyticAt ℝ q 0:= AnalyticAt.comp (by unfold p; rw [moveField_zero]; exact h.analytic) moveField_analytic
  have hx : AnalyticAt ℝ (q∘plasterL) 0:= AnalyticAt.comp (by rw [flashL]; exact hp) flameL; refine ⟨hx.congr ht.symm,?_⟩; let F : Swatch G n→ℝ:= P∘Prod.snd; have hF : AnalyticAt ℝ F 0:= h.analytic.comp (f:=⇑(ContinuousLinearMap.snd ℝ (BaseSites G n) (Link G n))) (ContinuousLinearMap.analyticAt _ _) -- comp
  intro v; exact (merkin (hp.sub hF) h.grade _ (flameL (G:=G) (n:=n)) flashL v).congr' ((along v).eventually ((ht.sub (f:=_) (.refl _ _))).symm) .rfl -- inspect
structure WedgeL (F: Config G n→ℝ): Prop where
  invariance : GaugeInvariant F
  consent: Continuous F
  radiant: AnalyticAt ℝ (F∘ input G n) 0
lemma fireLife (h: GuardsL P k): WedgeL (fire P):= ⟨fire_colorL h, fire_contL h,(firesL h).1⟩
end Kale
end
end YM.Contacts.Milling
noncomputable section
namespace YM.Contacts.Milling
open Function Set Filter Metric MeasureTheory Asymptotics
open Finset Lattice RG Wilson Precision Exterior PertExtension.Series Pulse YM.Stationary Tree
open Kale
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge}{c f: Side}{T:Ratio c f}(A:Forest T){n:ℕ}
variable {X V : Type}[NormedAddCommGroup V][NormedSpace ℝ V][FiniteDimensional ℝ V]
structure SensorL (M:ℝ→ Config G f→ Config G c→ℝ) (T:Ratio c f):Prop where
     color (t:ℝ) (k:Site f→ G.El) U V: M t (Lattice.gauge k U) (Lattice.gauge (k∘T.embed) V)=M t U V
local notation "φ" => 𝓝[>] (0:ℝ)
variable {M:ℝ→ Config G f→ Config G c→ℝ}{g:cap G c→ℝ}
lemma flash_foldL (h:SensorL M T) (t:ℝ)(U:Config G f)(V:Config G c): M t (A.drape (dawn A U)) V=M t U V:= by
  rw [dawn_d]; have he:= h.color t (A.foldAt U) U V; convert he using 2; funext; simp only [Lattice.gauge,Function.comp_apply,A.fold_root,inv_one,one_mul,mul_one]
lemma sensorGateL {b:ℝ}(h:SensorL M T)(hg:AnalyticAt ℝ g 0)(hc:Radial.Stationary g)(he:Sight (runner M A) g b n)
    (U Y: V→ Link G c)(hU:AnalyticAt ℝ U 0)(hZ:U 0=0)(hY:AnalyticAt ℝ Y 0)(hY':Y 0=0) (L:V → (Config G f ≃ₜ Config G f)) (hp:∀ x, Kale.released T (L x)) (hS:∀ x, Kale.released T (L x).symm) (hT : ∀ x,MeasurePreserving (L x) (prior G f) (prior G f))
    (hμ : ContinuousAt (fun x : V × Config G f=> L x.1 x.2) (0,1))(hv:ContinuousAt (fun x: V × Config G f=>(L x.1).symm x.2) (0,1))(hl : L 0 1=1)
    (hK : ∀ᶠ x in 𝓝 (0:V),∀ t a,M t (L x a) (input G c (Y x))=M t a (input G c (U x))) : Rays (n+3) ((g∘axisRoll U)-(g∘axisRoll Y)):= by
  let Q:=g∘axisRoll U; let P:=g∘axisRoll Y; have hE (V:V→Link G c)(h:AnalyticAt ℝ V 0)(he:V 0=0): AnalyticAt ℝ (axisRoll V) 0 := ContDiffAt.analyticAt (contDiffAt_fst.prodMk (h.contDiffAt.comp (f:=Prod.snd) _ contDiffAt_snd))
  have hpP : axisRoll Y 0=0 := Prod.ext rfl hY'; have hpQ:axisRoll U 0=0:= Prod.ext rfl hZ; have hP : AnalyticAt ℝ P 0 := AnalyticAt.comp (by rw [hpP]; exact hg) (hE _ hY hY'); have hQ:AnalyticAt ℝ Q 0 := AnalyticAt.comp (by rw [hpQ]; exact hg) (hE _ hU hZ)
  refine benchPitch (hQ.sub hP) fun x=> marker (hQ.sub hP) _ (sample_cost (merkin hg (rays_cast hg hc) _ (hE _ hU hZ) hpQ) (merkin hg (rays_cast hg hc) _ (hE _ hY hY') hpP) _ _ ?_)
  let y:ℝ→ Link G c:=fun t=>t⁻¹ • Y (t • x); let w:ℝ→ Link G c:= fun t=> t⁻¹ • U (t•x)
  obtain ⟨k,hk⟩:= winged _ hU hZ x; obtain ⟨r,hr⟩:= winged _ hY hY' x; have hb : ∀ᶠ t in φ, ‖w t‖ ≤ max k r ∧ ‖y t‖≤ max k r:= (hk.and hr).mono fun t ht=> ⟨ht.1.trans (le_max_left ..),ht.2.trans (le_max_right ..)⟩
  let ℓ(t:ℝ): A.Slice G≃ₜA.Slice G:= swing A (hp (t•x)) (hS _); let u:= A.order G; let Φ:=φ ×ˢ (𝓝 (1:A.Slice G));
  have Hx:Tendsto (fun t:ℝ=> t•x) φ (𝓝 0):=(along x).mono_left (nhdsGT_le_nhdsNE _); have hu:Tendsto (fun x: A.Slice G=> A.drape x) (𝓝 1) (𝓝 1):=by simpa [curtain_one] using! (Forest.continuous_drape A (G:=G)).tendsto 1
  have hi:Tendsto (fun z:ℝ×A.Slice G=> (z.1 • x,A.drape z.2)) Φ (𝓝 (0,1)):= ((Hx.comp tendsto_fst).prodMk_nhds (hu.comp tendsto_snd))
  have hh:Tendsto (fun z:ℝ×A.Slice G=>ℓ z.1 z.2) Φ (𝓝 1):= by have hz:= hμ.tendsto; rw [show L _ _=_ from hl] at hz; -- unfolds?
                                                                                 exact (show Tendsto (dawn A) _ _ from by simpa using! (dawn_cont A (G:=G)).tendsto 1).comp (hz.comp hi)
  have hy:Tendsto (fun z:ℝ×A.Slice G=>(ℓ z.1).symm z.2) Φ (𝓝 1):= by
    have he:= hv.tendsto; erw [show (L 0).symm 1=1 from (L 0).symm_apply_eq.mpr hl.symm] at he; exact (show Tendsto (dawn A) (𝓝 1) (𝓝 (1:A.Slice G)) from (by simpa using! (dawn_cont A (G:=G)).tendsto 1)).comp (he.comp hi)
  have hA : ∀ᶠ t in φ, MeasurePreserving (ℓ t) (PertExtension.Chart.physical G _) (PertExtension.Chart.physical G _) ∧ runner M A (t,t•y t) ∘ ℓ t = runner M A (t,t• w t) := by
    filter_upwards [Hx.eventually hK,Tested.eventually_pos] with t he ht; refine ⟨swing_preserve _ _ _ (hT _),funext fun u=> ?_⟩; change M t (A.drape (dawn A _)) (input G c _) = M t _ (input G c _); unfold w y; rw [smul_inv_smul₀ ht.ne', smul_inv_smul₀ ht.ne', flash_foldL A h]; exact he _ _
  obtain ⟨C,hC,H⟩:= shaded he hh hy w y hA hb; refine ⟨C,hC, (Tested.eventually_pos.and H).mono fun t ht=>?_⟩; have hx (f:V→Link G c): sample g (1,t⁻¹ • f (t • x)) t=sample (g ∘ axisRoll f) (1,x) t:= by unfold sample Function.comp axisRoll; rw [show t • ((1:ℝ),_)= (t • (1:ℝ),f (t• x)) from Prod.ext rfl (smul_inv_smul₀ ht.1.ne' _)]; rfl
  change ‖Real.exp _-Real.exp _‖≤ _; rw [←hx U, ←hx Y]; exact ht.2
lemma buffersL {b:ℝ}(h:SensorL M T)(hg:AnalyticAt ℝ g 0)(hc:Radial.Stationary g)(he:Sight (runner M A) g b n)(u:G.El): Rays (n+3) (g-(g∘axisRoll (stain u))):= by
   let k:= fun _:Site f=> u
   refine sensorGateL A h hg hc he id (stain u) analyticAt_id rfl ((stain u).analyticAt _) (map_zero _) (fun _=> roam f k) (fun _=> roam_fed T k) (fun _=> roam_fed T k⁻¹) (fun _=> prior_gauge k) ((Homeomorph.continuous _).continuousAt.comp continuousAt_snd) ((Homeomorph.continuous_symm _).continuousAt.comp continuousAt_snd) ?_ ?_
   · ext1 i; change u*1*u⁻¹=1; group
   exact Eventually.of_forall fun x t a=> by rw [← stain_cons u x]; exact h.color t k ..
lemma costs_nowL {b:ℝ}(h:SensorL M T)(hg:AnalyticAt ℝ g 0)(hc:Radial.Stationary g)(he:Sight (runner M A) g b n): Rays (n+3) (g ∘ axisRoll (Prod.snd (α:=BaseSites G c))-g ∘ axisRoll (moveField (G:=G) (m:=c))):= by
   let k (x:Swatch G c):= switchSite x.1 ∘ T.parent; have hi i: Continuous (fun x=> k x i) := (continuous_apply _).comp (switch_cont.comp continuous_fst)
   refine sensorGateL A h hg hc he Prod.snd moveField contDiffAt_snd.analyticAt rfl moveField_analytic moveField_zero (fun x=> roam f (k x)) (fun _=> roam_fed T _) (fun i=> roam_fed T (k i)⁻¹) (fun i=> prior_gauge (k i)) ?_ ?_ ?_ ?_
   · refine (continuous_pi (fun i=> ?_)).continuousAt; exact ((hi _|>.comp continuous_fst).mul ((continuous_apply i).comp continuous_snd)).mul (hi _|>.inv.comp continuous_fst)
   · refine (continuous_pi (fun i=>?_)).continuousAt; exact ((hi _ |>.inv.comp continuous_fst).mul ((continuous_apply i).comp continuous_snd)).mul (hi _|>.inv.inv.comp continuous_fst)
   · change Lattice.gauge (k 0) 1=1; ext1 i; simp [k,Lattice.gauge]
   filter_upwards [moveField_germ (G:=G) (m:=c)] with i hi t a; rw [hi,show shiftLinks i=Lattice.gauge (k i ∘ T.embed) (input G c i.2) from (by unfold shiftLinks; rw [show k i ∘ T.embed=switchSite i.1 from funext fun j => by simp [k,Ratio.embed_parent]])]; exact h.color t (k i) _ _
end YM.Contacts.Milling
namespace YM.Contacts.Milling
open Function Set Filter Metric MeasureTheory Asymptotics
open Finset PertExtension.Series Pulse Pulse.Form Radial Ion YM.Stationary
open scoped Topology BigOperators ContDiff Classical
noncomputable section
variable {α β : Type}[Fintype α][Fintype β]
variable {n:ℕ}
open House Kale
open Lattice RG Wilson Tree
variable {G:Gauge}{c f:Side}
lemma wind_guardL {M:ℝ→ Config G f→ Config G c→ℝ} (P:House (Lines G c 1)){T:Ratio c f}(A:Forest T)(ho:Odd T.count.val){b:ℝ}(h:Sight (runner M A) (swell P (n+3)) b n)(hp:SensorL M T): ∀ i<n+3,GuardsL (wind P (n+3) i) (n+3-i):= by
    let p:=swell P (n+3); let F:=wind P (n+3); have he:=spectrum P (n+3); have hv:=orchestra P (n+3)
    have H u:= buffersL A hp hv he h u; have ha i:=wind_controls P i (n+3); have hl i:= wind_ana P (n+3) i 0
    have ht (Q:Link G c →L[ℝ] Link G c) (hq:Rays (n+3) (p-p ∘ axisRoll Q)): ∀ i<n+3,F i ∘ Q=F i := by
       intro i hi; apply Eq.symm (instant (ha _) (repeater (ha _) Q) (show Rays _ _ from transported (P:=F) (L:=id) (Y:=Q) (fun i _=>hl i) analyticAt_id rfl (Q.analyticAt _) Q.map_zero hq i hi))
    intro i hi; refine ⟨continuous_iff_continuousAt.mpr (fun x=>(wind_ana ..).continuousAt),hl _,fun u x=>congr_fun (ht (stain u) (H u) i hi) x,fun x=> ?_⟩
    have hh:= transported (P:=F) (L:=Prod.snd) (Y:=moveField) (fun i _=>hl i) contDiffAt_snd.analyticAt rfl moveField_analytic moveField_zero (costs_nowL A hp hv he h) i hi x; refine hh.neg_left.congr_left (fun b=>?_); change -( F i _-F i _)= F i _-F i _; abel
end
end YM.Contacts.Milling
noncomputable section
namespace YM.Contacts.Milling.Forge
open Filter Function Set Finset Lattice RG Wilson Bid Exterior Precision Tree Matrix
open Bloch Stationary Garf Pulse Spine Larch Origin PertExtension.Series MeasureTheory
open PertExtension.GaussianScore FreeResolvent PhysicalNext.RankCovariance
open PertExtension.Chart Kale Spark House Radial Ion
open scoped Topology ContDiff BigOperators Classical Matrix Matrix.Norms.Frobenius
variable {G:Gauge}{c f n:Side} {S:StepData c f} {X E α:Type}{k r:ℕ}
local notation "T" => planting S.ratio S.patch.odd_side
local notation "κ" => (AxisChart G T)
local notation "Ξ" => insertion (plant T (G:=G))
local notation "Λ" => Link G f
local notation "Δ" => Link G c
local notation "Ω" => House.Dir (Yard G S)
-- Character through telescope horizons downward specific slot
def sealedL (F:House (Lines G n 1))(k:ℕ) := ∀ i<k,GuardsL (wind F k i) (k-i)
structure PackageL (Y:ℝ→ Config G n→ℝ)(F:House (Lines G n 1))(k:ℕ): Prop where
    color t : GaugeInvariant (Y t)
    paid : Measurable (Function.uncurry Y)
    vest : AnalyticAt ℝ (fun p : cap G n=> Y p.1 (input G n p.2)) 0
    exact : Rays k ((fun p : cap G n=> Y p.1 (input G n p.2)) - swell F k)
def handL (F:House (Lines G n 1))(k:ℕ)(t:ℝ)(U:Config G n) := ∑ i∈Finset.range k, t^i * (fire (wind F k i)) U
lemma candlesL (F:House (Lines G n 1))(k:ℕ)(h: sealedL F k) : PackageL (handL F k) F k:= by
   let Φ i:= (fire (wind F k i)); have he i (hi:i<k): WedgeL (Φ i):=fireLife (h _ hi); let V i:= Φ i ∘ input G n
   refine ⟨fun t x u=>sum_congr rfl (fun i hi=>congr_arg (_*·) ((he i (mem_range.mp hi)).invariance x u)),?_ , stake_ana (F:=V) (fun i hi=>(he i hi).radiant),?_⟩
   · exact Finset.measurable_fun_sum _ fun i hi=> (measurable_fst.pow_const (by exact i)).mul (((he _ (mem_range.mp hi)).consent.measurable).comp measurable_snd)
   · change Rays k (Ion.stake V k - Ion.stake (wind F k) k); rw [show Ion.stake V k - Ion.stake (wind F k) k= Ion.stake (V-wind F k) k from (by ext1 x; simp [Ion.stake,conjunct, mul_sub,sum_sub_distrib])]; exact good_spaces (fun i hi=>(he i hi).radiant.sub ((h i hi).analytic)) fun i hi=> (firesL (h i hi)).2
variable {Y:ℝ→ Config G f→ℝ}{F:House (Lines G f 1)}{P: FreeResolvent.FaceRow}
lemma plan_mL (hQ:PackageL Y F k)(h:S.patch.Branches S.kernel G)(u:ChartRatio G)(hs:LocalRatio u): Measurable (tribute u S Y):= by
   apply Measurable.sub
   refine Measurable.add (hQ.paid.comp (measurable_fst.prodMk ((input_cont (m:=f) (G:=G)).measurable.comp ((teen S).continuous.measurable.comp measurable_snd)))) ?_
   · simp_rw [hot_spec]; unfold noiseTaylor; apply Measurable.mul measurable_const (Finset.measurable_fun_sum _ (fun i _=>?_)); exact (show Continuous G.price by fun_prop).measurable.comp (Measurable.mul ((measurable_pi_apply i).comp ((input_cont (m:=c) (G:=G)).measurable.comp ((mature S).continuous.measurable.comp measurable_snd))) (((measurable_pi_apply i).comp ((S.prediction_meas h (art S)).comp ((input_cont (G:=G)).measurable.comp ((teen S).continuous.measurable.comp measurable_snd)))).inv)) -- continuous names
   exact (measurable_fst.pow_const (2:ℕ)).mul ((gold_meas hs).comp measurable_snd)
-- pars analytic
local notation "ν" => (ℝ × Ω)
section
variable {Q:ChartRatio G}(hQ:PackageL Y F k)(h:S.patch.Branches S.kernel G)(hv:LocalRatio Q)
include hQ h hv
lemma tribute_anaL : AnalyticAt ℝ (tribute Q S Y) 0:= ((starts _ hQ.vest (ace S)).add (starts _ (hot_ana h) (ContinuousLinearMap.snd ℝ ℝ _))).sub (conjunct_ana (gold_ana (S:=S) hv) 2)
lemma tribute_jetL (r:ℕ)(hr:r<k)(x:ν) : jet (tribute Q S Y) r x=jet (swell F k) r (ace S x)+jet (hot S) r x.2 -if 2≤r then x.1^2*jet (gold Q) (r-2) x.2 else 0:= by
   let V : ν→ℝ := ((fun p:cap G f=> Y p.1 (input G f p.2)) ∘ ace S); let H := (hot S (G:=G)) ∘ (ContinuousLinearMap.snd ℝ ℝ Ω); have he : AnalyticAt ℝ V 0:= starts _ hQ.vest (ace S); have hy: AnalyticAt ℝ H 0:= starts _ (hot_ana h) _; change jet (V+H-conjunct (gold (S:=S) Q) 2) _ _=_; rw [jet_minus _ _ _ _ (he.add hy) (conjunct_ana (gold_ana hv) 2), serif he H hy, joint _ _ _ _ (gold_ana hv)]; congr 2
   · exact (woven hQ.vest _ _ _).trans (nightwalk hQ.vest (orchestra F k) hQ.exact _ hr _)
   exact woven (hot_ana h) _ _ _
lemma tribute_wantedL (hk:1<k) : Radial.Stationary (tribute Q S Y):= by
   have he:=tribute_anaL hQ h hv; have hs:= spectrum F k; have hp:= (torch_c (hot_ana h) (torch h)).1
   constructor
   · apply he.contDiffAt
   · have hz:= tribute_jetL hQ h hv 0 (by omega) 0; simpa [hp.base0,hs.base0] using hz
   intro u; rw [tribute_jetL hQ h hv 1 hk,hp.base1,hs.base1]; simp
lemma tribute_beamsL (hP:Chest F P)(hk:2<k)(x: ν) : jet (tribute Q S Y) 2 x=(teen S x.2) ⬝ᵥ (spindle G f P*ᵥ (teen S x.2))/2 + jet (hot S) 2 x.2:= by
   rw [tribute_jetL hQ h hv 2 hk, theme hP _ hk,if_pos le_rfl,Nat.sub_self,jet_zero,gold_zero,mul_zero,sub_zero]; rfl
end
local notation "ϕ" => (cap G c × κ)
section
variable {Q:ChartRatio G}(hQ:PackageL Y F k)(h:S.patch.Branches S.kernel G)
include hQ h
lemma seenL : SensorL (visitor S Y) S.ratio:= ⟨fun i v U V=> by rw [visitor, S.covary h,hQ.color]; rfl⟩
lemma visit_measL (x:ℝ)(p:Config G c): Measurable (fun U:Config G f=> visitor S Y x U p) := by
   let t :ℝ:= (x^2)⁻¹; have hf: Measurable (fun U:Config G f=> S.density t U p):= by
        let L:= fun v:Config G f=>(v,p); let τ(z:Config G f × Config G c):= S.density t z.1 z.2; change Measurable (τ ∘ L); apply (show Measurable τ from S.density_meas h t).comp (f:=L); exact measurable_id.prodMk (measurable_const (a:=p))
   have hy: Measurable (Y x):= hQ.paid.comp ( (measurable_const (a:=x)).prodMk measurable_id)
   exact (hf.const_mul _).mul (hy.neg.div_const _|>.exp)
lemma fosterL (hv:LocalRatio Q): Faces Q (runner (visitor S Y) T) ((tribute Q S Y) ∘ inked S) (jacobian (U:=(T).Free) Q 0):= by
  have hx:= gold_jac_0 (S:=S) hv; let W:=visitor S Y; refine ⟨hx,fun ⟨x,p⟩=> ?_,?_ ⟩
  · exact (visit_measL hQ h x (input G c p)).comp (Forest.continuous_drape T (G:=G)).measurable
  have he : Tendsto (fun p:ϕ=> input G f (stash S T p.2)) (𝓝 0) (𝓝 1):= by simpa using! (input_cont.comp ((stash S T).continuous.comp continuous_snd)).tendsto (0:ϕ)
  filter_upwards [he.eventually (ground_deduct h), (show Tendsto (fun p:ϕ=>p.2) (𝓝 0) (𝓝 0) from continuous_snd.continuousAt ).eventually (gold_chart (S:=S) hv)] with z hϕ hxg (ht:0< z.1.1)
  let t:= z.1.1; let b:= z.1.2; let y:=z.2; let p:= weave S (b,stash S T y); let U:=input G f (stash S T y); let V:= input G c b; let X:=jacobian Q y; let A:= jacobian Q (0:κ);
  have hk : (visitor S Y t U V)=Real.exp (-Y t U/t^2 - hot S p/t^2) := by
    unfold visitor; rw [hϕ V,←Real.exp_add]; congr 1; rw [hot_spec,(show mature S p=b from grow _),(show teen S p=stash S T y from blooms _)]; unfold V U; ring
  change X* W t ((T).drape _) V= _; rw [←stash_drape]; change X*visitor S Y t U V=A*Real.exp (-tribute Q S Y (inked S z)/t^2); rw [hk]; -- expose
  let J:=Y t U+hot S p-t^2*gold Q p; rw [show tribute Q S Y (inked S z)= J from ?_]; swap; · rw [show inked S z=_ from penPort z.1 z.2]; change Y t (input G f (teen S p)) + _-_ = _; rw [show teen S p=_ from blooms _]; rfl
  calc
    _ = (A*Real.exp (gold Q p))*Real.exp (-Y t U/t^2 - hot S p/t^2):= by rw [show Real.exp (gold Q p)=X/A from hxg b]; field_simp [(show A≠0 from hx.ne')]
    _ = _:= by rw [mul_assoc, ← Real.exp_add]; unfold J; change A*_=A*Real.exp (-(_-t^2* _)/t^2); congr 2; field_simp [(show t≠0 from ht.ne')]; ring
end
end YM.Contacts.Milling.Forge
namespace YM.Contacts.Milling.Forge
open Filter Function Set Finset Lattice RG Wilson Bid Exterior Precision Tree Matrix
open Bloch Stationary Garf Pulse Spine Larch Origin PertExtension.Series MeasureTheory
open PertExtension.GaussianScore FreeResolvent PhysicalNext.RankCovariance Pulse.Form
open PertExtension.Chart Kale Spark House Radial Ion
open scoped Topology ContDiff BigOperators Classical Matrix Matrix.Norms.Frobenius
variable {G:Gauge}{c f n:Side} {S:StepData c f} {X E α:Type}{k e r:ℕ}
local notation "T" => planting S.ratio S.patch.odd_side
local notation "κ" => (AxisChart G T)
local notation "Ξ" => insertion (plant T (G:=G))
local notation "Λ" => Link G f
local notation "Δ" => Link G c
local notation "ψ" => Yard G S
local notation "Ω" => House.Dir (Yard G S)
variable {Q: ChartRatio G}{F:House (Lines G f 1)} {Y:ℝ→ Config G f→ℝ}
lemma banners_inkL (x:Ω)(hQ:PackageL Y F k)(h:S.patch.Branches S.kernel G)(hu:LocalRatio Q){e:ℕ}(he:e+2<k): MvPolynomial.aeval x (PowerSeries.coeff e (clouds (banners G S Q F)))=Radial.layers (tribute Q S Y) e (1,x):= by
   rw [parcel]; by_cases ht:e=0; · subst e; simp [Radial.layers,banners,compote]
   unfold banners Radial.layers; simp_rw [parcel_bill x e ht,hoist_read,shaved,sum_add_distrib,sum_neg_distrib]; change _= -jet (tribute Q S Y) _ _+_; simp only [sum_ite_eq',sum_add_distrib, Finset.mem_range,if_pos (show e<e+3 from by omega), if_pos (show e+2<e+3 from by omega),tribute_jetL hQ h hu _ he,if_pos (show 2 ≤ e+2 from by omega),one_pow,one_mul,if_neg ht,Nat.add_sub_cancel]
   rw [show ace S (1,x)=(1,teen S x) from rfl, House.stamp F k e he,← hot_craft h,←gold_spec hu]; simp only [terrace,stage,map_sum, design]; ring_nf; rw [sub_right_comm]; congr!
variable {P H:FreeResolvent.FaceRow}{R: Astro G S}{d:ℝ}
lemma targetsL (Q : ChartRatio G){P H:FreeResolvent.FaceRow}{R: Astro G S}{d:ℝ}(hQ: PackageL Y F (k+3))(hP:Chest F P)(H_Q:LocalRatio Q)(h:Beam S G R P H d):
   Arc (court h) (fun v:cap G c=> (sky S G (atr G S R))*ᵥ v.2) (attendP S G) (banners G S Q F) ((tribute Q S Y) ∘ inked S) (swell (vault S Q F R P H) (k+3)) ((course S T R) ∘ Prod.snd) k {z:cap G c | z.1=1} := by
  let C:=court h; let a:=tribute Q S Y; let f:= a ∘ inked S; let p:= vault S Q F R P H; let y:=swell p (k+3); let M:=course S T R; let R':= atr G S R; have ha:= tribute_anaL hQ h.light.1 H_Q; let K:= sky S G R'; let g: cap G c→ κ :=M ∘ Prod.snd; let χ:=attendP S G; have hp: Chest p H:= vault_beams (Q:=Q) hP.toShaped
  constructor
  · refine ⟨fun x z=> ?_, M.continuous.comp continuous_snd⟩
    let w:= stash S T ((course S T R) x.2+z); let X:=weave S (x.2,w); change jet f 2 (_,M x.2+z)=jet y 2 x+ _; rw [show jet f 2 (x,M x.2+z) = jet a 2 (x.1,X) from woven ha (inked S) (x,M x.2+z) 2]; unfold a y; rw [tribute_beamsL hQ h.light.1 H_Q hP (by omega), theme hp _ (by omega)]; dsimp only; rw [spice X h.light.1]; have ht: w= R'*ᵥ x.2+ stash S T z:= by unfold w; rw [map_add,gather_flow h]
    erw [show teen S X=w from blooms _, show Garf.mature S X=x.2 from grow _,ht]; change _=_ +( (tribe S T z) ⬝ᵥ (_*ᵥ (tribe S T z)))/2; rw [← add_div,← add_div]; apply congr_arg (·/ (2:ℝ)) ((shift_physical h x.2 (tribe S T z)).trans (add_comm ..))
   -- identity apply shift
  · intro i hi x hx z; rw [mark]; let w:= weave S (x.2,stash S T (M x.2+z)); have hh: inked S (x,M x.2+z)=(1,w):= Prod.ext hx rfl
    change MvPolynomial.aeval (K *ᵥ x.2 + _) _=Radial.layers f i (x,M x.2+z); rw [show K*ᵥ x.2 + (fun i=> attendP S G i z)=w from ?_, banners_inkL w hQ h.light.1 H_Q (by omega)]; rotate_left
    · unfold w K M; rw [firesP,sky_pass,map_add,gather_flow h, ← map_add]; congr 2 <;> simp [R']
    unfold Radial.layers f; rw [woven ha,woven ha,hh]
  intro i hi x hx; rcases x with ⟨t,v⟩; change t=1 at hx; subst t; rw [veers h]; exact parcel_forward _ (sky S G (atr G S R)) v _ (banners G S Q F) (banner_snug hP.toShaped) (by omega)
lemma franchiseL (Hq:LocalRatio Q)(hQ:PackageL Y F (k+3))(hP:Chest F P)(h:Beam S G R P H d):
   Sight (runner (visitor S Y) T) (swell (vault S Q F R P H) (k+3)) (jacobian (U:=(T).Free) Q 0 * measureT (court h) (tangent G (T).Free)) k:= by
     have hs:= tribute_anaL hQ h.light.1 Hq; let μ:=tribute Q S Y; let g:= μ ∘ inked S; have ht:= tribute_wantedL hQ h.light.1 Hq (by omega); have hg: Radial.Stationary g:= ⟨(starts μ hs (inked S)).contDiffAt,(congr_arg μ ((inked S).map_zero)).trans ht.base0,fun i=> (woven hs (inked S) i 1).trans (ht.base1 _)⟩; exact shelterbelt Hq (fosterL hQ h.light.1 Hq) (targetsL Q hQ hP Hq h) hg ((plan_mL hQ h.light.1 Q Hq).comp (inked S).continuous.measurable) (spectrum ..) (banner_snug hP.toShaped)
lemma passportL (Hq:LocalRatio Q)(hi:sealedL F (k+3))(hP:Chest F P)(h:Beam S G R P H d) : sealedL (vault S Q F R P H) (k+3) :=
   wind_guardL _ T S.patch.odd_side (franchiseL Hq (candlesL F _ hi) hP h) (seenL (candlesL F _ hi) h.light.1)
end YM.Contacts.Milling.Forge
