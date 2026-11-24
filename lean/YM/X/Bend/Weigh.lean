import YM.X.Bend.Flirt
/-!
# invariant functional parameter.Beacon light subtract. finite-only twists. remaining pp solved by analytic coord tilt when Kar approved.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Bend
open Maxwell Set Function MeasureTheory Lattice Wilson Next.Rank Labels Pert.Position
open Maxwell.Free Filter Metric Chir Sage Tri Ribbon Extra.FD Jet
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{F:Labels.Frames G} {d k m n:ℕ} {q:ℕ+} {V I:Type*} {r R:ℝ}
local notation "K"=>(atTop:Filter ℕ)
local notation "T"=>Fin 3
local notation "W"=>Bank F 6
local notation "G₀"=>pureBank F 6
variable (B:Bare.Shop F) (hq:1<q.val)(hg:G.Simple)
structure Booth (r:ℝ)(F:Frames G) where
    r1 : 4096 ≤ r
    normalC:ℝ
    valid : normalC<0
/-- eligible at fixed q.F.MScheme, Color. chooses numerical tangent by separated-position continuation. -/
def BeaconTest (x:Booth r F): Prop:= firstX B q hq hg 6 3 (mainT r x.r1) (beaconLabels F (Nat.le_refl 6))=Complex.ofReal x.normalC
lemma raised : ∃ (r:ℝ)(x:Booth r F), Avoid q r ∧ BeaconTest B hq hg x:= by
    obtain ⟨r,hr,h⟩:= region_power hq; obtain ⟨c,hc,k⟩:=unitSight B hq hg r hr h; exact ⟨_,⟨hr,c,hc⟩,h,k⟩
variable (t:Booth r F)
set_option quotPrecheck false
local notation "Φ"=> Board7 F t.r1 -- quotPre projection
abbrev haze (a:ℕ→ℝ): Word ℝ:=a- just (a 0)
def metricT (x:Booth r F)(w:Word (Bank F 6)) : Word ℝ := (x.normalC)⁻¹ • haze (Complex.re ∘ Wanted x.r1 w)
lemma metric_zero (w:Word W): light (metricT t w):= by simp [metricT,haze,just,light]
lemma ren_Wanted (v:Word ℝ)(w:Word W) (h:light v): Wanted t.r1 (ren v w)= ren v (Wanted t.r1 w):= by unfold Wanted; rw [ren_writes (Board7 ..),run_ren _ _ h rank_smooth.contDiffAt] -- projection order
lemma meter_ren (v:Word ℝ)(w:Word W)(h:light v): metricT t (ren v w)= ren v (metricT t w):= by
    let f:=Complex.reCLM.toLinearMap; let u:= Wanted t.r1 w; have ht:f ∘ ren v u=ren v (f ∘ u):= ren_writes f ..; unfold metricT; rw [ren_Wanted t v w h]; change _ • haze (f ∘ ren v u) =ren v (_ • haze (f ∘ u)); rw [ht]; unfold haze; rw [Jet.ren_light h];
    let a:=just ((f ∘ u) 0); let F:= f ∘ u; have he (r:ℝ)(b:Word ℝ): ren v (r • b)=r • ren v b:= (ren_writes (r • LinearMap.id (R:=ℝ) (M:=ℝ)) v b).symm
    change _ • (ren v F - a)= ren v (_ • (F-a)); have hg: F-a=F+(-1:ℝ) • a:= by rw [neg_one_smul,←sub_eq_add_neg]
    rw [hg,he,ren_add,he,show ren v a= _ from ren_static _ h,neg_one_smul,←sub_eq_add_neg]

lemma Ψcalibrated (w:Word W)(h:Genuine (metricT t w)): metricT t (ren (Jet.inverse (metricT t w)) w)=headway:= by rw [meter_ren _ _ _ (Jet.lives _), guarded h]
local notation "γ"=> par F 6
-- sign under ordered Beacon/Powers
lemma wants_t (w: Bank F 6): wants t.r1 (pulls γ w)= - wants t.r1 w:= by
   have he(i:Tea): Φ (pulls γ w) i= billSign i • Φ w i:= dark t.r1 w i; unfold wants rankT; simp_rw [he]; rw [show billSign 0= -1 from rfl, show billSign 1= -1 from rfl, show billSign 2=1 from rfl, show billSign 3=1 from rfl,show billSign 4= -1 from rfl,show billSign 5= -1 from rfl, show billSign 6=1 from rfl]; simp only [one_smul,neg_one_smul]; ring
lemma wants_odd (w:ℕ→Bank F 6)(h:pulls γ ∘ w=turn w): turn (Wanted t.r1 w) = -Wanted t.r1 w:= by
    funext i; let a:=Wanted t.r1 w; let f:= delay w i; have he:= part_frame t.r1 f w (appears_delay w i); let u:= wants (F:=F) t.r1; have ht : (fun x:ℝ=>u (f (-x)))= fun x=>-u (f x):= by ext1 x; unfold f; rw [←delay_turn, ← h, ← delay_map]; exact wants_t t _
    have hx : Act i (fun x=>u (f (-x))) (turn a):= he.reflects; rw [ht] at hx; refine hx.trans_at (show Act i (fun x=>-u (f x)) (-a) from ?_) le_rfl -- annotate
    simpa using! he.smul (-1)
lemma meter_odd (w:Word W)(h:pulls γ ∘ w=turn w): turn (metricT t w)= - metricT t w:= by
    funext i; have hv:=congr_fun (wants_odd t w h) i; let f:= Wanted t.r1 w i; change (-1:ℝ)^i • f = -f at hv; apply_fun Complex.reCLM at hv; rw [map_smul,map_neg] at hv; let p:=metricT t w; rcases eq_or_ne i 0 with h'|h'; · subst i; simp only [turn_zero, Pi.neg_apply,show metricT t w 0=0 from metric_zero ..,neg_zero]
    have hh: p i=t.normalC⁻¹ • f.re:= by unfold p metricT haze f; simp [just,h']
    change (-1:ℝ)^i • (p i)= -(p i); rw [hh,smul_comm, show (-1:ℝ)^i • (f.re)= -f.re from hv, smul_neg]
-- stable T coupling evaluation at uncut diagrams
variable (hw:BeaconTest B hq hg t)
local notation "M"=> mainT r t.r1
local notation "τ'"=> beaconLabels F (Nat.le_refl 6)
local notation "κ"=> metricT t
include hw
lemma standing_tip(w: Word (Bank F 6)) (hv:w 0=pureBank F 6)(hx: w 1=firstX B q hq hg 6): metricT t w 1=1:= by
   have h: t.normalC≠0:=t.valid.ne
   unfold metricT haze; simp only [Pi.smul_apply,Pi.sub_apply, Function.comp_apply,G₁moment t.r1 B hq hg w hv,hx,just, if_neg Nat.one_ne_zero,sub_zero, smul_eq_mul]; rw [show (firstX B q hq hg 6) 3 M τ'=_ from hw,Complex.ofReal_re,inv_mul_cancel₀ h] -- shadow w not included? fix
lemma meter_tip : Tendsto (fun k=>metricT t (B.uncut hg q k 6) 1) K (𝓝 1):= by
    let u(k):=B.uncut hg q k 6; let U(k i:ℕ):= Board7 F t.r1 (u k i); have H:Tendsto (fun k:ℕ=>U k 0) atTop (𝓝 0):= by rw [← board_m t.r1 B hq]; apply tendsto_pi_nhds.mpr;intro i;exact full_stick B hq hg _
    let P:= (firstX B q hq hg 6); have H':Tendsto (fun k:ℕ=>U k 1) atTop (𝓝 (Board7 F t.r1 P)):= tendsto_pi_nhds.mpr fun i=>limit₁ B q hq hg _
    let f(o:Clique×Clique):ℝ := t.normalC⁻¹ * (fderiv ℝ rankT o.1 o.2).re; have hu(a:Word (Bank F 6)): metricT t a 1= f (Board7 F t.r1 (a 0), Board7 F t.r1 (a 1)):=by unfold metricT Wanted haze; simp_rw [Pi.smul_apply, Pi.sub_apply,just,if_neg Nat.one_ne_zero, comp_apply]; rw [flow_tip _ _ (rank_smooth.differentiable (by simp) _)];simp [f]
    have hv:Continuous f:=continuous_const.mul (Complex.continuous_re.comp (((rank_smooth.continuous_fderiv (by simp)).comp continuous_fst).clm_apply continuous_snd)); have ht:= (hv.continuousAt (x:=((0:Clique),Board7 F t.r1 P))).tendsto.comp (H.prodMk_nhds H'); simp_rw [hu]; rw [show (1:ℝ)= f (0,Board7 F t.r1 P) from ?_]; exact ht; unfold f; rw [rank_entry]; change 1=_*((Board7 F _ P 0).re); rw [show Board7 F t.r1 P 0=t.normalC from hw,Complex.ofReal_re,inv_mul_cancel₀ t.valid.ne]
end YM.PositionX.Bend
