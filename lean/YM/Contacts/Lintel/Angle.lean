import YM.Contacts.Lintel.Launch
import YM.AnalyticNext.CALENDAR_SCENE_ADAPTER.ThermalRule
namespace YM.Contacts.Lintel
set_option linter.unusedSectionVars false
set_option quotPrecheck false
open Function Set Finset Filter Metric RG Wilson Lattice Precision Exterior MeasureTheory
open Bloch Milling Milling.Steam Pulse Spine MergeProof Milling.Forge Laurent Stationary Matrix Work.F05
open Milling.Garf Form House PertExtension.Series Tree Larch FreeResolvent PhysicalNext.RankCovariance
open PertExtension.Chart Radial
open scoped Topology BigOperators Matrix Classical NNReal ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{c f m: Side}{α:ℕ→Type}{n k:ℕ}
namespace Angle
open Crag Wire AnalyticNext.CalendarScene Next.SectorChange Gaussian Lumen Ion Spark
variable {S:StepData c f}{P: Clip}{Z:PathData G}{m:Towers S.patch.L}{Ω: ChartRatio G}{w u v b A:ℝ}
local notation "B" => planting S.ratio S.patch.odd_side
local notation "E" => (Link G c)
local notation "κ" => AxisChart G (B)
variable {ρ:fieldDir G c 1→ AxisChart G (planting S.ratio S.patch.odd_side)}
variable (hZ:Z.Bounds P w u v) (hB:S.patch.Branches S.kernel G) (h:LocalRatio Ω) (hp:Critical (planting S.ratio S.patch.odd_side) P Z ρ) (hf: (PriceGap (planting S.ratio S.patch.odd_side) P Z b)) (hb:0<b)
     (hk: AnalyticAt ℝ (thermal (planting S.ratio S.patch.odd_side) (art S) P Z ρ Ω) 0)
def material (P:Clip)(Z:PathData G)(t:ℝ)(U:Config G f):ℝ:=mainTerm P Z U + t^2*Precision.loop Z U
def classS (P:Clip)(Z:PathData G) (ρ:fieldDir G c 1→ AxisChart G (planting S.ratio S.patch.odd_side)) (x:E):= tested (B) (art S) P Z (arm G c 1 x) (ρ (arm G c 1 x)) -- burn
-- not logging estimates
section
local notation "L" => (arm G c 1).toContinuousLinearMap
local notation "F" => (tested (B) (art S) P Z)
private abbrev Z₀ (ρ:fieldDir G c 1→ AxisChart G (planting S.ratio S.patch.odd_side)): E×κ→fieldDir G c 1 × κ:= fun x=> (L x.1,ρ (L x.1)+x.2)
include hp in
private lemma letterA : Z₀ (S:=S) ρ 0=0 ∧ AnalyticAt ℝ (Z₀ (S:=S) ρ) 0:= by
   let f:= (L).comp (ContinuousLinearMap.fst ℝ E κ); refine ⟨by simp only [Z₀, Prod.fst_zero,Prod.snd_zero,map_zero,hp.1, zero_add,Prod.mk_zero_zero],?_⟩; apply ContDiffAt.analyticAt; exact (f.contDiff.contDiffAt.prodMk (g:=fun x=>ρ (f x)+x.2) ((ContDiffAt.comp (g:=ρ) (f:=f) (0:E×κ) (by rw [map_zero];exact hp.2.1) f.contDiff.contDiffAt).add contDiffAt_snd)) -- syntax
private def Mi (P:Clip)(Z:PathData G)(ρ:fieldDir G c 1→ AxisChart G (planting S.ratio S.patch.odd_side))(x:E×κ):= tested (B) (art S) P Z (L x.1) ((Z₀ (S:=S) ρ x).2) - classS (S:=S) P Z ρ x.1 -- issue notation
private def Np (Ω:ChartRatio G)(Z:PathData G)(ρ:fieldDir G c 1→ AxisChart G (planting S.ratio S.patch.odd_side))(x:E×κ):= jacobian Ω ((Z₀ (S:=S) ρ x).2)* Real.exp (-AnalyticNext.CalendarScene.Pair.payload (S:=S) (B) Z (Z₀ (S:=S) ρ x))
include hp
local notation "M" => (Mi (S:=S) P Z ρ)
local notation "N" => (Np (S:=S) Ω Z ρ)
local notation "X" => (classS (S:=S) P Z ρ)
private lemma shape_cost : AnalyticAt ℝ (X:E→ℝ) 0:= by unfold classS; let Z (x:E):=Z₀ (S:=S) ρ (x,0); have he : AnalyticAt ℝ ((uncurry F) ∘ Z₀ (S:=S) ρ) 0:= AnalyticAt.comp (f:=Z₀ (S:=S) ρ) (x:=0) (by rw [(letterA hp).1];exact (hp.2.2 (art S)).1.analyticAt) (letterA hp).2; let K:=ContinuousLinearMap.inl ℝ E κ; apply AnalyticAt.congr (starts _ he K) (Eventually.of_forall fun x=>?_); dsimp [K,Z₀]; congr 1; exact add_zero _
omit hp in
private lemma shift_bend {V:Type}[NormedAddCommGroup V][NormedSpace ℝ V](f:V→ℝ)(u:V)(K:ℝ): bend (fun x=> f (u+x)-K) 0=Work.F05.bend f u:= by
    unfold Work.F05.bend; rw [show fderiv ℝ _ = (fun x=> fderiv ℝ f (u+x)) from funext (fun x=> by rw [fderiv_sub_const, fderiv_comp_add_left]),fderiv_comp_add_left,add_zero]
omit hp in
private lemma revolve (x:E): bend (fun y=> M (x,y)) 0=Work.F05.bend (F (L x)) (ρ (L x)):= by
   exact shift_bend (F (L x)) (ρ (L x)) (X x)
include hZ h
def rentV (S:StepData c f)(P:Clip)(Z:PathData G)(ρ:fieldDir G c 1→ AxisChart G (planting S.ratio S.patch.odd_side))(Ω:ChartRatio G) : Link G c→ℝ:= fun x=> thermal (planting S.ratio S.patch.odd_side) (art S) P Z ρ Ω ((arm G c 1).toContinuousLinearMap x)
include hf hb hk
omit hZ h hf hb hk in
private lemma homeM : AnalyticAt ℝ M 0:= by
    let W:= Z₀ (S:=S) ρ; let K:=X; have hs:= shape_cost hp; have hW:= letterA hp; have hm:AnalyticAt ℝ ((uncurry F) ∘ W) 0:= AnalyticAt.comp (f:=W) (g:=uncurry F) (x:=0) (by rw [show W 0=0 from hW.1]; exact (hp.2.2 (art S)).1.analyticAt) hW.2
    let U:= ContinuousLinearMap.fst ℝ E κ; change AnalyticAt ℝ ((uncurry F) ∘ W - K ∘ U) 0; exact hm.sub (Forge.starts K hs U)
omit hZ h hf hb hk in
private lemma homeZ : ∀ᶠ x:E in 𝓝 0,M (x,0)=0 ∧ fderiv ℝ (fun y=>M (x,y)) 0=0:= by
    have hy: ∀ᶠ x:E in 𝓝 0,fderiv ℝ (F (L x)) (ρ (L x))=0:= ((show Tendsto L (𝓝 0) (𝓝 0) from (by simpa using (L).continuous.tendsto (0:E))).eventually (((hp.2.2 (art S)).2).mono fun i he=>he.fderiv))
    have hu : ∀ᶠ x:E in 𝓝 0,M (x,0)=0 ∧ fderiv ℝ (fun y=>M (x,y)) 0=0:= by
       refine hy.mono fun x hh=>?_; constructor; · unfold Mi Z₀ classS; simp
       change fderiv ℝ (fun y=> F (L x) (ρ (L x)+y) -X x) 0=0; erw [fderiv_sub_const, fderiv_comp_add_left, add_zero]; exact hh
    exact hu
omit hZ h hk in
private lemma homeGap : ∃ b:ℝ,0<b∧∀ v,b*‖v‖^2≤radial M (0,v):= by
    let g:=fun y:κ=>M (0,y); have hD(y:κ)(h':y≠0): 0 < jet g 2 y:= by
       unfold Radial.jet; apply mul_pos (by positivity) ?_; rw [show (fun _:Fin 2=> y)=![y,y] from funext fun i=>by fin_cases i<;>rfl,← Work.F05.bend_apply]; unfold g; rw [revolve (x:=(0:E)), map_zero,hp.1]; exact Work.F05.tested_diag hb hf (art S) y h'
    exact Radial.quadratic_min g hD
omit hf hb hk in
private lemma homeN : AnalyticAt ℝ N 0:= by
       have hW:= letterA hp
       unfold Np; let R:=Z₀ (S:=S) ρ;
       have hs : ContDiffAt ℝ ω (fun x:E×κ=> jacobian Ω (R x).2) 0:= ContDiffAt.comp (g:=jacobian Ω) (f:=Prod.snd ∘ R) _ (by rw [Function.comp_apply, show R 0=0 from hW.1]; exact PertExtension.Chart.Ratio.jacobian_smooth h) (contDiffAt_snd.comp (f:=R) _ hW.2.contDiffAt)
       exact ContDiffAt.analyticAt (hs.mul ((ContDiffAt.comp (f:=R) (g:=AnalyticNext.CalendarScene.Pair.payload (S:=S) (B) Z) 0 (by rw [show R 0=0 from hW.1]; exact AnalyticNext.CalendarScene.payload_smooth hZ) hW.2.contDiffAt).neg.exp))
private lemma tides (hS:Rays 2 X): Tide X (rentV S P Z ρ Ω) M N:= ⟨shape_cost hp, starts _ hk (L), homeN hZ h hp, homeM hp,hS,homeZ hp,homeGap hp hf hb⟩
private lemma mountain (hS:Rays 2 X) :
   ∀ᶠ x:E in 𝓝 0,N (x,0)*(∫ y,Real.exp (-radial M (x,y)) ∂tangent G (B).Free)= Ω.scale^(Fintype.card (B).Free) * dome (Key (B) G)* Real.exp (- rentV (ρ:=ρ) (S:=S) (P:=P) (Z:=Z) (Ω:=Ω) x):= by -- rentV implicit parameters issue include
    obtain ⟨b',hb',H⟩:= (tides hZ h hp hf hb hk hS).rise;
    let hm:=homeM hp; let D:= Ω.scale^Fintype.card (B).Free; have hv:0 < D:= pow_pos h.scale _
    have hl(x:E): bunch (B) G M x=hessian (B) (art S) P Z (L x) (ρ (L x)):= by rw [bunch,revolve,hessian_eq] -- speed
    have hψ: Tendsto (ρ ∘ L) (𝓝 0) (𝓝 0):= by have he:= hp.2.1.continuousAt.tendsto; rw [hp.1] at he; exact he.comp (by simpa using (L).continuous.tendsto (0:E))
    filter_upwards [breath_pay (S:=M) hb' H hm,hψ.eventually (Metric.ball_mem_nhds _ h.patch)] with x hd hx;
    rw [hd.2,hl]; let t:= ρ (L x); let v:=∏ i : (B).Free, Ω.J (t i); let c:=Gaussian.dome (Key (B) G); let z:= Precision.loop Z (lifting (B) (represent (L x)) t); let p:= hessian (B) (art S) P Z (L x) t;
    have hp (i:(B).Free):0<Ω.J (t i):= h.pos _ (by change t ∈ ball 0 Ω.radius at hx; rw [ball_pi _ h.patch] at hx; exact hx i (Set.mem_univ i)); have he: 0<v:= Finset.prod_pos (fun i _=> hp i); have hu: jacobian Ω t=D*v:= by unfold jacobian; simp_rw [PertExtension.Chart.fee, fun i:(B).Free=>max_eq_left (mul_pos h.scale (hp i)).le, Finset.prod_mul_distrib, Finset.prod_const,Finset.card_univ]; rfl
    unfold Np; erw [show Z₀ (S:=S) ρ (x,0)= (L x,t) from Prod.ext rfl (add_zero _)]; change jacobian Ω t*Real.exp (-z)*(c*Real.exp (-Real.log p.det/2))= D*c*Real.exp (-(z + _-Real.log v)); rw [hu, show -(z+1/2*Real.log p.det-Real.log v)= -z +(-(Real.log p.det)/2+Real.log v) by ring,Real.exp_add,Real.exp_add,Real.exp_log he]; ring
variable {U:House (Lines G f 1)} (hU:Forge.Package (n:=f) (material (G:=G) P Z) U 5)
include hU hB
local notation "BV" => runner (Forge.visitor S (material (G:=G) P Z)) (B)
omit hZ hf hb hk in
private lemma drawing : Draws (tangent G (B).Free) X M N BV:= by
   let T (x:E):= input G c x; let g (x:E):= ρ (L x); let k(x:E)(i:(B).Free):= replica S.ratio (T x) i.val; have he: Tendsto g (𝓝 0) (𝓝 0):= by have he:= hp.2.1.continuousAt.tendsto; rw [hp.1] at he; exact he.comp (by simpa using (L).continuous.tendsto (0:E));
   have hy: Tendsto k (𝓝 0) (𝓝 1):= tendsto_pi_nhds.mpr fun i=> by unfold k replica; split; exact tendsto_const_nhds; simpa only [Function.comp_def,Pi.one_apply] using ((continuous_apply _).tendsto (1:Config G c)).comp (show Tendsto T (𝓝 0) (𝓝 1) from (by simpa [T] using! ((input_cont (G:=G) (m:=c)).tendsto (0:E)))) -- output
   refine receipt (S:=N) h he hy (fun ⟨x,U⟩=> (Forge.visit_meas hU hB x (T U)).comp (Forest.continuous_drape (planting S.ratio S.patch.odd_side)).measurable) ?_; let f(y:E×κ):= lifting (B) (T y.1) (g y.1+y.2); let L':= Z₀ (S:=S) ρ; have hw:= letterA hp; have hF : Tendsto f (𝓝 0) (𝓝 1) := by
      apply ( (show Tendsto (fun y: fieldDir G c 1 × κ=> lifting (B) (represent y.1) y.2) (𝓝 0) (𝓝 1) from (by simpa using! ((Work.F04.lifting_cont (S:=S) (B) (G:=G)).tendsto 0))).comp (f:=L') _); exact hw.1 ▸ hw.2.continuousAt.tendsto
   filter_upwards [hF.eventually (ground_deduct hB)] with y hr t ht; let W:=f y; let η:=T y.1; let q:=noiseTaylor S η W (art S); let γ:=Precision.loop Z W; let β:=mainTerm P Z W; have hx : (BV) (t,y.1) (expLinks G (B).Free (g y.1+y.2) * k y.1)=visitor S (material P Z) t W η:= rfl
   rw [hx,Forge.visitor,hr]; let d':=jacobian Ω (g y.1+y.2); change d'* (Real.exp (-(t^2)⁻¹ * q)*Real.exp (-(β+t^2*γ)/_))= (d'*Real.exp (-γ))*Real.exp (-(_+_)/_); set v:= (X : E→ℝ) y.1; change _= _*Real.exp (-(v+(β+q-v))/_); rw [mul_assoc d',←Real.exp_add,←Real.exp_add]; congr 2; field_simp; ring
-- chain to gauge-invariant formal step.
theorem classical_ray {R:Astro G S}{H Q: Bed}{d:ℝ} (hz:Beam S G R H.metric Q.metric d) (hS:Rays 2 X) (hF:Chest U H.metric): let T:= Forge.vault S Ω U R H.metric Q.metric; Rays 5 (margin ((swell T 5)- score X (rentV S P Z ρ Ω))) := by
    intro T; let Y:=swell T 5; have hv:=orchestra T 5; have hs : Sight (BV) Y _ 2:= franchise h hU hF hz; exact quota _ (tides hZ h hp hf hb hk hS) (mountain hZ h hp hf hb hk hS) hv (rays_cast hv (spectrum T _)) (drawing hB h hp hU) hs
end
end Angle
end
end YM.Contacts.Lintel
