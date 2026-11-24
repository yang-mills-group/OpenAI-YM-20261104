import YM.MS.Wilson.Gauge
import YM.Wilson.Law
/-!
# Frame energy exactly Wilson's counting action

Signed coordinate pull later uses original Wilson symmetric lemma. Landau
 Plan master includes locals in log. Keep separately actual analytic stencils
 via four-argument price function. Gauge invariance of any analytic local LW
 radius ensures Focus.Inert.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Native.Chart
open Function Filter Finset Set Plane Koszul Cylinder Taylor Bare Focus Lattice
open scoped Topology ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:Type}

abbrev Rout (P:Type) := P×PlaqAxes
def nation (a:City G P) : Edge P→ G.El:= G.lieExp ∘ a
def atCart (U:Axis→G.El):= U 0*U 1*(U 2)⁻¹*(U 3)⁻¹
def gone (b: Lot G Axis): ℝ:= -(G.price (atCart (G.lieExp ∘ b)))

lemma well_paid {Z:Type}[NormedAddCommGroup Z][NormedSpace ℝ Z] {F:Z→ G.El} (h:germ (G.mat ∘ F)): germ (G.price ∘ F) := by unfold Gauge.price; exact contDiffAt_const.sub (((Complex.reCLM.contDiff.contDiffAt).comp 0 ((((Matrix.traceLinearMap _ ℂ ℂ).restrictScalars ℝ).toContinuousLinearMap.contDiff.contDiffAt).comp 0 h)).div_const _)
lemma bill_gone : germ (gone (G:=G)):= by
   let E := Maurer.lie G; let F i (b:Lot G Axis) := E (b i); let A (b:Lot G Axis) := atCart (G.lieExp ∘ b)
   have he i : germ (F i):= G.exp_jet.contDiffAt.comp (f:=fun x:Lot G Axis=>x i) 0 (contDiff_apply ..|>.contDiffAt)
   let V i:=fun b=>star (F i b); let W : G.Mat≃L[ℝ] G.Mat:=starL ℝ; have hv i : germ (V i):= W.contDiff.contDiffAt.comp (f:=F i) 0 (he i)
   have hh: G.mat ∘ A= fun b=>F 0 b* F 1 b*V 2 b*V 3 b:= funext fun b=> by simp only [A,Function.comp_apply,atCart,G.mat_mul,G.mat_inv]; rfl
   change germ (-(G.price ∘ A)); have ht : germ (G.mat∘ A):= by rw [hh]; exact (((he 0).mul (he 1)).mul (hv 2)).mul (hv 3)
   exact (well_paid ht).neg

variable [AddCommGroup P]
def loadC (d:Rail P)(k:Rout P): Axis→Edge P:= ![(k.1,k.2.val.1), (k.1+d k.2.val.1,k.2.val.2), (k.1+d k.2.val.2,k.2.val.1), (k.1,k.2.val.2)]
-- gauge with old right orientation (links in path relative x→ x+d). Includes identity convention compatible at A=1 variables
variable (d:Rail P)
def siteGauge (d:Rail P)(g:P→G.El)(U: Edge P→G.El): Edge P→G.El:= fun e=> (g e.1)⁻¹*U e*g (endRail d e)
def steering (u: Eyes G P) [DecidableEq P](t:ℝ): P→ G.El:= fun x=> G.lieExp (t • priv u x) -- binder

-- extends to empty stencils
abbrev OpenGauge (f:(Edge P→G.El)→ℝ): Prop:= ∀ g U, f (siteGauge d g U) = f U
lemma class_cart (k:Rout P) (g:P→G.El)(U: Edge P→G.El) : atCart (siteGauge d g U ∘ loadC d k)= (g k.1)⁻¹* atCart (U ∘ loadC d k)*g k.1:= by
   simp [atCart,siteGauge,endRail,loadC,mul_assoc]; rw [add_right_comm k.1]; group
lemma gone_gauge (k:Rout P): OpenGauge (G:=G) d (fun U=> -(G.price (atCart (U ∘ loadC d k)))):= fun g U=> by dsimp only; rw [class_cart]; simpa using congr_arg Neg.neg (G.price_conj (g k.1)⁻¹ (atCart (U ∘ loadC d k)))

variable [Fintype P]
def rent (d:Rail P)(b:City G P): ℝ:=∑ k:Rout P, gone (b ∘ loadC d k)
lemma rent_s : germ (rent (G:=G) d) := ContDiffAt.sum fun i _=>bill_gone.comp (f:=fun a:City G P=>a ∘ loadC d i) 0 (contDiffAt_pi.mpr fun _=> contDiff_apply ..|>.contDiffAt)
variable [DecidableEq P]
omit [Fintype P] in
lemma steering_here (u:Eyes G P)(t:ℝ)(e:Edge P)(a:City G P): siteGauge d (steering u t) (nation a) e=Maurer.step (route d e (priv u)) (a e) t:= by unfold Maurer.step steering siteGauge nation; simp_rw [Next.SectorChange.exp_negative]; rfl
-- trajectory in log of those actual rotations. equality for tiny t only.
def hover (u:Eyes G P)(a:City G P)(t:ℝ): City G P:=fun e=> G.plog (G.mat (siteGauge d (steering u t) (nation a) e))
lemma hover_stay (u:Eyes G P)(a :City G P){s:Set G.Color} {U:Set G.El} (h:LocalH.Geom G U s)(he:∀ i,a i∈s):
    hover d u a 0=a ∧ HasDerivAt (hover d u a) (loco d u a) 0 ∧ (∀ᶠ t:ℝ in 𝓝 0,nation (hover d u a t)=siteGauge d (steering u t) (nation a)) := by
    unfold hover; simp_rw [steering_here]; refine ⟨funext (fun e=> ?_), hasDerivAt_pi.mpr (fun i=> Maurer.amp _ h (he i)),?_⟩
    · rw [Maurer.step_start]; exact Maurer.snap_on h (he e)
    filter_upwards [eventually_all.mpr (fun i:Edge P=> Maurer.walk_on (route d i (priv u)) h (he i))] with t ht; funext i; rw [steering_here]; exact h.2.2.2.1 (ht i)
lemma confine {f:(Edge P→ G.El)→ℝ}(hx: OpenGauge d f) (h:germ (f ∘ nation)): Inert (loco d) (f ∘ nation):= by
    intro i; obtain ⟨r,hr,H⟩:=LocalH.geom_patch G
    filter_upwards [h.eventually (by simp),eventually_all.mpr (fun e:Edge P=> (continuous_apply e|>.tendsto (0:City G P)).eventually (Metric.ball_mem_nhds (0:G.Color) hr))] with a ha hv
    obtain ⟨he,hh,hg⟩:= hover_stay d i a (H r (le_refl r)) hv
    have ht : HasDerivAt ((f ∘ nation) ∘ hover d i a) (fderiv ℝ (f ∘ nation) a (loco d i a)) 0:= HasFDerivAt.comp_hasDerivAt_of_eq 0 (ha.differentiableAt (by simp) |>.hasFDerivAt) hh he.symm
    exact ((ht.congr_of_eventuallyEq (f₁:=fun _=> f (nation a)) (hg.mono fun t ht=> by dsimp only [Function.comp_apply]; rw [ht,hx])).unique (hasDerivAt_const ..))
lemma rentGauge : Inert (loco d) (rent (G:=G) d):= by
    let F U:=∑ k:Rout P, -(G.price (atCart (U ∘ loadC d k))); refine confine d (f:=F) ?_ (rent_s d)
    exact fun g U=> Finset.sum_congr rfl (fun i _=> gone_gauge d i g U)
end YM.MS.Native.Chart

namespace YM.MS.Native.Chart
open Function Filter Finset Set Plane Koszul Cylinder Taylor Bare Focus Lattice
variable {G:Gauge} {n:Side} (U:Wilson.Config G n) (a:City G (Site n))
def drive (n:Side): Rail (Site n):= Lattice.step
-- Origin. This is an exact identification using Wilson symbols with dimensions. Need plaquette lemma for rotation.
lemma plaza (p:Rout (Site n)): atCart (U ∘ loadC (drive n) p)= faceValue U p:= by
    unfold faceValue atCart drive loadC travel square; simp [travel,Lattice.Step.vec,mul_assoc]; rw [add_right_comm p.1]; simp [sub_eq_add_neg,posDir,negDir]
lemma original_W : rent (drive n) a= -Wilson.energy (nation a):= by unfold rent Wilson.energy; rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun i _=> congr_arg (fun u=> -G.price u) (plaza (nation a) i))
-- invariant of lattice old standard gauge sign
lemma when_invariant {f: Wilson.Config G n→ℝ}(h:Lattice.GaugeInvariant f): OpenGauge (drive n) f:=fun g U=> by
    rw [show siteGauge (drive n) g U=Lattice.gauge (fun x=>(g x)⁻¹) U from funext fun x=> by simp [siteGauge,Lattice.gauge,endRail,drive]]; exact h ..
end YM.MS.Native.Chart
