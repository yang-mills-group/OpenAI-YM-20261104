import YM.AllOrder.Wheel.Egress
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Wheel
open Function Filter Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid Planned.JetPort
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration Catch Catch.Clock Floe StateE Pace Plateau
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G: Gauge}{L n f : Side}{ι:Type*}{T:Clock ι} {K:KernelChoices}{P:Patch}{σ C b a D η κ:ℝ}{k l p j M:ℕ}
open ConnectedActivityE6.Coat Shellac Work.G05
variable (S:Stage) (R:ι→PathData G) (hG:G.Simple) {n:ι→Side} {f Λ a' b':ι→ℝ} {U:ι→ Age→ℕ} (h:∀ᶠ i in T.rail,(R i).Bounds S.clip S.width S.paths (Λ i))
    (x: ∀ i,Apex (n i) G) {β:ι→ℝ} (ht:Epoch T β) (hp:T.Meter Λ 0) (hq:T.Meter (fun i=> (Fintype.card (Primary (n i) G):ℝ)) 0) (ha:T.Meter f (-(1/2)))(hv:∀ᶠ i in T.rail,0<f i ∧ ‖x i‖≤ f i)(hj:k+3 ≤ j)
local notation "A"=> T.Meter
local notation "V"=> fun i=> Apex (n i) G
local notation "H"=> (fun i=> (f i)⁻¹)
local notation "u"=>fun i=> gStep (β i)
local notation "M'"=> fun i=> staff S.clip (R i) (n i)
local notation "Q"=> fun (i:ι)=> BareRates.pre G S.width S.paths j
local notation "L"=> fun i=> Precision.loop (R i) ∘ Desk.night (c:=n i)
local notation "F'"=> Shellac.off
local notation "τ"=> Estate («V»:=V) T j k (H) u x
variable (Q':ι→ Coin)(hQ:Hall T k β Q')
-- 
-- `off` only. aff compensation next.Q stamp independent θ.`now`.Age power analytic.Need caps.
structure Mosaic (T:Clock ι)(k:ℕ)(K0:ι → Floe.Layout G):Prop where
   desc (v:Age)(hk:v∈ Age.scope k): Atlas v (fun i=> K0 i v) T
include hG hq ha hv hj hQ
lemma keeper (hc:Civil S T R): τ (fun i=> now (Q' i) k (β i) • staff S.clip (R i) (n i) + Precision.loop (R i) ∘ Desk.night (c:=n i)) (fun i=> adjective (shiftB (Q' i) S.clip (R i)) (n i) (β i)):= by
 obtain ⟨hz,he⟩:= Civil.footprint j S R hG x hQ.tune hq ha hv hj hc ; have ht:= hz.spin (Civil.firstC j S R hG x hQ.tune hq ha hv hj hc) hQ.tune.stepI hQ.logic (hv.mono fun _ hi=> inv_nonneg.mpr hi.1.le); apply ((hz.pair he).pair ht).cong;
 · refine Eventually.of_forall fun i=>?_ ; apply congr_arg F'; ext1 v; simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]; unfold now; ring
 intro j hj; apply Eventually.of_forall; intro i; unfold adjective forming shiftB; ext1 x; simp only [Pi.add_apply,Pi.smul_apply,Finset.sum_apply]; rw [weighs]; simp_rw [Finset.sum_apply,Pi.smul_apply]
local notation "E'"=>Age.scope k
omit hG
variable (V':ι→ Floe.Layout G)(hV: Mosaic T k V')
include hV
abbrev render (k:ℕ)(K0:Floe.Layout G)(b:ℝ)(n:Side) := ∑ i∈Age.scope k, (ratioW (gStep b) i.e i.r) • Extra.Iteration.action (K0 i) (n:=n)
local notation "b0"=> fun i=> now (Q' i) k (β i)
lemma extras : τ (fun i=> render k (V' i) (b0 i) (n i) ∘ Desk.night) (fun i=> adjective (glory (Q' i) (V' i) (E')) (n i) (β i)):= by
 let f (w:Age)i:= ratioW (gStep (b0 i)) w.e w.r • speak (V' i w) (n i); let g (w:Age)i:= adjective (moiety (Q' i) w (V' i)) (n i) (β i); have hU := hQ.tune; have he (w)(hw:w∈E'): τ (f w) (g w):= by
    let a' i:= (1+wag (Q' i) k (β i))^(elapsed w); have hu:= hV.desc w hw; unfold g; let hp:w.e≤k:=Age.in_scope.mp hw; let hv':= Atlas.setup x hU hq ha hv hj w (fun i=>V' i w) hu hp; refine Estate.cong (hv'.spin ((Atlas.fare_v x hU hq ha hv hj w _ hu hp).weak (by unfold graded; linarith [Nat.cast_nonneg (α:=ℝ) w.e])) hU.stepI (hQ.cellar w) (hv.mono fun _ hi=> inv_nonneg.mpr hi.1.le)) ?_ ?_; · filter_upwards [Hall.tissue hQ w] with i h'; unfold f; rw [h',smul_smul];
    intro k _; refine Eventually.of_forall fun i=>?_ ; ext1 x; unfold adjective forming moiety; simp [weighs,Finset.sum_apply]
 apply (Estate.total (E') he (hv.mono fun _ hi=> inv_nonneg.mpr hi.1.le)).cong; · refine Eventually.of_forall fun i=>?_ ; apply congr_arg F'; ext1 x; simp only [Finset.sum_apply, Function.comp_apply,render,f,Pi.smul_apply]; rfl
 intro j hj; refine Eventually.of_forall fun i=>?_ ; ext1 x; simp_rw [Finset.sum_apply]; unfold g adjective Pace.glory; simp_rw [Finset.sum_apply] -- defeq
-- Render crop normalized coefficients
open Till
abbrev spell (k:ℕ)(V_:Floe.Layout G)(U:ℝ)(w:ℕ)(n:Side): Config G n→ℝ:= ∑ i:Site n, Tilt.patch G w n i (Age.scope k) V_ (gStep U)
def View (T:Clock ι)(r:ι→ℕ): Prop:=∀ C:ℝ,0<C→∀ e:ℝ,T.Meter (fun i=> Real.exp (-C*r i)) e
variable (m:ι→ℕ)(hm:View T m)(hw:∀ᶠ i in T.rail,4*(k+2)≤ m i)
omit hV hQ
variable {η : ℝ}
include hm
lemma slipsX (z:Age) {s:ι→Packet G z.r}(hu:Atlas z s T) : Catch.Cover T j η H (fun i=> F' (speak (s i) (n i)-speak (legible (s i) (m i)) (n i))) x:= by
 obtain ⟨σ,Λ,v,hp,hU⟩:= hu.pays; let L' i:= Real.exp (-(σ/2)*m i)*Λ i; let U(a:ι)(s' s₀:Packet G z.r): Prop:= speak (s a) (n a)-speak (legible (s a) (m a)) (n a)=speak s' (n a)-speak s₀ (n a) ∧ Charged s' (σ/2) (L' a) ∧ Charged s₀ (σ/2) (L' a)
 have h(i:ι)(h':Charged (s i) σ (Λ i)):∃ s' s₀:Packet G z.r, U i s' s₀:= by obtain ⟨p,q,t,hp,h⟩:= action_slips (s i) h' v (m i); exact ⟨p,q,funext fun x=> t (n i) (Desk.night x),hp,h⟩
 choose F F₀ hGp using (fun i=>(show ∃ s' s₀:Packet G z.r,Charged (s i) σ (Λ i)→ U i s' s₀ from Classical.byCases (fun h'=>(by obtain ⟨p,q,t⟩:= h i h'; exact ⟨p,q,fun _=>t⟩)) (fun h'=> ⟨s i,s i,fun he=>(h' he).elim⟩)))
 let h:= hU.mono fun i hi=> hGp i hi
 let hs (p:ι→Packet G z.r) (h':∀ᶠ i in T.rail,Charged (p i) (σ/2) (L' i)):= Atlas.space z p h' (half_pos v) (((hm _ (half_pos v) η).mul hp).weak (b:=η) (by simp)) ha hq (by omega : 1 ≤ j)
 have hu :∀ᶠ i in T.rail,x i∈ Metric.closedBall 0 (f i):= hv.mono fun i hi=>mem_closedBall_zero_iff.mpr hi.2
 have he': (fun _ => 1) ≤ᶠ[T.rail] (fun i=>(f i)⁻¹):= (hv.and (ha.low (by norm_num) zero_lt_one)).mono fun i hi=> (one_le_inv₀ hi.1.1).2 ((le_abs_self _).trans hi.2.le)
 have hr1(p:ι→Packet G z.r) (h':∀ᶠ i in T.rail,Charged (p i) (σ/2) (L' i)): Catch.Cover T j η H (fun i=> F' (speak (p i) (n i))) x:= (Catch.Cover.from_book («V»:=V) (U:=fun _=>ℝ) _ _ (hs p h') hu).small le_rfl le_rfl he'
 apply ( (hr1 F (h.mono fun _ hi=>hi.2.1)).sub (hr1 F₀ (h.mono fun _ hi=>hi.2.2))).home; filter_upwards [h] with i hi; rw [(show speak _ _-_= _ from hi.1), skirt]
include hw hQ hV
lemma scriptum(η:ℝ): Catch.Cover T j η H (fun i=> F' ((render k (V' i) (b0 i) (n i)-spell k (V' i) (b0 i) (m i) (n i)) ∘ Desk.night)) x:= by
 let X i:= V i; let F (z:Age)i:= speak (V' i z) (n i); let Fc (z:Age)i:= speak (legible (V' i z) (m i)) (n i);
 let p(z:Age) i:= ratioW (gStep (b0 i)) z.e z.r; let r(z:Age)i:= F' (p z i • (F z i-Fc z i))
 have hC(w:Age)(hh:w∈ Age.scope k):Catch.Cover T j η H (r w) x:= by
    let h:= hQ.tune.hours w; let hv':= hQ.cellar w; let a:= graded w.e+w.r/2; have he:A (p w) a:= (hv'.small.unitPay le_rfl h).eq_mem ((hQ.tissue w).mono fun i hi=>hi.symm); apply Catch.Cover.home ( (slipsX x hq ha hv hj m hm (η:=η-a) w (hV.desc _ hh)|>.caliber he).weak (by simp)); filter_upwards with i; unfold r; rw [off_sc]
 refine Catch.Cover.home (Catch.Cover.booking (E') hC (hv.mono fun _ hi=> inv_nonneg.mpr hi.1.le)) ?_; filter_upwards [hw] with i hi; ext1 v; have ht (U:Config G (n i)): (spell k (V' i) (b0 i) (m i) (n i) U)=∑ j∈ E', p j i*Extra.Iteration.action (legible (V' i j) (m i)) U:= by rw [spell,Finset.sum_apply]; exact Tilt.emit _ _ _ _ (fun i hh=> Nat.mul_le_mul_left 4 (i.pricey.trans (Nat.add_le_add_right (Age.in_scope.mp hh) 2))|>.trans hi) _ U
 simp only [Finset.sum_apply,r,F,Fc,Shellac.off,render, Function.comp_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul, ht,mul_sub]; rw [← Finset.sum_sub_distrib,←Finset.sum_sub_distrib,←Finset.sum_sub_distrib]; rfl
include hG -- add binder and hG
lemma spelled (hc:Civil S T R) : τ (fun i=>now (Q' i) k (β i) • M' i + L i+ spell k (V' i) (b0 i) (m i) (n i) ∘ Desk.night) (fun i=> adjective (grouping (Q' i) (V' i) (Age.scope k) S.clip (R i)) (n i) (β i)) :=by
 let H':=((keeper S R hG x hq ha hv hj Q' hQ hc).pair (extras x hq ha hv hj Q' hQ V' hV))
 refine ⟨fun l hl=>?_⟩; refine Catch.Cover.home (((H'.trend l hl).sub (scriptum x hq ha hv hj Q' hQ V' hV m hm hw (graded (l+1))))) (Eventually.of_forall fun i=>?_); rw [skirt,skirt,off_ya]; simp only [Pi.add_apply];
 let f:= adjective (shiftB (Q' i) S.clip (R i)) (n i) (β i); let a:= adjective (glory (Q' i) (V' i) (E')) (n i) (β i); rw [show adjective (grouping (Q' i) (V' i) (Age.scope k) S.clip (R i)) (n i) (β i)= f+a from rfl]; ext1 x; simp only [Pi.sub_apply,Pi.add_apply,Shellac.off,Function.comp_apply]; abel
end YM.AllOrder.Wheel
