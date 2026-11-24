import YM.FormalBulk08.Broc.Scrub
import YM.Next.STATIONARY.Shape.ClassicalMatch
import YM.Next.STATIONARY.Films.LeadingRay

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Broc
open Function Filter Lattice RG Laurent Bloch Exterior Wilson
open Reef Lava Gorge Mesa Shore Lotus Orb Wick Series Jets PowerSeries North
open Stationary hiding shine Rays
open scoped Topology ENNReal Matrix BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J:Type}{G:Gauge}{n:Side}{s:Signed}{r t e E:ℕ}{A σ:ℝ}
-- rank projections use assumption earlier orders (not linear or subminimal spheres). An any-period bridge for coal-V recurrence.

def oracle (T:Pot G)(e t:ℕ)(n: Side)(U:Config G n):ℝ:= Patch.average fun s: Signed=> evenBrush (stripeK T n e t) (pull s 0 U)
def shadeK (T:Pot G)(e t:ℕ)(n: Side):= oracle T e t n ∘ input G n
section
variable (T: Pot G)(h:Charter (stone T n) E)(he:e≤E)(hh:t<e+2)(hw:∀ i<e,coeff i (stone T n)=0)
include h he hh hw
lemma stripe_even (a:G.El): stripeK T n e t ∘ stain a = stripeK T n e t := by
   let i:=ContinuousLinearMap.id ℝ (Link G n)
   have ha x : input G n (stain a x)=Lattice.gauge (fun _=>a) (pull 1 0 (input G n (i x))) := by simp only [←stain_cons,pull_id];rfl
   have hx:=choir T (0:Site n) h he hh hw i (stain a) (fun _ _=>a) (map_zero _) (map_zero _) ⟨a,rfl⟩ (fun _=>contDiffAt_const) i.contDiff.contDiffAt (stain _).contDiff.contDiffAt (.of_forall ha)
   let V:=stripeK T n e t; change V ∘ stain a=V
   exact (linear_blur _ _).trans ((congr_arg (fun p=> fun x:Link G n=>traceP x p) hx.symm).trans (linear_blur _ i).symm)
lemma shade_frame : shadeK T e t n=ᶠ[𝓝 0] fun x=> Patch.average fun s:Signed=> stripeK T n e t (scrub G n (orderTurn s x)) := by
   let F := stripeK T n e t; have ht := even_brush F (fun x a=> congr_fun (stripe_even T h he hh hw a) x)
   have he (s:Signed): ∀ᶠ x : Link G n in 𝓝 0, evenBrush F (pull s 0 (input G n x))= stripeK T n e t (scrub G n (orderTurn s x)) := ?_
   filter_upwards [eventually_all.mpr he] with x hx; exact congr_arg Patch.average (funext hx)
   case _ =>
    filter_upwards [(show Tendsto (orderTurn (G:=G) (m:=n) s) (𝓝 0) (𝓝 0) from by simpa using (orderTurn (G:=G) (m:=n) s).continuous.tendsto 0).eventually ht] with x hx; rw [flip_links]; exact hx
lemma orbitPoint : Pointwise (shadeK T e t n) := by
    refine point_actual _ ?_ ?_ (fun s x=> orbit_axis _ x s)
    · apply AnalyticAt.congr _ (shade_frame T h he hh hw).symm
      unfold Patch.average; apply ContDiffAt.analyticAt; apply ContDiffAt.mul contDiffAt_const; refine ContDiffAt.sum fun i _=>?_ ; exact ContDiffAt.comp (f:=⇑(orderTurn (G:=G) (m:=n) i)) _ (by rw [map_zero]; exact ContDiffAt.comp (f:=scrub G n) (g:=stripeK T n e t) _ (by rw [scrub_zero];apply blueprint_diff) (scrub_smooth ..)) (orderTurn _).contDiff.contDiffAt
    intro v U; unfold oracle; exact congr_arg Patch.average (funext fun s=>by rw [Work.F05.pull_gauge_zero,evenBond])
omit h he hh hw in lemma lens (a:Signed): ContDiffAt ℝ ω ((stripeK T n e t ∘ scrub G n) ∘ orderTurn (G:=G) (m:=n) a) 0:= ContDiffAt.comp _ (by rw [map_zero]; exact ContDiffAt.comp _ (by rw [scrub_zero];apply blueprint_diff) (scrub_smooth ..)) (orderTurn _).contDiff.contDiffAt
-- successive phases. need Charter commute s=a
lemma coinK (a:Signed): coeff (t+1) (paste ((stripeK T n e t ∘ scrub G n) ∘ orderTurn a)) = facade (t+1) (cum 0 n (T e (t+1))):= by
    let Q:= orderTurn (G:=G) (m:=n) a; let k (x:Link G n):=wisp (input G n (Q x)); have hz : k 0 = 1:= by unfold k;simp
    have ht:Tendsto Q (𝓝 0) (𝓝 0):= by simpa using Q.continuous.tendsto 0
    let y := scrub G n ∘ Q
    have HH : coeff (t+1) (paste (blur (cum 0 n (T e (t+1)))))=facade (t+1) (cum 0 n (T e (t+1))):= by rw [blueprint_price,coeff_X_pow_mul']; simp
    refine Eq.trans (choir T (s:=a) (0:Site n) h he hh hw id y k rfl (by simp [y,scrub_zero]) ⟨1,hz⟩ ?_ contDiffAt_id ?_ ?_).symm HH
    · exact Army.comp (w:=Q) (g:=fun x:Link G n=> wisp (input G n x)) (by rw [map_zero];exact trail_airy G n) Q.contDiff.contDiffAt
    · exact ContDiffAt.comp _ (by rw [map_zero];exact scrub_smooth ..) Q.contDiff.contDiffAt
    filter_upwards [ht.eventually (scrub_brush G n)] with i hi;rw [flip_links];exact hi
lemma lens_boat : paste (shadeK T e t n) = C (MvPolynomial.C (Fintype.card Signed:ℝ)⁻¹)* ∑ a:Signed,paste ((stripeK T n e t ∘ scrub G n)∘orderTurn a) := by
   rw [paste_replace (shade_frame T h he hh hw)]
   let F a:= (stripeK T n e t ∘ scrub G n)∘orderTurn a
   have hF a : ContDiffAt ℝ ω (F a) 0 := lens T a
   simp only [Patch.average]; rw [show (fun x=> _*∑ a:Signed,stripeK T n e t (scrub G n (orderTurn a x)))=(fun _:Link G n=> (Fintype.card Signed:ℝ)⁻¹)*(∑ a:Signed,F a) by ext;simp [F,Finset.sum_apply],paste_mul _ _ contDiffAt_const ?hv,paste_flat,garter _ _ (fun i _=>(hF i).of_le le_top)]
   case hv=> rw [show (∑ a:Signed,F a) = fun x=>∑ a,F a x by ext; simp [Finset.sum_apply]]; exact ContDiffAt.sum fun i _=>(hF i).of_le le_top
lemma lens_abroad : coeff (t+1) (paste (shadeK T e t n))=facade (t+1) (cum 0 n (T e (t+1))) := by
    rw [lens_boat T h he hh hw, coeff_C_mul, map_sum]; simp_rw [coinK T h he hh hw]; simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; rw [←mul_assoc]; rw [←map_natCast (MvPolynomial.C),←map_mul]; simp
lemma lens_quiet {r:ℕ} (hr:r<t+1): coeff r (paste (shadeK T e t n))=0:= by
    rw [lens_boat T h he hh hw,coeff_C_mul,map_sum]; rw [Finset.sum_eq_zero (fun i _=>?_),mul_zero]
    let Q:=orderTurn (G:=G) (m:=n) i
    exact blur_low (cum 0 n (T e (t+1))) (scrub G n ∘ Q) (by simp [scrub_zero]) (ContDiffAt.comp _ (by rw [map_zero]; exact (scrub_smooth ..).of_le le_top) Q.contDiff.contDiffAt) _ hr
lemma quietsK : Quiets (shadeK T e t n) (t+1) := by
   intro i hi hl; let a:Link G n→ℝ:=0; have he:=lens_quiet T h he hh hw hi
   have ha : coeff i (paste a)=0:= by change coeff i (paste (fun _:Link G n=>0))=_; simp only [paste_flat,map_zero];
   rw [←ha] at he; rw [from_note _ _ i (convert_note (orbitPoint T h (show e≤E from by assumption) hh hw).analytic analyticAt_const he)]; exact congr_fun (iteratedFDeriv_const_of_ne hl.ne' 0) 0
lemma local_receive (v: Up (T e (t+1)))(b: Agate (T e (t+1))) : cum 0 n (T e (t+1))=beam (shadeK T e t n) (t+1):= facade_unique (cum_agate 0 n _ v b) (beam_pulse _ (orbitPoint T h he hh hw).analytic _) (by rw [beam_price,lens_abroad T h he hh hw])
end
end YM.FormalBulk08.Broc
