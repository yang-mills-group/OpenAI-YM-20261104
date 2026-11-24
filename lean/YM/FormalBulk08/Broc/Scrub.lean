import YM.FormalBulk08.Broc.Blurb

/-!
Invariant uncosted per-period temporary completion. All-leg prices then use
its Ward symmetry without carrying its (period-dependent) paths. Don't confuse
with the final emitted coefficient or physical finite-volume effective action.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Broc
open Function Filter Lattice RG Laurent Bloch Exterior Wilson
open Reef Lava Gorge Mesa Shore Lotus Orb Wick Series Jets PowerSeries North
open Stationary hiding shine Rays
open scoped Topology ENNReal Matrix BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J:Type}{G:Gauge}{n:Side}{s:Signed}{t e E:ℕ}{A σ:ℝ}

def walkD (x:Site n):= route 0 (Lattice.lift x) 1
lemma walk_dest (x:Site n): stop 0 (walkD x)=x:= by unfold walkD; rw [←map_zero (wrap n), ←wrap_stop_cover,route_end,wrap_lift]
def wisp (U:Config G n) (x:Site n):= travel U 0 (walkD x)
def wipeD (U: Config G n):= Lattice.gauge (wisp U) U
lemma wipe_turn (t:Site n→G.El)(U:Config G n): wipeD (Lattice.gauge t U)= Lattice.gauge (fun _=>t 0) (wipeD U) := by
    funext b; unfold wipeD; change wisp (Lattice.gauge t U) _ * _*_ = _; change wisp (Lattice.gauge t U) _ * _*_ = t 0*(wisp U _ * _*_)*(t 0)⁻¹; unfold wisp; simp_rw [travel_gauge,walk_dest]; unfold Lattice.gauge; group
lemma hike_one (x:Site n)(w:Walk): travel (1:Config G n) x w=1:= by induction w generalizing x <;> simp_all [travel,Step.read]
@[simp] lemma wisp_one : wisp (1:Config G n)=1 := funext fun _=> hike_one _ _
@[simp] lemma wipe_one : wipeD (1:Config G n)=1 := by rw [wipeD,wisp_one];funext; simp [Lattice.gauge]
variable (G n)
lemma trail_airy : Army (fun x=> wisp (input G n x)) 0 := by
    intro p
    have h : Army (input G n) 0:=Army.powL contDiffAt_id
    have he (w : Walk)(p:Site n) : ContDiffAt ℝ ω (fun b=> G.mat (travel (input G n b) p w)) 0 := by
       induction w generalizing p with
       | nil=> exact contDiffAt_const
       | cons i t ih=>
         simp_rw [travel,G.mat_mul]; refine ContDiffAt.mul ?_ (ih _); simp_rw [Step.read]; split
         · exact h.inv _
         exact h _
    exact he _ _
lemma trail_swell : Army (wipeD ∘ input G n) 0 := (trail_airy G n).slant (Army.powL contDiffAt_id)
def scrub : Link G n→Link G n := content ∘ wipeD ∘ input G n
lemma scrub_zero : scrub G n 0=0:= by simp [scrub]
lemma scrub_smooth : ContDiffAt ℝ ω (scrub G n) 0:= (trail_swell G n).logL (by simp)
lemma scrub_brush : ∀ᶠ z in 𝓝 0,input G n (scrub G n z)=wipeD (input G n z) := (show Tendsto (wipeD ∘ input G n) (𝓝 0) (𝓝 1) from by simpa using! (trail_swell G n).cont.tendsto).eventually content_encodes
lemma scrub_linger : ∀ᶠ z: Link G n in 𝓝 0,∀ a:G.El,content (Lattice.gauge (fun _=>a) (wipeD (input G n z)))=stain a (scrub G n z):= by
   obtain ⟨ε,hε,H⟩:= Metric.mem_nhds_iff.mp (show {v|G.plog (G.mat (G.lieExp v))=v}∈𝓝 0 from G.plog_left)
   let f:= arm G n 1 ∘ scrub G n; have h (i) : Tendsto (fun x=> f x i) (𝓝 0) (𝓝 0):=by
      have hp : ContinuousAt f 0:=(arm G n 1).continuous.continuousAt.comp (scrub_smooth G n).continuousAt; exact tendsto_pi_nhds.mp (show Tendsto f (𝓝 0) (𝓝 0) from by simpa [f,scrub_zero] using hp.tendsto) i
   filter_upwards [scrub_brush G n, eventually_all.mpr (fun i=> (h i).eventually (Metric.ball_mem_nhds _ hε))] with z hz hn a
   rw [←hz,stain_cons]; let v:=scrub G n z
   apply (arm G n 1).injective; funext ⟨i,b⟩; obtain ⟨b,rfl⟩:=axisEquiv.surjective b
   simp only [coord_map,content_at,encode_link]; apply H
   rw [stain]; simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,(Stationary.arm _ _ _).apply_symm_apply]
   change G.adjoint a (f z (i,coord b))∈_
   simp only [Metric.mem_ball,dist_eq_norm,sub_zero,G.norm_adjoint] at *; exact hn _
variable {G n}
-- piecewise F lets us reuse actual (non-formal) force behind Laurent

def evenBrush (f : Link G n→ℝ) (U:Config G n) := if ∀ a:G.El,f (content (wipeD U))=f (content (Lattice.gauge (fun _=>a) (wipeD U))) then f (content (wipeD U)) else 0
lemma evenBond (f:Link G n→ℝ)(U:Config G n)(k:Site n→ G.El) : evenBrush f (Lattice.gauge k U)=evenBrush f U:= by
    let F a:= f (content (Lattice.gauge (fun _=>a) (wipeD U)))
    have hz:F 1=f (content (wipeD U)):= by unfold F;rw [show Lattice.gauge _ _= wipeD U from funext fun a=>by simp [Lattice.gauge]]
    have ht (a:G.El): f (content (Lattice.gauge (fun _=>a) (wipeD (Lattice.gauge k U))))= F (a*k 0):= by
       rw [wipe_turn]; unfold F; congr 2; funext; simp [Lattice.gauge,mul_assoc]
    have he (b:G.El) : (∀ a,F b=F (a*b)) ↔ ∀ a,F 1=F a := by
        constructor
        · intro H a; rw [←show a*b⁻¹*b=a from inv_mul_cancel_right a b]; rw [←H]; simpa using (H b⁻¹).symm
        intro H a; rw [←H b,H (a*b)]
    unfold evenBrush; simp_rw [ht,wipe_turn,←hz]; change (if ∀ a:G.El,F (k 0)=F (a*k 0) then F (k 0) else 0)=if ∀ a:G.El,F 1=F a then F 1 else 0
    by_cases h:∀ a:G.El,F 1=F a
    · rw [if_pos ((he _).mpr h),if_pos h,←h]
    rw [if_neg (h ∘ (he _).mp),if_neg h]
lemma even_brush (f:Link G n→ℝ)(h:∀ (x:Link G n) (a:G.El), f (stain a x)=f x): (evenBrush f ∘input G n)=ᶠ[𝓝 0] f ∘ scrub G n:= by
    filter_upwards [scrub_linger G n] with z hz; change evenBrush f _=_; unfold evenBrush; refine if_pos ?_ ; intro a;rw [hz,h];rfl
end YM.FormalBulk08.Broc
