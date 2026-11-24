import YM.FrontierTrace.Primary.Frames
import YM.Work.A05.Window

/-! # compact, divergence-free translation shear detector

To isolate `J00-J11` and leave only offdiags. Need no annular estimates
near coincidence. All shape variable integrations on FIXED compact sets
of [0,δ] × wing. `projectiongeneric` further. Centers slide along axis0,
so NOT introducing a long-distance direction derivative or probe horizon.
-/
set_option autoImplicit false
set_option maxHeartbeats 850000
noncomputable section
namespace YM.FrontierTrace.Primary
open Function Set Filter Analysis Trace Table Work.A01 Work.A05 MeasureTheory
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius InnerProductSpace Interval
variable (ℓ:E4) {v y:E4} {t:ℝ}

def slide (t:ℝ):E4:=ℓ+t • basis 0
/-- choose ℓ₀>ℓ₁>0, then all rotated scalar slots also generic. -/
structure Aimed : Prop where
    unit : ‖ℓ‖=1
    first : ℓ 1 < ℓ 0
    positive : 0<ℓ 1
    clear : ∀ a,ℓ a≠0
namespace Aimed
variable {ℓ} (h:Aimed ℓ)
include h
lemma openRay: ℓ 0*ℓ 1≠ 0:= mul_ne_zero (h.clear _) (h.clear _)
lemma chosen (t:ℝ) (ht:0≤t):‖slide ℓ t‖^2=1+2*ℓ 0*t+t^2:=by
   unfold slide; rw [←real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_add_right]
   simp only [real_inner_smul_left,real_inner_smul_right,real_inner_self_eq_norm_sq,h.unit]; norm_num
   have he: ⟪ℓ,basis 0⟫_ℝ=ℓ 0:=by rw [PiLp.inner_apply, Fin.sum_univ_four]; simp
   rw [he,norm_smul_of_nonneg ht,basis_norm]; ring
lemma slide_norm (t:ℝ) (ht:0≤t):1≤‖slide ℓ t‖:=by
   have hS:=h.chosen t ht; have h₁:= norm_nonneg (slide ℓ t); nlinarith [sq_nonneg t, mul_nonneg ht (h.positive.trans h.first).le]
end Aimed

def acrossRay : ℝ:=Real.sqrt (3+(ℓ 0)^2) - ℓ 0
lemma across_pos:0<acrossRay ℓ:=by unfold acrossRay; nlinarith [Real.sq_sqrt (by positivity : 0≤ 3+(ℓ 0)^2), Real.sqrt_nonneg (3+(ℓ 0)^2)]
lemma across_length (h:Aimed ℓ): ‖slide ℓ (acrossRay ℓ)‖=2:=by have he:=h.slide_norm (acrossRay ℓ) (across_pos ℓ).le; have hv:=h.chosen (acrossRay ℓ) (across_pos ℓ).le; unfold acrossRay at *; nlinarith [Real.sq_sqrt (by positivity : 0 ≤ 3+(ℓ 0)^2)]

def wing := {z:E4|1/4≤‖z‖ ∧ ‖z‖≤1/2}
lemma wing_compact : IsCompact wing := by
   have hw : IsClosed wing:= (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
   exact (isCompact_closedBall (0:E4) (1/2)).of_isClosed_subset hw (fun z h=>Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact h.2))
lemma wing_safe {z:E4} (hz:z∈ wing): z≠0:= norm_pos_iff.mp (lt_of_lt_of_le (by norm_num:(0:ℝ)<1/4) hz.1)
lemma wing_room3 (hv:1≤‖v‖) {z:E4} (hz:z∈ wing): Points.cons (v+z) (atShape v)∈ conf 3:= by
    have hS:= wing_safe hz
    apply conf_cons (atRoom (norm_pos_iff.mp (by linarith)))
    intro i hi; fin_cases i
    · change v+z=v at hi; apply hS (add_eq_left.mp hi)
    change v+z=0 at hi; have hh:z=-v:=eq_neg_iff_add_eq_zero.mpr ((add_comm ..).trans hi); have hz':=hz.2; rw [hh,norm_neg] at hz'; linarith

def seed : ContDiffBump (0:E4):=⟨1/4,1/2,by norm_num,by norm_num⟩
def proj : E4→L[ℝ] ℝ:= EuclideanSpace.proj 1
def ψ (x:E4):ℝ:= seed x * proj x
def firstProbe := D (basis 1) ψ
def secondProbe := -D (basis 0) ψ
local notation "Ξ₀"=> firstProbe
local notation "Ξ₁"=> secondProbe
local notation "I"=> Metric.ball (0:E4) (1/4)
local notation "U"=> Metric.closedBall (0:E4) (1/2)

lemma ψ_germ {z:E4} (h:z∈I): ψ =ᶠ[𝓝 z] (proj:E4→ℝ):=by
    filter_upwards [Metric.isOpen_ball.mem_nhds h] with y hy; rw [ψ,seed.one_of_mem_closedBall (Metric.ball_subset_closedBall hy),one_mul]
lemma dψ_supp (i:Axis) : tsupport (D (basis i) ψ) ⊆ U:=by
    apply subset_trans (tsupport_fderiv_apply_subset ℝ (basis i)); apply subset_trans (b:=tsupport (seed:E4→ℝ)) (closure_mono fun y hy=> ?_) (by rw [seed.tsupport_eq]; exact subset_rfl)
    intro h; change seed y=0 at h; apply hy; change seed y * _=0; rw [h,zero_mul]
lemma first_germ (h:y∈I): Ξ₀ =ᶠ[𝓝 y] fun _=>1:=by
    filter_upwards [(ψ_germ h).fderiv (𝕜:=ℝ)] with z hz; change fderiv ℝ ψ z _ = _; rw [hz,proj.fderiv]; change (basis 1) 1=1; simp
lemma second_germ (h:y∈I): Ξ₁ =ᶠ[𝓝 y] fun _=>0:=by
    filter_upwards [(ψ_germ h).fderiv (𝕜:=ℝ)] with z hz; change -(fderiv ℝ ψ z _)= _; rw [hz,proj.fderiv]; change -((basis 0) 1)=0; simp
lemma second_wing : tsupport Ξ₁ ⊆ wing := by
    intro y hy; constructor
    · by_contra! H; apply notMem_tsupport_iff_eventuallyEq.mpr (second_germ (by simpa [Metric.mem_ball] using H)) hy
    have he : tsupport Ξ₁⊆U:= by change tsupport (-_)⊆_; rw [tsupport_neg]; exact dψ_supp 0
    simpa only [Metric.mem_closedBall,dist_zero_right] using he hy
lemma first_wing (i:Axis) : tsupport (D (basis i) Ξ₀) ⊆ wing:=by
    intro y hy; constructor
    · by_contra! H; apply notMem_tsupport_iff_eventuallyEq.mpr ?_ hy; have hv:=first_germ (show y∈ I from by simpa [Metric.mem_ball] using H)
      filter_upwards [hv.fderiv (𝕜:=ℝ)] with x hx; simp [D,hx]
    have he: y∈U:= dψ_supp 1 (tsupport_fderiv_apply_subset ℝ _ hy)
    simpa [Metric.mem_closedBall] using he
lemma dψ_smooth (i:Axis) : ContDiff ℝ ∞ (D (basis i) ψ):=contDiff_iff_contDiffAt.mpr (fun _=> dSmooth ((seed.contDiff (n:=⊤)).mul proj.contDiff).contDiffAt _ (by simp))
lemma first_smooth : ContDiff ℝ ∞ Ξ₀ := dψ_smooth _
lemma second_smooth : ContDiff ℝ ∞ Ξ₁ := (dψ_smooth _).neg
lemma div0 (v:E4):D (basis 1) Ξ₁ v = -D (basis 0) Ξ₀ v:= by
    unfold secondProbe firstProbe; rw [D,fderiv_neg]; apply congr_arg Neg.neg; apply commuteD (show ContDiffAt ℝ 2 ψ v from (seed.contDiff.mul proj.contDiff).contDiffAt)

def seat (v:E4)(χ:E4→ℝ)(y:E4):= χ (y-v)
lemma unseat (v y:E4)(χ:E4→ℝ): seat v χ (v+y)=χ y:=by unfold seat; simp
lemma seat_stretch (i:Axis)(v y:E4)(φ:E4→ℝ)(hp:ContDiff ℝ ∞ φ): D (basis i) (seat v φ) (v+y)=D (basis i) φ y:=by
    let f:= fderiv ℝ (fun z:E4=>z-v) (v+y)
    change fderiv ℝ (φ ∘ (·-v)) _ _= _; rw [fderiv_comp (v+y) ((hp.differentiable (by simp)) _) (by fun_prop),ContinuousLinearMap.comp_apply]; rw [(show HasFDerivAt (fun z:E4=>z-v) (ContinuousLinearMap.id ℝ E4) _ from (hasFDerivAt_id (𝕜:=ℝ) _).sub_const v).fderiv,add_sub_cancel_left]; rfl
lemma support_shift (φ:E4→ℝ): y ∈ tsupport (seat v φ) ↔ y-v ∈ tsupport φ:=by
    let H:=Homeomorph.subRight v
    change y ∈ tsupport (φ ∘ H) ↔ H y∈_
    rw [tsupport_comp_eq_preimage]; rfl
lemma seat_smooth (v:E4)(φ:E4→ℝ)(h:ContDiff ℝ ∞ φ):ContDiff ℝ ∞ (seat v φ):= by unfold seat; fun_prop
lemma first_window (hv:1≤‖v‖) : Window (atShape v) (seat v Ξ₀) := by
    have ho: seat v Ξ₀ =ᶠ[𝓝 v] fun _=>1 :=
       (first_germ (y:=0) (by simp [Metric.mem_ball])).comp_tendsto (show Tendsto (fun z:E4=>z-v) (𝓝 v) (𝓝 0) from by simpa using! (tendsto_id.sub_const v: Tendsto _ (𝓝 v) _))
    refine ⟨seat_smooth _ _ first_smooth,?_,ho,?_⟩
    · have hq: HasCompactSupport Ξ₀:= ((isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) (dψ_supp 1)); exact hq.comp_homeomorph (Homeomorph.subRight v)
    intro i he; rw [support_shift] at he; have ht:=dψ_supp 1 he; change (0:E4)-v∈U at ht; simp [Metric.mem_closedBall] at ht; linarith
lemma second_room {y:E4} (hv:1≤‖v‖) (hy:y∈ tsupport (seat v Ξ₁)) : Points.cons y (atShape v)∈ conf 3 := by
    have hs:= wing_room3 hv (second_wing ((support_shift _).mp hy)); simpa using hs
end YM.FrontierTrace.Primary
