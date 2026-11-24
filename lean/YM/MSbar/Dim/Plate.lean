import YM.MSbar.Dim.Drop

/-! The hat part of a one-loop integration. General pullback for any symbol well defined
on one extra plane. The dimension parameter is **in pairs**. Public facing d-reg calculations
will feed in number of extra pairs `-ε`. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Dim
open Function Set Filter Metric Complex MeasureTheory Symbol
open scoped Topology ContDiff BigOperators Classical InnerProductSpace

variable {E X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
-- support in norm (not squared)
abbrev Vanish (K : ℝ) (f : E→ℂ) := ∀ q: E, K<‖q‖ → f q=0
variable {m n : ℕ} {K H : ℝ} {f g : Hat (m+1)→ℂ}
lemma Vanish.compact {f:E→ℂ} (hf: Vanish K f): HasCompactSupport f :=
    (isCompact_closedBall 0 K).of_isClosed_subset isClosed_closure (closure_minimal (fun x hx=> mem_closedBall_zero_iff.mpr (le_of_not_gt fun h=> hx (hf x h))) isClosed_closedBall)
lemma Vanish.face [MeasurableSpace E] {f:E→ℂ} (hf:Vanish K f) {μ : Measure E} : (∫ x,f x ∂μ)=∫ x in closedBall (0:E) K,f x ∂μ :=
    Eq.symm (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx=> hf _ (lt_of_not_ge fun h=> hx (mem_closedBall_zero_iff.mpr h))))

def push (m:ℕ) (s:Hat m × ℝ):= grow m (s.1,s.2 • axis)
lemma tame_push : (push m).HasTemperateGrowth:=by
    let v : (Hat m × ℝ)→L[ℝ] Plane := (ContinuousLinearMap.snd ℝ (Hat m) ℝ).smulRight axis
    exact (grow m).hasTemperateGrowth.comp (tame_pair tame_projL v.hasTemperateGrowth)
lemma bounds (q:Hat m) (v:ℝ) : ‖q‖≤ ‖push m (q,v)‖ ∧ ‖v‖ ≤ ‖push m (q,v)‖:=by
    have hh: ‖push m (q,v)‖^2= ‖q‖^2+‖v‖^2:=by unfold push; rw [grow_sq]; simp only [norm_smul,axis_norm,mul_one]
    constructor <;> nlinarith [norm_nonneg q,norm_nonneg v,norm_nonneg (push m (q,v))]

structure Packed (m:ℕ)(K:ℝ)(F:Hat (m+1)→ℂ):Prop where
    space : 0≤K
    smooth : F.HasTemperateGrowth
    nulls : Vanish K F
    even (q:Hat m) : Function.Even (fun v:ℝ=> F (push m (q,v)))
    -- independence further perpendicular rotations separately supplied

variable (hp : Packed m K f) {s : ℂ}
include hp
lemma Packed.radius (q:Hat m): Radius K (fun v:ℝ=> f (push m (q,v))) := ⟨hp.space,hp.smooth.1.comp (tame_push.1.comp (contDiff_const.prodMk contDiff_id)),hp.even _,fun v hv=>hp.nulls _ ((hv.trans_le (le_abs_self _)).trans_le (bounds q v).2)⟩

def face (s : ℂ) (f:Hat (m+1)→ℂ) (v: Hat m) := radial (fun t=> f (push m (v,t))) (s-(m:ℂ))
def plate (s : ℂ) (f:Hat (m+1)→ℂ) := ∫ v, face s f v
omit hp in
lemma face_zero (v:Hat m): face s (0: Hat (m+1)→ℂ) v=0:= emit_zero _
lemma Packed.add_face (hq : Packed m H g) (v : Hat m) : face s (f+g) v= face s f v+face s g v:= radial_add (hp.radius v) (hq.radius v) _
lemma Packed.ends : Vanish K (face s f):=by
    intro v h; have hq : (fun t=> f (push m (v,t)))=0:=funext fun t:ℝ=> hp.nulls _ (h.trans_le (bounds v t).1)
    unfold Dim.face; rw [hq,emit_zero]

omit hp in
lemma face_ah {G : ℂ×(E × Hat (m+1)) →ℂ} {U : Set ℂ} {t : ℂ→ℂ}(h : AH U G)(ht : DifferentiableOn ℂ t U) (hu:IsOpen U)
   (hg : ∀ z∈U,∀ x, Packed m K (fun y=>G (z,x,y))) : AH U (fun p:ℂ × (E × Hat m)=> face (t p.1) (fun y=> G (p.1,p.2.1,y)) p.2.2):=by
    let w : (E × Hat m)×ℝ → E × Hat (m+1):= fun x=>(x.1.1,push m (x.1.2,x.2))
    have hL : HasTemperateGrowth (fun p:(E × Hat m) × ℝ=> p.1.2) := by fun_prop
    have hP := (tame_push (m:=m)).comp (tame_pair hL tame_projR)
    have hw : w.HasTemperateGrowth := tame_pair (by fun_prop : HasTemperateGrowth (fun y:(E × Hat m)×ℝ=>y.1.1)) hP
    let F : ℂ × ((E × Hat m)×ℝ)→ℂ:=fun p => G (p.1,w p.2)
    have H : AH U F:= h.arguments hw
    unfold Dim.face
    exact radial_AH (F:=F) (t:=fun z=> t z-(m:ℂ)) (ht.sub_const _) hu H (fun z hz x=> (hg z hz x.1).radius x.2)

lemma Packed.face_tame (s:ℂ) : (face s f).HasTemperateGrowth:= by
    let G : ℂ × (Hat m × ℝ)→ℂ := fun p=> f (push m p.2)
    have hR : AH univ G:= AH.param_tame (hp.smooth.comp tame_push)
    have hn:= radial_AH (X:=Hat m) (t:=id) differentiableOn_id isOpen_univ hR (fun _ _ x=> hp.radius x)
    exact hn.slice (mem_univ (s-(m:ℂ)))
lemma Packed.integrable (s:ℂ) : Integrable (face s f):= ((hp.face_tame _).1.continuous).integrable_of_hasCompactSupport (hp.ends.compact)

lemma Packed.read : plate s f=∫ v in closedBall (0:Hat m) K,face s f v:= hp.ends.face
lemma four_plane : plate (m:ℂ) f = ∫ v: Hat m, f (up m v) := by
   unfold plate face; refine integral_congr_ae (Eventually.of_forall fun v=>?_); dsimp only; rw [sub_self,radial_zero (hp.radius _)]; simp [push]
omit hp in
lemma plate_zero (s:ℂ) : plate s (0:Hat (m+1)→ℂ)=0:=by simp [plate,face_zero]
lemma plate_add (hq : Packed m H g) (s :ℂ): plate s (f+g)=plate s f+plate s g:=by
    unfold plate; simp_rw [hp.add_face hq]; exact integral_add (hp.integrable s) (hq.integrable s)
lemma plate_smul (c s:ℂ) : plate s (c • f)=c*plate s f:= by
    unfold plate; rw [← integral_const_mul]; exact integral_congr_ae (Eventually.of_forall fun v=> radial_smul (hp.radius v) c _)
omit hp in
lemma plate_ah {G : ℂ×(E × Hat (m+1)) →ℂ} {U : Set ℂ} {t : ℂ→ℂ} (h : AH U G) (ht : DifferentiableOn ℂ t U) (hu:IsOpen U)
   (hg : ∀ z∈U,∀ x, Packed m K (fun y=>G (z,x,y))) : AH U (fun p:ℂ×E=> plate (t p.1) (fun y=> G (p.1,p.2,y))) := by
    have hf:= face_ah h ht hu hg
    let S:= closedBall (0:Hat m) K; haveI : IsFiniteMeasure (volume.restrict S):= ⟨by rw [Measure.restrict_apply_univ]; exact (isCompact_closedBall _ _).measure_lt_top⟩
    have H:= hf.after_average (μ:=volume.restrict S) (p:=id) (integrable_const (1:ℂ)) aestronglyMeasurable_id (ae_restrict_mem (s:=S) measurableSet_closedBall) (show IsCompact S from isCompact_closedBall ..)
    refine H.congr hu (fun z hz x=>?_); simp only [id,one_mul]; exact (Packed.read (hg z hz x)).symm
end YM.MSbar.Dim
