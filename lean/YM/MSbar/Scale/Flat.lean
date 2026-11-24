import YM.MSbar.Scale.Resolve
/-! A flat symbol on rays, including out-of-neutral degeneracies. The high cutoff is chosen
surely zero at the origin on a neighborhood and imposes this on parts of trees. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Scale
open Dim Symbol Domain Diagram Super Loops Function Set Filter Flight Counter Metric MeasureTheory
open scoped Topology BigOperators ContDiff Classical
variable {C:Type}{W: Edition C}{m j i:ℕ}{d:Bit} {f g:Vertex C}{w:Words C m} {x:Flight.Vec}

-- In the sequel `Flat` means identically zero in a neighborhood along each ray.
abbrev Flat (f:Vertex C):Prop:= ∀ i (x:Words C i), ∀ᶠ t:ℝ in 𝓝 0, f i (drag t x)=0
namespace Flat
lemma line (h:Flat f): ray f w =ᶠ[𝓝 0] 0:= (h _ w).mono fun s hs=> by simp [ray,hs]
lemma of_line (h: Live W d f)(he:∀ i (x:Words C i), ray f x=ᶠ[𝓝 (0:ℝ)] 0): Flat f:= by
    intro i x; by_cases H:channel x=0
    · exact (he _ x).mono fun t ht=> by simpa [ray,H] using ht
    have ht:= (he _ (drag 0 x)).eq_of_nhds; refine Eventually.of_forall fun s=>?_; rcases eq_or_ne s 0 with rfl|hv; simpa [ray] using ht
    exact h.quiet 0 (mem_univ _) _ _ (by rw [drag_bal]; exact smul_ne_zero hv H)
-- caution [quiet def]
lemma moves (he:x=ᶠ[𝓝 (0:ℝ)] 0): strip x=ᶠ[𝓝 (0:ℝ)] 0:= by
   have h : x 0=0:= he.eq_of_nhds; filter_upwards [he] with t ht; by_cases H:t=0; subst t; simpa [strip] using he.deriv_eq; simp [strip, dslope_of_ne _ H,slope_def_module,h,show x t=0 from ht]
lemma lifts (he:x=ᶠ[𝓝 (0:ℝ)] 0):layer i x=ᶠ[𝓝 (0:ℝ)] 0:= by induction i with | zero=> exact he | succ n ih=>rw [layer_next]; exact Flat.moves ih
lemma tangent (h: Flat f)(A: Mass C) : Inertia.tangent A f:= fun m _ _ _=> (lifts (Flat.line h)).eq_of_nhds
lemma scalar (a:ℂ)(h:Flat f): Flat (a • f):= fun m x=> (h m x).mono fun s hs=>by simp [hs]
lemma plus (hf:Flat f) (hg:Flat g):Flat (f+g):= fun m x=> by filter_upwards [hf _ x,hg _ x] with s hs hs';simp [hs,hs']
lemma none : Flat (0:Vertex C):= fun _ _=> Eventually.of_forall fun _=>rfl
lemma sum {α:Type*} {s:Finset α} {f:α→ Vertex C}(h:∀ i∈s,Flat (f i)): Flat (∑ i∈s,f i):=by induction s using Finset.induction_on with | empty=>rw [Finset.sum_empty]; exact none | insert i s he ih=> rw [Finset.sum_insert he]; exact Flat.plus (h i (Finset.mem_insert_self ..)) (ih (fun j hj=> h _ (Finset.mem_insert_of_mem hj)))

lemma state (he:x=ᶠ[𝓝 (0:ℝ)] 0) (a:ℂ)(i:ℕ): rollout i a x=ᶠ[𝓝 (0:ℝ)] 0:= by
    induction i generalizing a x with
    | zero=>
       obtain ⟨r,hr,h⟩:= Metric.mem_nhds_iff.mp he -- ambiguity
       filter_upwards [Metric.ball_mem_nhds 0 hr] with w hw
       refine setIntegral_eq_zero_of_forall_eq_zero (?_ : ∀ t∈ Icc (0:ℝ) 1, weight a t*x (t*w)=0); intro t ht; apply mul_eq_zero_of_right; refine h (?_ : t*w∈ Metric.ball (0:ℝ) r)
       rw [mem_ball_zero_iff,norm_mul,Real.norm_of_nonneg ht.1]; exact lt_of_le_of_lt (mul_le_of_le_one_left (by positivity) ht.2) (mem_ball_zero_iff.mp hw)
    | succ n ih=>
        filter_upwards [ih (Flat.moves he) (a-1)] with t ht; unfold rollout higher; dsimp; rw [show x 0=0 from he.eq_of_nhds,show rollout n _ _ _=0 from ht]; simp

lemma solves (he: Live W d f)(h: Flat f){A:Mass C}{N:Multiset C→ℕ} (ha: Inertia.Apert A N): Flat (Inertia.solve A N f):= by
   refine of_line (Inertia.admitted he ha) (fun i x=>?_); rw [Inertia.true_rays he ha]; exact state (Flat.line h) _ _
end Flat
end YM.MSbar.Scale
