import YM.MSbar.Scale.Euler
/-! Pole estimates for dimensional regularization. No epsilon poles from root contractions;
 poles only from resolving scaling (Euler) with near-integer dimensions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Scale.Inertia
open Dim Symbol Domain Diagram Super Loops Function Set Filter Flight Counter
open scoped Topology BigOperators ContDiff Classical
variable {C:Type} {W:Edition C} {U:Set ℂ} {A:Mass C} {M:ℂ→Mass C} {N: Multiset C→ℕ}{i n j:ℕ}{d:Bit}{z:ℂ}{F:Functionals C}
variable {f:Vertex C}(hf:Live W d f)
abbrev Apert (A:Mass C) (N:Multiset C→ℕ):= ∀ t, Land (A t-N t)
structure Pass (U:Set ℂ)(N: Multiset C→ℕ)(M:ℂ→Mass C)(j:ℕ):Prop where
    cr : ∀ t,DifferentiableOn ℂ (fun z=> M z t) U
    bound : ∀ t z, z ∈ U → Land (M z t-N t)
    clear : ∃ L: Multiset C→ℕ→ℂ→ℂ, (∀ t i, i<N t →DifferentiableOn ℂ (L t i) U) ∧ ∀ t i, i < N t → ∀ z ∈ rim U, L t i z=z^j/(M z t-i)

def solve (A:Mass C)(N:Multiset C→ℕ)(f:Vertex C): Vertex C:= apply_at (fun t h=> rollout (N t) (A t) h 1) f
variable (he: Apert A N)
include he hf
lemma plans : Cell W d (solve A N f):= reform (A:=fun t h=> rollout (N t) (A t) h 1) (fun t=>great_chart (fun hf hg=>congr_fun (Flight.plus hf hg (he t)) 1) (fun c {_} hf=>congr_fun (Flight.scalar hf (he t) c) 1)) hf
omit hf he in
lemma brights [Profit U] (hp:Pass U N M j){F: Functionals C}(h:Bright U W d F):
    Price j U W d (fun z=> solve (M z) N (F z)) :=by -- omit context
       obtain ⟨H,J,L,hl,hr⟩:=hp; let F' (z:ℂ):= apply_at (fun (t:Multiset C) g=> table (z^j) (N t) (fun i=>L t i z) (M z t) g 1) (F z)
       refine ⟨F',lined (A:=fun t z g=> table (z^j) (N t) (fun i=>L t i z) (M z t) g 1) (fun t z hz=>great_chart (fun hf hg=> congr_fun (grouping hf hg (J t z hz)) 1) (fun c {_} hf=> congr_fun (multiplier hf (J t z hz) c) 1)) ?_ Profit.pub Profit.proper h,fun z hz=>?_⟩
       · intro E i1 i2 i3 t g hg; exact (table_AH Profit.pub (H t) (b:=fun z=>z^j) (R:=L t) (differentiableOn_id.pow j) (hl t) (J t) hg).arguments (w:=fun x=>(x,(1:ℝ))) (by fun_prop)
       funext m x; change (z^j:ℂ)*_=table (z^j) (N (skin x)) _ _ _ 1; rw [stake (?_)]; rfl; exact fun i hi=> hr _ _ hi _ hz
omit hf he in
lemma priced [Profit U] (hp:Pass U N M j){F: Functionals C}(h:Price i U W d F):
    Price (j+i) U W d (fun z=>solve (M z) N (F z)):=by -- omit
       have ⟨G,hG,H⟩ := h; obtain ⟨X,hX,hh⟩:=brights hp hG; refine ⟨_,hX,fun z hz=>?_⟩
       rw [← hh hz,← thread,swell_inner,swell_inner,swell_inner,← H hz,swell_inner]; congr! 1
       funext m x; unfold solve apply_at; dsimp only; rw [ray_scale, Flight.scalar (great_ray (Price.alive h hz) x) (hp.bound (skin x) z hz.1)]; rfl

lemma true_rays {x: Words C n}: ray (solve A N f) x=Flight.rollout (N (skin x)) (A (skin x)) (ray f x):=by
   by_cases h:channel x=0
   · funext t; rw [ray,if_pos h,solve,apply_at,drag_skin,arms h,Flight.comm (great_ray hf x) t (he _)]; simp [Flight.pull]
   rw [show ray f x=0 from funext fun t=>by simp [ray,h], Flight.ground (he _)]; ext; simp [ray,h]

lemma admitted : Live W d (solve A N f):=by
   have hp: Pass disk N (fun _=>A) 0 :=⟨fun _=>differentiableOn_const _,fun t _ _=> he t, ⟨fun t i z=> 1/(A t-i),fun _ _ _=> differentiableOn_const _, by intros; simp⟩⟩
   let z:ℂ:=1/2; have hz : z∈rim disk := by norm_num [rim,disk,z, Metric.mem_ball]
   exact Price.alive (brights (F:=liftV f) hp (cold hf)) hz
lemma reserve (hc : tangent A f): Scale.tick A (solve A N f)= f:=by
    funext n x; change flight _ _ 1=_; rw [true_rays hf he, solves (hc n x) (great_ray hf x) (he (skin x)), ray_center (live_cell hf)]
lemma tangent_val : tangent A (solve A N f):= fun n x=>by rw [true_rays hf he]; exact normalization (great_ray hf x) (he _)
end YM.MSbar.Scale.Inertia
