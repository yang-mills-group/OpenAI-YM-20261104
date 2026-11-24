import YM.Contacts.Sentry.Joint
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Sensor
open Function Set Filter MeasureTheory Extraction Table Org Spec Power Next.UVStress Costar Analysis Ward
open scoped Topology BigOperators ContDiff
variable {α:Type*}{ι J :Type}[Fintype ι][DecidableEq ι][Fintype J][DecidableEq J]
  {G:Gauge}{L:Register G}{S T:Table L}(P:DiffPlan S) (h:P.Derivatives T)(H:T.Hierarchy)
variable (x:ι→ E4)(v:ι→ S.Tag)(u:ι)(k:E4)

/-- One-slot map works also on a companion (cf. adaptation of Ward.takes and here). -/
def dec {S:Table L}{d l:ℕ}(h:d=l) : S.Field d→ₗ[ℂ] S.Field l:= h ▸ LinearMap.id
lemma dec_eq {d l:ℕ}(h:d=l)(v:S.Field d): dec (S:=S) h v=cast (congr_arg S.Field h) v :=by subst l;rfl

def focus (S T:Table L){ι:Type}[Fintype ι][DecidableEq ι](x:ι→ E4)(v:ι→ S.Tag)(u:ι)(d:ℕ): S.Field d→ₗ[ℂ] ℂ :=
    let w:=update v u (⟨d,0⟩:S.Tag); let f:= (measure T x (fun i=>(w i).1)).toLinearMap (fun i=> (w i).2) u
    have hi : (w u).1=d:=by simp [w]
    f.comp (dec hi.symm)

lemma focus_at (S T:Table L){ι:Type}[Fintype ι][DecidableEq ι](x:ι→ E4)(v:ι→ S.Tag)(u:ι)(d:ℕ)(w:S.Field d): focus S T x v u d w=corr T x (update v u ⟨d,w⟩):= by
   let t:= update v u (⟨d,(0:S.Field d)⟩ : S.Tag); have hi:d=(t u).1:=by simp[t]
   let V:S.Field (t u).1:= dec hi w; let z:= update (fun j=>(t j).2) u V
   have he : named (fun i=>(t i).1) z= update v u (⟨d,w⟩: S.Tag):=by
       ext1 j; by_cases h:j=u
       · subst j; simp only [named,z,update_self]; exact Sigma.ext hi.symm (by unfold V; rw [dec_eq]; exact cast_heq _ _)
       simp [t,z,h,named]
   calc _ = measure T x _ z:= rfl
        _ = corr T x (named (fun i=>(t i).1) z):= rfl
        _ = _:= by rw [he]

def drive (d:ℕ): S.Field d→ₗ[ℂ] S.Field (d+1):=∑ i:Axis,(k i:ℂ) • P.deriv d i
-- `k` included?
def pushed (t:ℝ):ι→ E4:= update x u (x u+t • k)
lemma push_zero : pushed x u k 0=x:=by unfold pushed;simp
lemma push_left (y:J→ E4)(t:ℝ): (pushed x u k t ⌢ y)=pushed (x⌢y) (Sum.inl u) k t:=by
   ext1 (i|j); by_cases h:i=u; subst i; simp [pushed]; simp [pushed,h]; simp [pushed]
lemma push_right (y:J→ E4)(t:ℝ): (y⌢ pushed x u k t)=pushed (y⌢x) (Sum.inr u) k t:=by
   ext1 (i|j); simp [pushed]; by_cases h:j=u; subst j; simp [pushed]; simp [pushed,h]
private theorem instP (E:Type*) [NormedAddCommGroup E][NormedSpace ℝ E]: ContinuousSMul ℝ E:= inferInstance
local instance (n:ℕ): ContinuousSMul ℝ (Points n):= instP _
private lemma asym {n:ℕ}(x y:Points n)(t:ℝ): HasDerivAt (fun s:ℝ=> x+s• y) y t:=by
   simpa using (ContinuousLinearMap.toSpanSingleton ℝ y).hasDerivAt (x:=t) |>.const_add x
include h H
lemma one_step (t:ℝ)(hx:Injective (pushed x u k t)) (d:ℕ)(w:S.Field d) :
   HasDerivAt (fun s=> corr T (pushed x u k s) (update v u (⟨d,w⟩:S.Tag)))
    (corr T (pushed x u k t) (update v u (⟨d+1,drive P k d w⟩:S.Tag))) t:=by
       let e:= Fintype.equivFin ι; let n:= Fintype.card ι; let y:=pushed x u k; let z (t:ℝ):= points (y t ∘ e.symm); have ht:z t∈ conf n:=hx.comp e.symm.injective
       let f x:= S.useAt T x (update v u (⟨d,w⟩:S.Tag) ∘ e.symm)
       let D:=∑ i:Axis,k i • Points.direction (e u) i
       have hw j :D j = if e u=j then k else 0:=by
           by_cases h:e u=j; subst j
           · simp only [D,WithLp.ofLp_sum,Finset.sum_apply,Points.direction,PiLp.smul_apply,PiLp.single_eq_same,if_true]; ext i; simp
           · simp [D,Points.direction,h]
       have he' : z=fun t=>points (x ∘ e.symm)+ t • D:=by
           funext t; ext1 i; simp only [z,pushed,y,points_apply,comp_apply,PiLp.add_apply,PiLp.smul_apply,hw i]
           by_cases h:e u=i
           · subst i; simp
           simp [h,Function.update_of_ne, e.symm_apply_eq, Ne.symm h]
       have hp : HasDerivAt z D t:=by
           rw [he']; exact asym _ D t
       have hh := (((S.class_smooth T H.smooth _ (z t) ht).contDiffAt ((conf_open _).mem_nhds ht)).differentiableAt
            (by simp) : DifferentiableAt ℝ f (z t))
       have hF : fderiv ℝ f (z t) D=corr T (y t) (update v u (⟨d+1,drive P k d w⟩:S.Tag)) :=by
           have hz (w:S.Tag):update v u w ∘ e.symm=update (v∘ e.symm) (e u) w:=by
                 ext1 i; by_cases h:e u=i; subst i; simp; simp [update_of_ne, Ne.symm h,e.symm_apply_eq]
           have hh i : Analysis.D (Points.direction (e u) i) f (z t) = focus S T (y t) v u _ (P.deriv d i w):= by
                 unfold f; rw [hz, focus_at]; change _ = S.useAt T _ (update v u _ ∘ e.symm) -- syntax
                 rw [hz]; exact (P.derivative_slot h H.laws.toSymmetric H.smooth ht (e u) (v∘ e.symm) w i).symm
           rw [← focus_at, drive, LinearMap.sum_apply, map_sum,map_sum]; apply Finset.sum_congr rfl; intro i _
           rw [map_smul]; change k i • (Analysis.D _ f _) = _; rw [hh,LinearMap.smul_apply,map_smul,Complex.real_smul]; rfl
       change HasDerivAt (f ∘ z) _ _; rw [← hF]; exact hh.hasFDerivAt.comp_hasDerivAt t hp
end YM.Contacts.Sensor
