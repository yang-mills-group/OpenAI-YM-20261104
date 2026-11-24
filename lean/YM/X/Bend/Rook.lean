import YM.X.Bend.Park
/-!
# T profile. spheres positive stencil; compactly separated by >four. coupled smoothing for connected reductions with joint Cartesian products. Not OS probes.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Bend
open Maxwell Set Function MeasureTheory Lattice Wilson Next.Rank Labels Pert.Position
open Filter Metric Chir Sage Tri
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{F:Labels.Frames G} {d k m n:ℕ} {q:ℕ+} {V I:Type*} {r R:ℝ}
local notation "K"=> (atTop:Filter ℕ)
local notation "T"=>Fin 3
variable (r:ℝ) (p:Fin m ↪ Fin 3)
def galavant : ContDiffBump (0:ℝ):= ⟨1/32,1/16,by norm_num,by norm_num⟩
def θr (r:ℝ)(x:E4):= galavant (‖x‖^2-r^2)
def moors (r:ℝ)(x:E4):Prop:= r-1/4 ≤ ‖x‖∧‖x‖≤ r+1/4
lemma mooring (h:1/2 ≤ r)(x:E4)(hx: θr r x≠0) : moors r x:= by
    have he: ‖x‖^2-r^2 ∈ Function.support galavant:= hx; rw [galavant.support_eq,mem_ball,dist_zero_right,Real.norm_eq_abs] at he; change |‖x‖^2-r^2| < 1/16 at he; constructor <;> nlinarith only [norm_nonneg x,(abs_lt.mp he).1,(abs_lt.mp he).2,h]
lemma posV (h:0<r) : θr r (r • basis 0)=1:= by unfold θr; rw [norm_smul,Real.norm_of_nonneg h.le,basis_norm,mul_one,sub_self]; exact galavant.one_of_mem_closedBall (by rw [mem_closedBall]; simpa using galavant.rIn_pos.le)
lemma revolve (s:Ortho)(x:E4): θr r (s.move x) = θr r x:= by unfold θr; rw [Ortho.move_norm]
lemma smoothV : ContDiff ℝ ∞ (θr r):= galavant.contDiff.comp ((contDiff_norm_sq ℝ).sub contDiff_const)
def feeability (r:ℝ): Fin 3→ℝ:= ![r+1,1/2,17/2]
local notation "θ"=> feeability r
def note (r:ℝ)(p:Fin m ↪ Fin 3)(x:Points m):=∏ i:Fin m,θr (feeability r (p i)) (x i)
def rangeT (r:ℝ)(p:Fin m ↪ Fin 3) : Set (Points m):= ⋂ i:Fin m,{x|moors (feeability r (p i)) (x i)}
lemma range_m (s:Points m):s ∈rangeT r p ↔∀ i:Fin m,moors (θ (p i)) (s i):= Set.mem_iInter
lemma seats_compact (e:ℝ): IsCompact {x:E4|moors e x}:= (isCompact_closedBall (0:E4) (e+1/4)).of_isClosed_subset ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)) (by rintro x ⟨_,hw⟩; rwa [mem_closedBall,dist_zero_right]) -- interior names.
lemma range_compact : IsCompact (rangeT r p):= by
   let f:=WithLp.toLp (V:=(Fin m→E4)) 2; let s:Set (Fin m→E4):= {x | ∀i:Fin m, moors (θ (p i)) (x i)}
   rw [show rangeT r p=f '' s from ?_]; exact (show IsCompact s from isCompact_pi_infinite fun i=> seats_compact _).image (PiLp.continuous_toLp 2 _)
   ext1 x; rw [range_m]; constructor; · intro h; exact ⟨_,(show WithLp.ofLp x ∈ s from h), by simp [f]⟩
   rintro ⟨x,h,rfl⟩; exact h
variable (hr:4096 ≤ r)
include hr
lemma sc (i:T): (1/2:ℝ) ≤ feeability r i:= by fin_cases i <;> norm_num [feeability] <;> linarith only [hr]
lemma signal (i j:T)(h:i≠j) : θ i+5 ≤ θ j ∨ θ j+5 ≤ θ i := by
    fin_cases i<;>fin_cases j<;> first|exact False.elim (h rfl)|(norm_num [feeability]; first|(left;linarith only [hr])|(right;linarith only [hr]))|norm_num [feeability]
lemma fray (x y:E4)(i j:T)(h:i≠j)(hx:moors (θ i) x)(hy:moors (θ j) y) :4 < ‖x-y‖:= by have he:=norm_sub_rev x y; rcases signal r hr i j h with h|h <;> linarith only [h,hx.1,hx.2,hy.1,hy.2,norm_sub_norm_le x y,norm_sub_norm_le y x,he]
lemma range_line (x:Points m)(hx:x∈ rangeT r p): Pulse.Region m 4 x:= fun i _ j _ he=>fray r hr _ _ _ _ (p.injective.ne he) ((range_m r p _).mp hx i) ((range_m r p _).mp hx j)
lemma range_conf (x:Points m)(hx:x∈rangeT r p): x∈conf m:= by
   intro i j hij; by_contra H; have he:= range_line r p hr x hx i (by simp) j (by simp) H; rw [hij, sub_self,norm_zero] at he;norm_num at he
lemma range_note : tsupport (Complex.ofReal ∘ note r p)⊆ rangeT r p:= by
   apply closure_minimal _ (range_compact r p).isClosed; rintro x hx; apply (range_m r p x).mpr; intro i; apply mooring _ (sc r hr _) _; intro h; apply hx; rw [comp_apply,note,Finset.prod_eq_zero (Finset.mem_univ i) h];simp
omit hr in
lemma varying_c : ContDiff ℝ ∞ (note r p):= contDiff_prod (fun i _=> (smoothV _).comp (PiLp.proj (𝕜:=ℝ) 2 (fun _:Fin m=> E4) i).contDiff)
def Eyes : Test m := ⟨Complex.ofReal ∘ note r p, Complex.ofRealCLM.contDiff.comp (varying_c r p), (range_compact r p).of_isClosed_subset (isClosed_tsupport _) (range_note r p hr),fun x hx=> range_conf r p hr x (range_note r p hr hx)⟩
local notation "Vᵣ"=> Eyes r p hr
lemma stencil_eye (x:Points m): Eyes r p hr x= ↑(∏ i:Fin m,θr (θ (p i)) (x i)):= rfl
lemma eye_zone (x:Points m)(h:x∈ tsupport Vᵣ): x∈rangeT r p:= range_note r p hr h
lemma eye_pos (x:Points m): 0≤ (Eyes r p hr x).re:= by rw [stencil_eye,Complex.ofReal_re]; apply Finset.prod_nonneg; intro i _; exact galavant.nonneg
lemma eye_has : ∃ x:Points m,Eyes r p hr x=1:= by use points (fun i=> θ (p i) • basis 0); rw [stencil_eye]; simp only [points_apply, posV _ (lt_of_lt_of_le (by norm_num) (sc r hr _)),Finset.prod_const_one,Complex.ofReal_one]
lemma eye_o (s:Ortho)(x:Points m): Vᵣ (points (fun i=> s.move (x i)))= Vᵣ x:= by simp_rw [stencil_eye,points_apply,revolve]
abbrev mainT (r:ℝ)(h:4096≤r):= Eyes r (Function.Embedding.refl (Fin 3)) h
lemma farT (x:Points 3)(hx:x∈ tsupport (mainT r hr)) : Zone (x 1) (x 2) (x 0) ∧ r≤ ‖x 0‖:= by
   have he(i:Fin 3):moors (feeability r i) (x i):= (range_m r _ x).1 (eye_zone r _ hr x hx) i; obtain ⟨h,_⟩:= he 0; obtain ⟨_,ht⟩:= he 1; obtain ⟨hv,hy⟩:= he 2; norm_num [feeability] at h ht hv hy; refine ⟨⟨?_,?_,?_,?_⟩,?_⟩ <;> linarith only [h,ht,hv,hy,hr]
end YM.PositionX.Bend
