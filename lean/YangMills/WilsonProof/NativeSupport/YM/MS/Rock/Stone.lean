import YM.MS.Rock.Stone
import YangMills.WilsonProof.NativeSupport.YM.MS.Rock.Wing
/-!
# Swoop wired kernels including auxiliary test

Encoding final projected tadpole at x=1 on the ray of the given leg list.
 It coincides with computing at any chart of this list; this assertion matters
 because the continued integral is defined by differentiating the whole source.
 Free of any frame costs. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Rock
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux
open Momentum Landau Arts Pilot Spin Arc Wire
open scoped Topology ContDiff
variable {G:Gauge}{I E F H J A:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
 [NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup H][NormedSpace ℝ H]{m n k:ℕ}
-- external sector chord from m→m+n
namespace Path

lemma path (p:SectorP m)(r:ℝ)(h:m<n): slideA h (p,r)=Left h.le p+r • spray (hatch h):=rfl
def backA (h:m<n) : SectorP n→L[ℝ] SectorP m×ℝ:= (Cl h.le).prod (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:L n=>ℝ) (hatch h))
lemma equal0 (x:SectorP m×ℝ)(h:m<n): backA h (slideA h x)=x:=by
   obtain ⟨p,r⟩:=x; apply Prod.ext; · change Cl h.le (slideA _ (p,r))=_;   -- fails hatch not yet expanded
                                        rw [path,map_add,leftCl,map_smul]; simp only [hatch]; rw [← send_spray, Cl_left, smul_zero,add_zero] -- Cl_left name
   change slideA h _ (hatch h)=r; rw [path,Pi.add_apply]; rw [show Left h.le p (hatch h)=0 from offt _ _ _ (fun i=> nowhere h.le i (step h)) ]; simp [spray]
lemma slide_ext (h:m<n)(hp:n≤k)(x:SectorP m)(r:ℝ): Left hp (slideA h (x,r))=slideA (lt_of_lt_of_le h hp) (x,r):=by rw [path,map_add,map_smul,path, ← hatch_ext h hp]; unfold Left; rw [sons,rides_link, send_spray]

-- W cost on paths.
variable [FiniteDimensional ℝ E][FiniteDimensional ℝ F]
variable {z:UScale I}{Z:I→ℂ}{f:I→ Mob G}{u:I→Rip G}{a b:I→ℝ}
lemma sky (hc : ∀ m:ℕ,scaleC z 1 fun i=>‖(2*(Z i-m):ℂ)‖) (hF:fell z a f)(hU: rib z b u)(hp: ∀ i,0≤b i)(W:Touch G m E): quiet z (fun i=> wing (Z i) (u i) (f i) W) (fun i=>b i*a i):= by
   have hv:= higher (slideA (Nat.lt_succ_self m)) (backA (Nat.lt_succ_self m)) (fun p=> equal0 p _) hF hU hp (hc _) (move (Nat.le_succ m) W); convert! hv using 1; ext; simp only [wing,moves]

namespace Fiber
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
lemma curve {f:Tree E ℂ}{g:Tree F ℂ}(x:E)(y:F)(hf:ContDiff ℝ ∞ f)(hk:ContDiff ℝ ∞ g)(hp:∀ r,f (r,x)=g (r,y))(r:ℝ): Arc.d f (r,x)= Arc.d g (r,y):= by
    obtain he:= dr hf x r; rw [funext hp] at he; exact he.unique (dr hk y r)
lemma chopC {f:Tree E ℂ}{g:Tree F ℂ}(x:E)(y:F)(hf:ContDiff ℝ ∞ f)(hk:ContDiff ℝ ∞ g)(hp:∀ r,f (r,x)=g (r,y))(r:ℝ): chop f (r,x)=chop g (r,y):= by
    unfold chop; exact intervalIntegral.integral_congr (fun t _=> curve x y (fresh hf) (fresh hk) (curve x y hf hk hp) (t*r))
lemma pruneC {f:Tree E ℂ}{g:Tree F ℂ}(x:E)(y:F)(hf:ContDiff ℝ ∞ f)(hk:ContDiff ℝ ∞ g)(hp:∀ r,f (r,x)=g (r,y))(m:ℕ): ∀ r, pruning m f (r,x)=pruning m g (r,y):= by
    induction m generalizing f g with
    | zero=> exact hp
    | succ m ih=> unfold pruning; rw [Function.iterate_succ, Function.comp_apply ]; -- better change func
                    exact ih (c_chop hf) (c_chop hk) (chopC x y hf hk hp)
end Fiber
-- predicate gaussian path measure conventions.
noncomputable instance (m:ℕ):Measure.IsAddHaarMeasure (Px m):= inferInstanceAs (Measure.IsAddHaarMeasure (volume (α:=SectorP m)))
def spout (z:ℂ)(U:Rip G)(f:Mob G)(W:Touch G m E): E→ℂ:= swoop z (Px m) m (wing z U f W)
def ocean (z:ℂ)(U:Rip G)(f:Mob G):Mob G:= fun _ l=> spout z U f (ray l) (1:ℝ)
-- q calculation identity for field coordinates p
lemma oceanic (hx:∀ n:ℕ,scaleC z 1 fun i=>‖(2*(Z i-n):ℂ)‖)(h:fell z a f)(hv:rib z b u)(hh:∀ i,0≤b i)(i:I)(W:Touch G m E): fieldVal (ocean (Z i) (u i) (f i) m) W=spout (Z i) (u i) (f i) W:= by
   funext p; let M:=ray (sail W p); let F (i:I):= wing (Z i) (u i) (f i) W; let T (i:I):= wing (Z i) (u i) (f i) M; let μ:= Px m; have he: sail M 1=sail W p:= ray_sail _ -- remove binder
   have h0 r : carpet μ (F i) (r,p)=carpet μ (T i) (r,(1:ℝ)):= by simp [carpet, F,T,wing,he];
   have hz:=Fiber.pruneC p 1 (Arc.Q.Gquiet μ (sky hx h hv hh W)|>.smooth i) (Arc.Q.Gquiet μ (sky hx h hv hh M)|>.smooth i) h0 (m+1)
   change coreC _ _ (carpet μ (T i)) _=coreC _ _ (carpet μ (F i)) _; simp only [coreC,Pi.smul_apply,fetching,fetchP]; change ∀ t:ℝ, pruning (m+1) (carpet μ (F i)) (t,p)=pruning (m+1) (carpet μ (T i)) (t,1) at hz; simp_rw [hz]
end Path
end YM.MS.Rock
