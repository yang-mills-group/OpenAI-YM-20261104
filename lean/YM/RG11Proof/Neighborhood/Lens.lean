import YM.RG11Proof.Neighborhood.Places

/-!
# Powerlog OPE scorecards for point or compact smooth inner designs

Computations coefficientwise on *smooth separated/represented continuum
answers*. garde includes exact Maxwell full kernel. At t not small enough to
achieve separated support, no credit claimed and define bad integrated test
zero (must check domain Ω). Derivative σ (Marks around stresses using `run` or
directional fderiv) can be supplied by other leverages.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.RG11.Neighborhood
open scoped Classical BigOperators ContDiff Topology
open PowerSeries YM.RG11.Fields YM.RG11.Grove YM.RG11.Stress
open Maxwell Labels Function Set Filter MeasureTheory
variable {G: Gauge}{F:Frames G}{n m:ℕ}
local notation "ps"=>PowerSeries ℂ

def here (x:Points n):leverage n:= (LinearMap.proj (R:=ℂ) x).comp (clean n).subtype
 theorem here_at (x:Points n)(h:x∈conf n)(K:Points n→ℂ)(hK:ContDiffOn ℝ ∞ K (conf n)): here x (dress K hK)=K x:=indicator_of_mem h K

/-- Inputs at *relative* coordinates used to sample coefficients. Later joint
profiles may be assembled from exact point identities at exteriors when test
support compatible & estimates uniform enough. Include both cases to use RG10
OPE at this contract and allow conversion and uniqueness without Riemann
limits inside RG11. Point x in conf n; compact Test n; choose centers in
Reproductions. -/
def Design (n:ℕ) := (conf n) ⊕ Test n -- use CoeSort? Set conf

namespace Design
def selects (u:Design n): Set (Points n):=match u with | Sum.inl p=>{p.val} | Sum.inr p=>tsupport p
 theorem closed (u:Design n): IsCompact (u.selects):=by cases u with|inl p=> exact isCompact_singleton|inr p=>exact p.hasCompactSupport
 theorem sets (u:Design n): u.selects ⊆ conf _:=by cases u with|inl p=> exact singleton_subset_iff.mpr p.property|inr p=>exact p.tsupport_subset

/-- Normalize by Jacobians in positioned Test if performing that form of
sampling; here evaluate *relative f then driven positions* directly. -/
def scoop (f:Test n)(t:ℝ)(y:Tail m)(h:∀ x∈tsupport f,driven t x y∈conf (n+m)): leverage (n+m) where
   toFun K:= f.applyTo (fun x=> K.val (driven t x y))
   map_add' K L:= by
     change (∫ x,f x*(K.val (driven t x y)+L.val _))= (∫ _,_) + ∫ _,_
     simp_rw [mul_add]
     have he (u:clean (n+m)):Integrable (fun x=> f x*u.val (driven t x y)):=by
       refine Continuous.integrable_of_hasCompactSupport (continuous_iff_continuousAt.mpr (fun x=>?_)) f.hasCompactSupport.mul_right
       by_cases hv: x∈tsupport f
       · refine f.continuous.continuousAt.mul ((u.property.1.continuousOn.continuousAt ((conf_open _).mem_nhds (h x hv))).comp (f:=fun i:Points n=>driven t i y) ?_)
         exact ((smooth_driving y).comp (continuous_const.prodMk continuous_id)).continuousAt
       apply continuousAt_const.congr (f:=fun _:Points n=> (0:ℂ))
       filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hv] with x hx; simp [hx]
     exact integral_add (he K) (he L)
   map_smul' z K:= by
     change (∫ x, f x*(z*K.val (driven t x y)))=z* ∫ _,_
     simp_rw [mul_left_comm _ z,integral_const_mul]

def taps (x:Design n)(t:ℝ)(y:Tail m):leverage (n+m):=match x with
 | Sum.inl p=> here (driven t p.val y)
 | Sum.inr p=> if h:∀w∈tsupport p,driven t w y∈conf _ then scoop p t y h else (0:leverage (n+m))

 theorem scoop_at (f:Test n)(t:ℝ)(y:Tail m)(h:∀ x∈tsupport f,driven t x y∈conf (n+m))(K:Points (n+m)→ℂ)(H:ContDiffOn ℝ ∞ K (conf (n+m))):
   scoop f t y h (dress K H)= f.applyTo (fun x=>K (driven t x y)):=by
   unfold scoop dress Test.applyTo; dsimp; refine integral_congr_ae (Eventually.of_forall (fun x=>?_))
   dsimp only
   by_cases hx: x∈tsupport f
   · rw [indicator_of_mem (h _ hx)]
   rw [image_eq_zero_of_notMem_tsupport hx,zero_mul,zero_mul]

 -- supports and domain eventually along t=exp(-u)
 theorem arial (x:Design n)(y:Tail m):∀ᶠ u:ℝ in atTop,∀ w∈x.selects,driven (Real.exp (-u)) w y∈conf _:=isolates (x.closed) (x.sets) y
end Design

/-- For kernel-integrated representation can expose coherence first. d0 may use free arbitrary kernel. -/
def Profiled (A:ShapeReport G F)(d k n:ℕ):Prop:=
  ∀ z:sheaf F n d,∃ K:Points n→ℂ,∃ _:ContDiffOn ℝ ∞ K (conf n),∀ f:Test n,A.table k d n f ((tower F d).b ∘ z)=f.applyTo K

def Metered (A:ShapeReport G F):Prop:=∀ d k n,Profiled A d k n

 theorem link_integrates (A:ShapeReport G F)(d e k:ℕ)(i:sheaf F n d)(j:sheaf F m e)(p:leverage (n+m))
    (K: Points (n+m)→ℂ)(h:ContDiffOn ℝ ∞ K (conf _))(hi : ∀ f:Test (n+m),
        A.table k (max d e) _ f ((tower F (max d e)).b ∘ Fin.append (rise F (le_max_left d e) ∘ i) (rise F (le_max_right d e) ∘ j))=f.applyTo K):
    coeff k (link A d e p i j)=p (dress K h):= RG11.Stress.survey_integrated A _ _ _ _ h hi
end YM.RG11.Neighborhood
