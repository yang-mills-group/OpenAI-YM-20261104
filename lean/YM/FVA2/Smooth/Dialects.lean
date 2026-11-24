import YM.FVA2.Smooth.Marks
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
/-!
# Differentiate one mark in the `Smooth` calculus

`Steps` counts successive derivatives as ordered lists; `Rides` is the first
derivative relation on such data. Prove combinatorics and analysis for this
gradient rule, including a DCT interchange criterion.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Smooth
open Set Function Filter Finset Metric MeasureTheory Real
open MS MS.Plane MS.Koszul MS.Landau MS.Landau.Detect MS.Heat MS.Tone MS.Latch MS.Latch.Job MS.Rake
open Complex (I)
open scoped Topology ContDiff BigOperators Interval
variable {W E α : Type}
abbrev Draw (W:Type):= W→QP
abbrev Steps (W:Type):= W→List Axis
variable [DecidableEq W]
abbrev hop (v:Steps W)(i:W × Axis): Steps W:= update v i.1 ( i.2 :: v i.1 )
abbrev patch (s:Finset W): Finset ( W × Axis ) := s ×ˢ Finset.univ
lemma hop_other (v:Steps W)(p:W × Axis) {a:W}{s:Finset W}(hs:p.1∉s)(ha:a∈s): hop v p a=v a:= update_of_ne ( Ne.symm (ne_of_mem_of_not_mem ha hs).symm ) .. -- orientation
variable [Fintype W]
local notation "Ι"=> Draw W
local notation "υ"=> Steps W
local notation "ϕ"=> υ→Ι→ℂ
-- allow λ scaling, e.g. travel by constant to reach positive heat scales.
namespace Abroad
open ContinuousLinearMap -- no local classical to avoid DecidableEq W mismatch
variable (r:ℝ) (q:W × Axis)
def spot : Draw W →L[ℝ] ℝ:= r • ((ContinuousLinearMap.proj q.2 : QP →L[ℝ] ℝ ) ∘L (ContinuousLinearMap.proj q.1: Draw W→L[ℝ] QP)) 
def spout : ℂ→L[ℝ] Draw W →L[ℝ]ℂ := smulRightL ℝ _ _ (spot r q)
omit [DecidableEq W] in
lemma seen (t:ℂ)(p:Draw W): spout r q t p= (r * p q.1 q.2) • t:= rfl
def jet (s:Finset W) (v:Steps W)(f: Steps W →ℂ): Draw W→L[ℝ]ℂ:= ∑ i∈ patch s, spout r i ( f (hop v i) )
lemma spray (s:Finset W) (v:Steps W)(f:Steps W→ℂ)(p:Draw W): jet r s v f p= ∑ i∈ patch s,(r*p i.1 i.2) • ( f (hop v i) ) := by simp only [jet,_root_.sum_apply,seen]
lemma ray (s:Finset W)(v:Steps W)(f:Steps W→ℂ)(p:Draw W): jet r s v f p=∑ i∈s,∑ a:Axis, (r*p i a) • f (hop v (i,a)) := by rw [spray]; rw [patch,sum_product]; -- inspect
lemma jet_linear (s:Finset W)(v:Steps W)(f:Steps W→ℂ)(d:ℂ): jet r s v (fun p=>d*f p)=d • jet r s v f:= by
    ext1 q; simp only [spray,_root_.smul_apply,smul_eq_mul, Finset.mul_sum, Complex.real_smul ]; exact Finset.sum_congr rfl fun i _=> mul_left_comm ..
lemma jet_plus (s:Finset W)(v:Steps W)(f h:Steps W→ℂ): jet r s v (f+h) = jet r s v f + jet r s v h:= by simp only [jet,Pi.add_apply,map_add,Finset.sum_add_distrib]
lemma jet_congr (s:Finset W)(v:Steps W){f h:Steps W→ℂ}(he:∀ p∈ patch s,f (hop v p)= h (hop v p)): jet r s v f=jet r s v h:= by apply Finset.sum_congr rfl; intro p hp; rw [he p hp]
variable {r}
end Abroad
open Abroad
variable (r:ℝ) (s:Finset W)(v:Steps W)
/-- At a tag-arity and fixed mark-derivative counts, on all coordinates tangent full. -/
abbrev Rides (f: Steps W→ Draw W→ℂ)(x:Draw W): Prop:= HasFDerivAt ( f v ) ( Abroad.jet r s v (fun p=>f p x)) x
/-- untouched marks can have arbitrary derivative counts. Literally equality of the two evaluated kernels. -/
def held (v:Steps W)(s:Finset W)(f:Steps W→ℂ): Prop:= ∀ q: W × Axis,q∉ patch s→ f (hop v q)=f v
variable {r s v} {p:Draw W}
namespace Rides
variable {f g: Steps W→ Draw W→ℂ}{s' T:Finset W}
lemma add (hf:Rides r s v f p)(hg:Rides r s v g p) : Rides r s v (f+g) p:= by
    unfold Rides; convert! (HasFDerivAt.add hf hg) using 1; apply jet_plus r s v (fun t=>f t p) (fun t=>g t p) -- recursion conflict unqualified
lemma along (hf:Rides r s v f p)(z:ℂ) : Rides r s v (fun t x=>z*f t x) p:= by
    unfold Rides; convert! (HasFDerivAt.const_mul hf z) using 1; apply jet_linear
-- variant for z on right
lemma across (hf:Rides r s v f p)(z:ℂ) : Rides r s v (fun t x=>f t x*z) p:= by simp_rw [mul_comm _ z]; exact hf.along z
lemma zeroS (v:Steps W)(r:ℝ)(s:Finset W)(y:Draw W): Rides r s v 0 y:= by unfold Rides; simp only [jet,Pi.zero_apply,map_zero,Finset.sum_const_zero]; exact hasFDerivAt_const ..
lemma by_zero (hp: (f v)=0)(he:∀ q∈ patch s,f ( hop v q ) p= 0): Rides r s v f p:= by
    unfold Rides; have h0:= Abroad.jet_congr r s v (f:=fun t=> f t p) (h:=0) he; rw [h0,hp]; exact zeroS v r s p -- binder x inferred?
lemma prices (he:Disjoint s s')(hU:T=s∪s')(hf:Rides r s v f p)(hg:Rides r s' v g p)(hF:held v s (fun t=>f t p))(hG:held v s' (fun t=>g t p)): Rides r T v (fun t q=> f t q*g t q) p:= by
    unfold Rides; convert! (HasFDerivAt.mul hf hg) using 1; subst T
    rw [add_comm (f v p • _), ← jet_linear, ← jet_linear]; unfold jet; let k:=patch s; let j:=patch s'; have ht : Disjoint k j:= Finset.disjoint_left.mpr fun _ hl hr=> Finset.disjoint_left.mp he ( mem_product.mp hl ).1 ( mem_product.mp hr ).1;
    simp only; rw [patch,Finset.union_product,sum_union ht]; refine congr_arg₂ (·+·) ( Finset.sum_congr rfl ?_ ) ( Finset.sum_congr rfl ?_ ); -- needs simp only¿
    · intro i hi;  obtain he' : g (hop v i) p=g v p:= hG i ( Finset.disjoint_left.mp ht hi ); rw [he', mul_comm]
    intro i hi; obtain hp: f (hop v i) p=f v p:= hF i ( Finset.disjoint_right.mp ht hi ); rw [hp]
lemma sum (F: α→ Steps W→Draw W→ℂ)(a:Finset α)(he: ∀ i∈a,Rides r s v ( F i ) p): Rides r s v (fun t y=> ∑ i∈a,F i t y) p := by
    unfold Rides; convert! (HasFDerivAt.sum (A:=fun i=>F i v) he) using 1; funext; simp only [Finset.sum_apply]; unfold jet; symm; rw [ Finset.sum_comm ]; simp only [map_sum] -- verify
lemma congr (hf:Rides r s v f p)(hv:g v =ᶠ[𝓝 p] f v)(he:∀ q∈ patch s, g (hop v q) p=f (hop v q) p): Rides r s v g p:= by unfold Rides; rw [ Abroad.jet_congr r s v ( h:= fun t=> f t p ) he ]; exact hf.congr_of_eventuallyEq hv -- check orientation
end Rides
/-- Dominating $y$ function over *all* index slots, independent of positions (or travels).^ℝ -/
def Boxed {β E:Type*}[MeasurableSpace α][NormedAddCommGroup E](μ:Measure α)(f:β→α→E): Prop:= (∀ i, AEStronglyMeasurable ( f i ) μ ) ∧ ∃ h:α→ℝ, Integrable h μ∧∀ᵐ x ∂μ,∀ i, ‖f i x‖≤ h x
variable {β : Type} [MeasurableSpace α]{μ:Measure α} [NormedAddCommGroup E]{H:β→α→ E}
namespace Boxed
lemma earns (hp:Boxed μ H)(i:β): Integrable ( H i ) μ:= by obtain ⟨hS,m,hM,h⟩:=hp; apply hM.mono' (hS _); exact h.mono ( fun t ht=> ht i ) -- mono' requires norm M? check
variable {G J:Type} [NormedAddCommGroup G] {g:β→α→E}
lemma trace [NormedSpace ℝ E][NormedSpace ℝ G](L:E→L[ℝ] G)(h:Boxed μ H) : Boxed μ (fun p t=> L (H p t)):= by
    refine ⟨ fun i=> (( L.integrable_comp (h.earns i))).1,?_ ⟩; obtain ⟨f,hF,h⟩:=h.2; exact ⟨ _,hF.const_mul ‖L‖, h.mono (fun p hp i=> ( L.le_opNorm _ ).trans ( mul_le_mul_of_nonneg_left ( hp i ) ( norm_nonneg _ )))⟩
lemma zeroM (μ:Measure α): Boxed μ ( (0:β→α→E) ) := ⟨ fun _=> aestronglyMeasurable_const, _,integrable_zero α ℝ μ, Eventually.of_forall (fun _ _=> (norm_zero (E:=E)).le)⟩ -- arg E binder
lemma add (hh: Boxed μ H) (he:Boxed μ g): Boxed μ (H+g):= by obtain ⟨h,f,hF,h1⟩:= hh; obtain ⟨h0,g',hg,h2⟩:= he; refine ⟨ fun i=> ( h i ).add (h0 i),f+g', hF.add hg,( h1.and h2 ).mono fun p hp i=> (norm_add_le ..).trans (add_le_add ( hp.1 i ) ( hp.2 i )) ⟩
lemma money (j:Finset J)(F: J→ β→α→ E)(h:∀ i∈j,Boxed μ (F i)): Boxed μ (fun i x=> ∑ p∈j,F p i x):= by
  classical
  suffices Boxed μ ( ∑ p∈j,F p ) by convert! this using 1; funext; simp only [Finset.sum_apply] -- beta reduce pi
  induction j using Finset.induction_on with | empty=> rw [Finset.sum_empty]; exact zeroM μ | @insert x s hx hi=> rw [Finset.sum_insert hx]; exact add (h x (by simp)) (hi (fun i hh=> h i (by simp [hh])))
end Boxed
variable {k: Set (Draw W)}{F: α→ Steps W→Draw W→ℂ}
lemma Rides.money (hu:k∈𝓝 p)(hp:∀ t: Steps W, Boxed μ (fun x a=> F a t x ))(he:∀ᵐ a ∂μ,∀ y∈k, Rides r s v ( F a ) y): Rides r s v (fun t x=> ∫ z,F z t x ∂μ) p:= by
    let J (y: Draw W)(a:α):= jet r s v (fun t=> F a t y)
    let T (i:W×Axis)(x: Draw W)(a:α):= spout r i (F a (hop v i) x)
    have hT(i:W×Axis) : Boxed μ ( T i ):= Boxed.trace _ (hp (hop v i))
    obtain ⟨h,M,hM,hS⟩ := show Boxed μ J from Boxed.money ( patch s ) T ( fun i _=> hT i )
    unfold Rides; dsimp only
    rw [show (jet r s v fun i => ∫ z,F z i p ∂μ)=(∫ z,J p z ∂μ) from ?_];
    · apply hasFDerivAt_integral_of_dominated_of_fderiv_le (F':=J) (F:=fun x a=> F a v x) hu (Eventually.of_forall ((hp v).1)) (( hp v ).earns p) (h p) _ hM he; exact hS.mono (fun x hx y _ => hx y)
    change _= (∫ z, ∑ i∈ patch s,T i p z ∂μ); rw [ integral_finsetSum _ (fun i hi=> (hT i).earns p) ]; exact Finset.sum_congr rfl fun i hi=> (( spout r i ).integral_comp_comm ( φ:=fun a=> F a (hop v i) p ) ((hp (hop v i)).earns p)).symm -- F binder arg likely remove
end YM.FVA2.Smooth
