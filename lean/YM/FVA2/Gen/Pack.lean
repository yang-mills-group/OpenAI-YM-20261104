import YM.Work.G02
/-!
 # Classical comparison helpers: smooth compact-interval dependence

 Differentiation in parameters of real smooth fields in our Wilson-to-MS
 prescription. Keep unit interval actual integration domain.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Gen
open Function Filter Set Metric MeasureTheory Asymptotics
open scoped Topology ContDiff Interval BigOperators Classical
variable {E F X:Type} [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
variable [NormedAddCommGroup X][NormedSpace ℝ X]
local notation "Δ₁"=> unitInterval
local notation "∆"=>Δ₁
section
variable {T: Type}[TopologicalSpace T][CompactSpace T]
local notation "D"=> E→L[ℝ] F
private def blender (f:C(T,E→L[ℝ] F)) : E→L[ℝ]C(T,F):= by
    let L:E→ₗ[ℝ] C(T,F):={ toFun x:= ⟨fun t=> f t x, (f.continuous).clm_apply continuous_const⟩, map_add':=fun a b=> ContinuousMap.ext (fun i=>map_add (f i) a b),map_smul':=fun a b=>ContinuousMap.ext (fun i=>map_smul (f i) a b) }
    refine L.mkContinuous ‖f‖ (fun x=> (ContinuousMap.norm_le (L x) (by positivity)).mpr ?_); intro i; exact (( f i ).le_opNorm x).trans (mul_le_mul_of_nonneg_right ( f.norm_coe_le_norm i ) (norm_nonneg x))
lemma blender_p (f:C(T,E→L[ℝ] F)) (x:E)(t:T): blender f x t= f t x:=rfl
def mixing : C(T,E→L[ℝ] F)→L[ℝ] E→L[ℝ] C(T,F):= by
    let K:C(T,D)→ₗ[ℝ] E→L[ℝ] C(T,F):= { toFun f:=blender f, map_add':=fun a b=>ContinuousLinearMap.ext (fun x=> ContinuousMap.ext (fun t=>rfl)),map_smul':=fun a b=>ContinuousLinearMap.ext (fun x=>ContinuousMap.ext (fun t=>rfl)) }
    refine LinearMap.mkContinuous (E:=C(T,D)) (F:=E→L[ℝ] C(T,F)) K 1 (fun f=>?_); rw [one_mul]; apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f); intro p; refine (ContinuousMap.norm_le _ (by positivity)).mpr (fun i=>?_); rw [show K f p i=_ from blender_p f p i]; exact (( f i ).le_opNorm p).trans (mul_le_mul_of_nonneg_right ( f.norm_coe_le_norm i ) (norm_nonneg _))
lemma mix_formula (f:C(T,E→L[ℝ] F)) (p:E)(i:T): mixing f p i=f i p:=rfl
variable {p:E→ C(T,F)} {q:E→C(T,E→L[ℝ] F)}
lemma channels (h: Continuous q)(hp: ∀ (x:E)(t:T), HasFDerivAt (fun y=> p y t) ( q x t ) x)(z:E): HasFDerivAt p (mixing (q z)) z:= by
    rw [hasFDerivAt_iff_isLittleO,isLittleO_iff]; intro c hc; obtain ⟨r,hr,H⟩:= Metric.mem_nhds_iff.mp ( h.continuousAt.eventually ( ball_mem_nhds (q z) hc )); filter_upwards [ball_mem_nhds z hr] with x hx; apply (ContinuousMap.norm_le _ (by positivity)).mpr; intro t; let f y:= p y t; change ‖ f x- f z- q z t (x-z)‖ ≤ _; apply (convex_ball z r).norm_image_sub_le_of_norm_hasFDerivWithin_le' (s:=ball z r) (f':=fun y=>q y t) ?_ ?_ (mem_ball_self hr) hx;
    · intro x hx; exact (hp x t).hasFDerivWithinAt
    intro x hx; have ht:‖q x-q z‖ ≤ c:= lt_of_le_of_lt (le_of_eq (dist_eq_norm (q x) (q z)).symm) ( H hx )|>.le
    exact (ContinuousMap.norm_le _ hc.le).mp ht t
variable (h:T→ X)(hp:Continuous h) (f:E×X → F)(hu:ContDiff ℝ ∞ f)
-- parameter height, in unit interval (more general compacts)
def packing (t:T→X)(ht:Continuous t)(f:E×X→ F)(hu:Continuous f): E→ C(T,F):= ( ContinuousMap.curry (⟨fun p:E×T=> f (p.1,t p.2), hu.comp (Continuous.prodMk continuous_fst (ht.comp continuous_snd))⟩: C(E×T,F)) )
omit [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ X] [CompactSpace T] in
lemma packed (t:T→X)(ht:Continuous t)(f:E×X→ F)(hu:Continuous f) : Continuous ( packing t ht f hu ):= ContinuousMap.continuous _
def upper (f:E×X→F) (p:E×X): E→L[ℝ] F:= ( fderiv ℝ f p ).comp ( ContinuousLinearMap.inl ℝ E X )
include hu
lemma upper_level: ContDiff ℝ ∞ (upper f):= (hu.fderiv_right le_rfl).clm_comp contDiff_const
lemma upperF (x:E)(y:X) : HasFDerivAt (fun p=> f (p,y)) (upper f (x,y)) x:= ( hu.differentiable (by simp) _ |>.hasFDerivAt).comp (f:=fun p:E=>(p,y)) x ( HasFDerivAt.prodMk ( hasFDerivAt_id x ) (hasFDerivAt_const y x))
lemma credits (i:E): HasFDerivAt (packing h hp f hu.continuous) (mixing (packing h hp (upper f) (upper_level f hu).continuous i)) i:= channels (packed _ _ _ ( upper_level f hu ).continuous ) (fun x i=> upperF f hu x (h i)) i -- dots fix
lemma interlinks (n:ℕ): ContDiff ℝ n (packing h hp f hu.continuous):=by
    induction n generalizing F with| zero=> exact contDiff_zero.mpr ( packed h hp f hu.continuous )| succ n ih=> rw [Nat.cast_add_one, contDiff_succ_iff_hasFDerivAt]; refine ⟨ fun x=> (mixing ( E:=E ) ( F:=F ) ( T:=T )) (packing h hp (upper f) (upper_level f hu).continuous x), ?_, credits h hp f hu ⟩; exact ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=C(T,E→L[ℝ] F)) (mixing ( F:=F ) ( E:=E ) ( T:=T ))|>.comp ( ih ( F:=E→L[ℝ] F ) (upper f) ( upper_level f hu ) )
-- full∞
theorem packages : ContDiff ℝ ∞ (packing h hp f hu.continuous):= contDiff_of_differentiable_iteratedFDeriv (fun m hm=> show Differentiable _ _ from (( interlinks (E:=E) (F:=F) h hp f hu (m+1)).differentiable_iteratedFDeriv (m:=m) (by exact_mod_cast m.lt_succ_self))) -- codomain issue universe induction
-- point derivative get via eval.P statements.
end
end YM.FVA2.Gen
