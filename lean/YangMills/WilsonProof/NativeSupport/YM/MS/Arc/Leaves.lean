import YM.MS.Arc.Leaves
import YM.MS.Arc.Terrain
import YangMills.WilsonProof.NativeSupport.YM.MS.Heat.Park
/-!
# Radial recurrence (pairs of auxiliary dimensions)

This version starts with even functions of radial r (not square).
 Its integral representation gives smooth control at all r=0, repeated.
 Implement `R1 f`, `even` on mixed external momenta. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Arc
open Function Filter Set Finset MeasureTheory Real
open scoped Topology ContDiff Interval
open ContinuousLinearMap
variable {I E F G: Type}[NormedAddCommGroup E][NormedSpace ℝ E]
 [NormedAddCommGroup F][NormedSpace ℝ F][CompleteSpace F][NormedAddCommGroup G][NormedSpace ℝ G]
def Reflect (f:Tree E F): Prop:= ∀ (x:ℝ) y, f (-x,y)=f (x,y)
-- no 1/2 factor in chop
variable {f:Tree E F}
omit [CompleteSpace F] in
lemma dr (h: ContDiff ℝ ∞ f) (w:E) (s:ℝ) : HasDerivAt (fun i=>f (i,w)) (d f (s,w)) s:= by
   exact (h.differentiable (by simp) _|>.hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id' ..).prodMk (hasDerivAt_const ..)))
omit [CompleteSpace F] in
lemma fresh (h: ContDiff ℝ ∞ f): ContDiff ℝ ∞ (d f):=(apply ℝ F ((1,0):ℝ×E)).contDiff.comp ((contDiff_infty_iff_fderiv.mp h).2)
lemma c_chop (h: ContDiff ℝ ∞ f): ContDiff ℝ ∞ (chop f):= by
   let Z (p:ℝ×(ℝ×E)):= (p.1*p.2.1,p.2.2); have he:=fresh (fresh h); obtain ht:= Heat.Lot (volume.restrict (Ioc (0:ℝ) 1)) (show Heat.Cour _ from ⟨Icc 0 1,isCompact_Icc, (ae_restrict_mem measurableSet_Ioc).mono fun p hp=> Ioc_subset_Icc_self hp⟩) (he.comp (show ContDiff ℝ ∞ Z from by unfold Z; fun_prop)) -- instances? API inspect
   unfold chop; simp_rw [intervalIntegral.integral_of_le zero_le_one]; exact ht.contDiff
lemma raw_chop (h: ContDiff ℝ ∞ f)(x:ℝ)(p:E): x • (chop f (x,p))= d f (x,p) -d f (0,p):= by
   rw [chop,← intervalIntegral.integral_smul]; have hF : ∀ y ∈ uIcc (0:ℝ) 1, HasDerivAt (fun z:ℝ=>d f (z*x,p)) (x • d (d f) (y*x,p)) y:= ?_
   · simpa only [zero_mul,one_mul] using intervalIntegral.integral_eq_sub_of_hasDerivAt hF ((continuous_const.smul ((fresh (fresh h)).continuous.comp (show Continuous (fun t:ℝ=>(t*x,p)) by fun_prop))).intervalIntegrable 0 1)
   · intro y hy; have he: HasDerivAt (fun z:ℝ=>z*x) x y:= by
         simpa using (hasDerivAt_id' y).mul_const x
     exact (dr (fresh h) p (y*x)).scomp y he -- endpoint? u

-- reflections derivative
omit [CompleteSpace F] in
lemma d_odd (h:Reflect f)(hv: ContDiff ℝ ∞ f)(x:ℝ)(p:E): d f (-x,p)=-(d f (x,p)):= by
    obtain he:= (dr hv p (-x)).scomp x ( (hasDerivAt_id' x).neg); have hx : (fun i:ℝ=> f (i,p)) ∘ (fun i:ℝ=> -i)=(fun i:ℝ=> f (i,p)):=funext fun r=> h r p; rw [hx] at he -- composition shapes
    simpa using congr_arg Neg.neg (he.unique (dr hv p x))
omit [CompleteSpace F] in
lemma d_zero (h:Reflect f)(hv: ContDiff ℝ ∞ f)(p:E): d f (0,p)=0:= by
   have H : d f (0,p)= -(d f (0,p)):= by simpa only [neg_zero] using d_odd h hv 0 p
   let x:=d f ((0:ℝ),p); have h2 : (2:ℝ) • x=x+x:= two_smul ..; change x=0; refine smul_right_injective F (by norm_num : (2:ℝ)≠0) ?_; dsimp only; rw [smul_zero,h2]; change x= -x at H; nth_rw 1 [H]; simp
lemma restore (h: Reflect f)(hs:ContDiff ℝ ∞ f)(x:ℝ)(p:E): x • chop f (x,p)=d f (x,p):= by rw [raw_chop hs,d_zero h hs,sub_zero]
lemma chop_even (h:Reflect f)(hs: ContDiff ℝ ∞ f): Reflect (chop f):= by
    intro x p; by_cases hx:x=0; simp [hx]; apply smul_right_injective F (neg_ne_zero.mpr hx); dsimp only; rw [restore h hs, neg_smul, restore h hs, d_odd h hs]
end YM.MS.Arc
