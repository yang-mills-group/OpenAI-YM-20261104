import YM.OPE.Compatible.Loire.Four
/-!
# Cubic source IBP.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Shrew
open Function MeasureTheory Set Topology Metric Filter Libra PertExtension Series GaussianScore Flock
open scoped BigOperators Classical ContDiff
variable {V I:Type}[LinearOrder I]{i j:I}{s:Finset I}
variable [NormedAddCommGroup V][NormedSpace ℝ V][FiniteDimensional ℝ V] [MeasurableSpace V][BorelSpace V]
variable (μ:Measure V)[μ.IsAddHaarMeasure] (L:Law V) (K:I→I→ℝ)(v:I→Module.Dual ℝ V) {f g: V→ℝ}
lemma IP (x:V)(hg:Bond f): L.average μ (⇑(L.P x) * f)= L.average μ (poke x f):=by -- L.P coerces hint
   refine bask μ L x _ _ hg (hg.amount x) ?_; intro a b; refine HasFDerivAt.comp_hasDerivAt b (f:=fun y:ℝ=>a+y • x) (hg.smooth.differentiable (by simp) _|>.hasFDerivAt) ?_; simpa using! ((hasDerivAt_id' b).smul_const x|>.const_add a)
lemma snow (hx:Bond f)(hy:Bond g):L.average μ (f-g)=L.average μ f-L.average μ g:=by rw [sub_eq_add_neg,sun μ L hx hy.neg,show -g=(-1:ℝ) • g from by simp,scooted]; ring
lemma hick (hg:Bond f)(hp: First i s) : L.average μ (fauna K v s*f)= L.average μ (fauna K v (s.erase i)*poke (L.inverse (v i)) f) + ∑ j∈ s.erase i,(L.wick (v i) (v j)-K i j)* L.average μ (fauna K v ((s.erase i).erase j)*f):=by
     let A:= s.erase i; let S:=fauna K v; let q:=L.inverse (v i)
     have he : ∀ (j:I), Bond (S (A.erase j)*f):=fun j=>(incense ..).mul hg; have hh:Bond (S A*poke q f):=(incense ..).mul (hg.amount q)
     rw [pier _ _ hp,sub_mul, mul_assoc, Finset.sum_mul]; simp_rw [smul_mul_assoc]; let g(j:I):= S (A.erase j)*f
     rw [snow μ L ((Bond.glyph _).mul ((incense ..).mul hg)) (rear _ (fun i _=>Bond.scale _ (he i)))]
     rw [show L.average μ (⇑(v i)*(S A*f))= L.average μ (⇑(L.P q)*(S A*f)) from by rw [show L.P q= v i from L.applies _],IP μ L q ((incense ..).mul hg)]; erw [pokeA _ (incense ..) hg,poHer, Finset.sum_mul]; simp_rw [smul_mul_assoc]
     erw [sun μ L (rear _ (fun i _=> Bond.scale _ (he i))) hh, science μ L _ _ (fun i _=> Bond.scale _ (he i)), science μ L _ _ (fun i _=> Bond.scale _ (he i))]; simp_rw [scooted]; change _-_=_+∑ j∈A,(v j q-K i j)*_; simp_rw [sub_mul,Finset.sum_sub_distrib]; abel
lemma bloom_raw (hp:First i s): L.average μ (fauna K v s)=∑ j∈ s.erase i,(L.wick (v i) (v j)-K i j)* L.average μ (fauna K v ((s.erase i).erase j)):=by
    have hh : poke (L.inverse (v i)) (1:V→ℝ)=0:= by funext x;simp[poke]
    have hv:= hick μ L K v Bond.one hp; simpa only [mul_one,hh,mul_zero,zero_add, show L.average μ 0=0 from singleConst ..] using! hv
end YM.OPE.Shrew
