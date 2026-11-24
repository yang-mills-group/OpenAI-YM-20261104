import YM.OPE.Compatible.Words.Room
/-! # Gaussian differentiations. Finite injectivity rates and all powers
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt
open MeasureTheory Function Finset Filter Module
open scoped Topology BigOperators Classical ContDiff
open PertExtension Series Libra Stranded ScriptJ GaussianScore Flock Radial
variable {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable {I J:Type}[Fintype I]{n k m d:ℕ}
variable [MeasurableSpace E][BorelSpace E](μ:Measure E)[μ.IsAddHaarMeasure](A:Law E)
omit [MeasurableSpace E][BorelSpace E] in
lemma reel (f:ℝ×E→ℝ)(h:Bond f)(x:ℝ): Bond (fun y:E=>deriv (fun t:ℝ=>f (t,y)) x):=by
     have hg:= h.amount ((1:ℝ),(0:E)); have hp:= Shift.leanB _ hg x -- name
     convert hp using 1; funext i; let Q(t:ℝ):=(t,i); have he: HasDerivAt Q (1,0) x:=(hasDerivAt_id' _).prodMk (hasDerivAt_const x _); exact (((h.smooth.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt x he).deriv)
lemma hotrod (f:ℝ×E→ℝ)(h:Bond f)(x:ℝ):HasDerivAt (fun t:ℝ=> A.average μ (fun y=>f (t,y))) (A.average μ (fun y=>deriv (fun t:ℝ=> f (t,y)) x)) x := by
    let W(p:ℝ×E→ℝ)(i:ℝ):= A.average μ (fun y=>p (i,y)); let R(p:ℝ×E→ℝ)(y:E):=deriv (fun t:ℝ=> p (t,y)) x; apply sewn (fun f=>HasDerivAt (W f) (A.average μ (R f)) x) _ _ _ f h
    · intro f g hf hg; have hp: Differentiable ℝ f:= hf.smooth.differentiable (by simp); have he:= (hp x).hasDerivAt.mul_const (A.average μ g); rw [show W (fuseX f g)=f * (fun _=> A.average μ g) from funext fun i=> scooted μ A (f i) g,
            show R (fuseX f g)=deriv f x • g from ?_, scooted]; exact he
      funext y; exact ((hp x).hasDerivAt.mul_const (g y)).deriv
    · intro f hf hp c; let F:=f; rw [show W (c•f)=c • W f from funext fun t=>scooted μ A _ _,show R (c • f)= c • R f from ?_, scooted]; exact hp.const_smul _
      funext y; exact (((ht f hf ..).hasDerivAt).const_smul c).deriv -- helper
    intro f g hf hg hf' hg'; rw [show W (f+g)=W f+W g from funext fun i=> sun μ A (Shift.leanB f hf i) (Shift.leanB g hg i),show R (f+g)=R f+R g from ?_, sun μ A (reel f hf x) (reel g hg x)]; exact hf'.add hg'
    funext y; exact ((ht f hf y x).hasDerivAt.add (ht g hg y x).hasDerivAt).deriv
where ht (p:ℝ×E→ℝ)(h:Bond p)(y:E)(x:ℝ): DifferentiableAt ℝ (fun t:ℝ=> p (t,y)) x:=h.smooth.differentiable (by simp) _|>.comp (f:=fun t:ℝ=>(t,y)) _ (by fun_prop)
-- factors for k
abbrev oval (Z:E→L[ℝ] PAD I)(x:PAD I)(t:ℝ)(p:Pole (PAD I) n)(y:E):=Tensor.diagonal p (x+t • Z y)
abbrev coQ (Z:E→L[ℝ] PAD I)(y:I): Dual' E:= (ContinuousLinearMap.proj y ∘L Z).toLinearMap
abbrev chamber (Z:E→L[ℝ] PAD I): Mat I:= Matrix.of fun i j=> A.wick (coQ Z i) (coQ Z j)
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma ovalQ (Z:E→L[ℝ] PAD I)(x:PAD I)(p:Pole (PAD I) n):Bond fun y:ℝ×E=> oval Z x y.1 p y.2:=by
    apply Bond.multiline (A:=p) (w:=fun _ (y:ℝ×E)=>x+y.1 • Z y.2); intro i l; let k:= l ∘ₗ (Z.toLinearMap ∘ₗ LinearMap.snd ℝ ℝ E); have h := ((Bond.keep (E:=ℝ×E) (l x)).add ((Bond.glyph (LinearMap.fst ℝ ℝ E)).mul (Bond.glyph k))); simp_rw [map_add,map_smul]; exact h
omit [MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ E] in
lemma levied (Z:E→L[ℝ] PAD I)(x:PAD I)(t:ℝ)(p:Pole (PAD I) n):Bond (oval Z x t p):= Shift.leanB _ (ovalQ Z x p) t
-- curvature calculus. hessian capture orbital derivative. 
lemma rayP (v p:PAD I)(t:ℝ)(f:Pole (PAD I) (n+1))(h:Tensor.Sym f): HasDerivAt (fun i:ℝ=> Tensor.diagonal f (v+i • p)) (((n+1:ℕ):ℝ)* ((Tensor.diagonal (f.curryLeft p)) (v+t • p))) t:=by
     have hh:HasDerivAt (fun i:ℝ=>v+i • p) p t:=by simpa using! ((hasDerivAt_id' t).smul_const p).const_add v
     have hv:= ((Tensor.diag_smooth f ⊤).differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt _ hh; convert! hv using 1; rw [Tensor.differential_diagonal _ h, ← Nat.cast_smul_eq_nsmul ℝ];rfl
end YM.OPE.Silt
