import YM.OPE.Compatible.Lumen.Mush
/-!
# Independent channels, Wick signal summaries. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Flock
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Cascade
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace
variable {G:Gauge}{n:Side}
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency
open PertExtension Series Asymptotics GaussianScore Radial Finset List
variable {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable [NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]
abbrev dotV (l:List (Dual' E))(i:E):ℝ:= (l.map (fun k=>k i)).prod
omit [FiniteDimensional ℝ E] in lemma dot_cons (c:Dual' E)(l:List (Dual' E)): dotV (c::l)=(fun x=>c x)*dotV l:= funext fun i=>by simp only [dotV,List.map_cons,List.prod_cons,Pi.mul_apply]
omit [FiniteDimensional ℝ E] in lemma dot_rake (l q:List (Dual' E)): dotV (l++q)= dotV l*dotV q:= funext fun i=> by simp [dotV]
omit [FiniteDimensional ℝ E] in lemma bonded (l:List (Dual' E)): Bond (dotV l):=by induction l with
    | nil=> exact Bond.keep 1
    | cons l k h=> rw [dot_cons]; exact (Bond.glyph l).mul h
-- hook closure by generators
structure Quilting (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] (g:(E→ℝ)→ Prop):Prop where
    stamps (d:List (Dual' E)): g (dotV d)
    scope (f:E→ℝ)(hf: Bond f)(he:g f)(c:ℝ): g (c • f)
    folds (f a:E→ℝ)(hf:Bond f)(ha:Bond a)(he:g f)(hx:g a): g (f+a)
namespace Quilting
variable {g:(E→ℝ)→ Prop}
lemma everything (p: Quilting E g)(f:E→ℝ)(h:Bond f): g f:=by
    -- induction append via multipliers
    let cap(f:E→ℝ) := ∀ d:List (Dual' E),g (f*dotV d); -- ih might not allow cross multiplication. generalize p
    induction h generalizing g with
    | keep x=>
       convert! p.scope (dotV []) (bonded _) (p.stamps _) x using 1; ext i; simp [dotV]
    | glyph y=>
       convert p.stamps [y] using 1; funext i; simp [dotV]
    | add hf he ih hp=> exact p.folds _ _ hf he (ih p) (hp p)
    | @mul f a h h' ih ih'=>
       apply ih (g:=fun i=> g (i*a)); refine ⟨fun s=>?_,fun i H hp c=>?_,fun u v he hr ht hx=>?_⟩
       · apply ih' (g:=fun A=>g (dotV s*A)); exact {
             stamps := fun t=>by rw [←dot_rake]; exact p.stamps (s++t)
             scope :=fun j hj he c=> by rw [mul_smul_comm]; exact p.scope _ ((bonded s).mul hj) he _
             folds :=fun i j h H hp hq=>by rw [mul_add]; exact p.folds _ _ ((bonded s).mul h) ((bonded s).mul H) hp hq }
       · rw [smul_mul_assoc]; exact p.scope _ (H.mul h') hp c
       rw [add_mul]; exact p.folds _ _ (he.mul h') (hr.mul h') ht hx
end Quilting
variable [MeasurableSpace E][BorelSpace E](μ: Measure E)[μ.HasTemperateGrowth]
variable (A:Law E)
lemma lumpZ (R:Law E)(p:E→ℝ)(h:Bond p) : Integrable (p * R.kern) μ:= R.integrable_entry μ h.cost h.smooth.continuous
omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.HasTemperateGrowth] in
lemma scooted (c:ℝ)(x:E→ℝ): A.average μ (c • x)=c*A.average μ x:=by
     unfold Law.average; rw [smul_mul_assoc]; simp only [Pi.smul_apply,integral_const_mul,smul_eq_mul];ring -- notation? ring
lemma sun {u v:E→ℝ}(h:Bond u)(k:Bond v) : A.average μ (u+v)=A.average μ u+A.average μ v:=by
      unfold Law.average; rw [add_mul]; simp only [Pi.add_apply]; rw [integral_add (lumpZ μ A u h) (lumpZ μ A v k),add_div]
variable [NeZero μ]
lemma singleConst (k:ℝ): A.average μ (fun _=> k)=k := by rw [show (fun _=>k)=(k• (1:E→ℝ)) from funext fun i=>by simp,scooted,A.empty]; simp
-- reindex sum recursion concentrated
variable [μ.IsAddRightInvariant]
variable {ι:Type}
omit [NeZero μ] in lemma slopeTest (ℓ:ι→Dual' E)(s:Finset ι)(i) (hi:i ∉ s): A.average μ (Law.product ℓ (insert i s)) = ∑ j∈s, A.average μ (Law.product ℓ (s.erase j))*A.wick (ℓ i) (ℓ j):=by
      rw [show Law.product ℓ (insert i s)=(fun x=>Law.product ℓ s x*ℓ i x) from funext fun x=>by unfold Law.product; rw [prod_insert hi,mul_comm],Law.recursion]
end YM.OPE.Libra.Flock
