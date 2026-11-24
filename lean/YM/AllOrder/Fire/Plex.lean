import YM.AllOrder.Fire.Box
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Fire
open Function Finset Laplace.SigmaP PositionX.Jet PertExtension PertExtension.Series PositionX.Gauss Radial MeasureTheory Response Module
open scoped Topology ContDiff BigOperators Classical
variable {Y X:Type} [NormedAddCommGroup X][NormedSpace ℝ X] [NormedAddCommGroup Y][NormedSpace ℝ Y]
section vary
variable [FiniteDimensional ℝ X] {f g:ℝ×X→ℝ} {n k:ℕ} {w : X→ℝ}
def view (x:X)(f:ℝ×X→ℝ)(t:ℝ):= f (t,x)
def beam (f:ℝ×X→ℝ)(m:ℕ)(x:X):= someJ (view x f) m
omit [FiniteDimensional ℝ X] in
lemma loc_beam [FiniteDimensional ℝ X]  (x:X) (h:Plausible f) : Plausible (view x f):= by
   have hh:= nearStep (p:=((0:ℝ),x)) (B:=LinearMap.inl ℝ ℝ X) h; simpa [view] using! hh
lemma has_time (t:ℝ×X) (h:Plausible f) : diff' ((1:ℝ),(0:X)) f t= deriv (view t.2 f) t.1:= by
   unfold view; symm; have ht(x):=h.smooth.differentiable (by simp) x
   exact (((show HasFDerivAt f (fderiv ℝ f t) (t.1,t.2) from (ht t).hasFDerivAt)).comp_hasDerivAt t.1 ( (hasDerivAt_id t.1).prodMk (hasDerivAt_const t.1 t.2))).deriv -- order const
lemma beam_step (f:ℝ×X→ℝ)(h:Plausible f) (n:ℕ): beam f (n+1)= ((n+1:ℕ):ℝ)⁻¹ • (beam (diff' ((1:ℝ),(0:X)) f) n):= by
 ext1 x; have he : view x (diff' ((1:ℝ),(0:X)) f)= deriv (view x f):= funext fun t=>has_time _ h; simp only [beam, he, someJ, iteratedDeriv_succ', smul_eq_mul, Pi.smul_apply]; rw [Nat.factorial_succ]; push_cast; field_simp
lemma restrict_ds (x:X) (h:Plausible f): diff' x (fun y=> f (0,y))=fun y=> diff' (foot x) f (0,y):= by
 ext1 y; unfold diff'; let L:= ContinuousLinearMap.inr ℝ ℝ X; change fderiv ℝ (f ∘ L) y _=_; rw [fderiv_comp y (h.smooth.differentiable (by simp) _) L.differentiableAt,L.fderiv]; rfl
lemma lighted (h:Plausible f)(n:ℕ): Plausible (beam f n):= by
 induction n generalizing f with
 | zero=> unfold beam; simp only [someJ_zero]; exact h.app (LinearMap.inr ℝ ℝ X)
 | succ k ih=> rw [beam_step _ h]; exact (ih (h.ds _)).scale _
lemma along (x:X) (h:Plausible f) (n:ℕ):diff' x (beam f n)=beam (diff' (foot x) f) n := by
 induction n generalizing f with
 | zero=> rw [show beam f 0=(fun x=>f (0,x)) from funext (fun x=> someJ_zero _), show beam (diff' (foot x) f) 0=(fun y=> diff' (foot x) f (0,y)) from funext (fun x=> someJ_zero _)]; exact restrict_ds x h
 | succ n ih=> rw [beam_step _ h,scalars (lighted (h.ds _) n),ih (h.ds _), beam_step _ (h.ds _),Fire.order h]
lemma beam_sum {ι:Type} (s:Finset ι){f:ι→ℝ×X→ℝ}(h:∀ i∈s,Plausible (f i))(n:ℕ):beam (∑ i∈s,f i) n=∑ i∈s, beam (f i) n:=by
   ext1 x; rw [beam,Finset.sum_apply]; have he:view x (∑ i∈s,f i)= ∑ i∈s,view x (f i):=by ext1 u; unfold view;rw [Finset.sum_apply,Finset.sum_apply]
   rw [he]; rw [(exact_sum (F:=fun i=> view x (f i)) s (fun i hi=>eo_Act n (loc_beam x (h i hi)).smooth.contDiffAt)).writes n le_rfl,Finset.sum_apply]; rfl
lemma beam_add (h:Plausible f)(H:Plausible g)(i:ℕ):beam (f+g) i=beam f i+beam g i:=funext fun x=> congr_fun (some_add (loc_beam x h).smooth.contDiffAt (loc_beam x H).smooth.contDiffAt) i
lemma beam_mul (h:Plausible f)(H:Plausible g)(i:ℕ):beam (f*g) i=alters (beam f) (beam g) i:= funext fun x=> congr_fun (some_mul (loc_beam x h).smooth.contDiffAt (loc_beam x H).smooth.contDiffAt) i
end vary
end YM.AllOrder.Fire
