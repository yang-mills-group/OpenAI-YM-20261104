import YM.AllOrder.Fire.Basis
/-! # Differentials on price-valid polynomial tests -/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Fire
open Function Finset Laplace.SigmaP PositionX.Jet PertExtension PertExtension.Series PositionX.Gauss Radial MeasureTheory Response
open scoped Topology ContDiff BigOperators Classical
variable {Y X:Type} [NormedAddCommGroup X][NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
local notation "Ω"=>X×Y
open GaussianScore
variable [FiniteDimensional ℝ X][FiniteDimensional ℝ Y] {a b:X}{f g:X→ℝ}
lemma licensed (h:ContDiffAt ℝ ω f a) (b:X) : diff' b f a= someJ (fun t:ℝ=> f (a+t • b)) 1:= by
   let F (t:ℝ):= a+t•b; have hp:F 0=a:=by simp [F]
   rw [voyage]; symm
   exact ((show HasFDerivAt f (fderiv ℝ f a) (F 0) from ((by rw [hp]; exact (h.differentiableAt (by simp)).hasFDerivAt))).comp_hasDerivAt 0 (show HasDerivAt F b 0 from (by unfold F; simpa using! (((hasDerivAt_id' (0:ℝ)).smul_const b).const_add a)))).deriv
lemma adds (h:Plausible f)(H:Plausible g)(v:X): diff' v (f+g)=diff' v f+diff' v g := funext fun i=> (congr_arg (fun A:X→L[ℝ] ℝ=>A v) (fderiv_add (h.smooth.differentiable (by simp) i) (H.smooth.differentiable (by simp) i)))
lemma mults (h:Plausible f)(H:Plausible g)(v:X): diff' v (f*g)=diff' v f*g+f*diff' v g:= by ext p; rw [diff',fderiv_mul (h.smooth.differentiable (by simp) p) (H.smooth.differentiable (by simp) p)]; simp only [_root_.smul_apply,_root_.add_apply,smul_eq_mul]; change _= fderiv ℝ f p v *g p+ f p*fderiv ℝ g p v; ring
lemma scalars (h:Plausible f)(c:ℝ)(v:X): diff' v (c• f)= c• diff' v f:= by ext x; rw [diff', fderiv_const_smul (𝕜:=ℝ)]; rfl; exact h.smooth.differentiable (by simp) _
lemma dift (c:ℝ)(x:X): diff' x (fun _=> c)=0:= by ext t; simp [diff']
lemma tout {ι : Type*} {f:ι→X→ℝ}(s:Finset ι)(h:∀ i∈s,Plausible (f i))(v:X): diff' v (∑ i∈s,f i) = ∑ i∈s,diff' v (f i):= by induction s using Finset.induction_on with
   | empty=> simp only [Finset.sum_empty]; exact dift ..
   | insert a s hi ih=> have hf:= fun i hx=> h i (mem_insert_of_mem hx); rw [sum_insert hi,sum_insert hi,adds (h a (mem_insert_self ..)) (Plausible.sum hf), ih hf]
lemma pays (h:Plausible f)(x v y:X): diff' v (diff' y f) x=fderiv ℝ (fderiv ℝ f) x v y:= by
   let L:=ContinuousLinearMap.apply ℝ ℝ y; change fderiv ℝ (L ∘ fderiv ℝ f) x v=_; rw [fderiv_comp x L.differentiableAt (((h.smooth.fderiv_right (m:=ω) (by simp)).differentiable (by simp) _)),L.fderiv]; rfl
lemma order (h:Plausible f)(v w:X): diff' v (diff' w f)=diff' w (diff' v f) := by funext i; simp_rw [pays h]; exact h.smooth.contDiffAt.isSymmSndFDerivAt le_top|>.eq ..
variable [MeasurableSpace Y][BorelSpace Y](A: Law Y)(μ:Measure Y)[μ.IsAddHaarMeasure] {u:X×Y→ℝ} -- add μ attrs
lemma diff_bound (h:Plausible u)(v x:X): diff' v (bound A μ u) x=A.average μ (fun z=> diff' (v,0) u (x,z)):= by
   let F(t:ℝ):=x+t • v; have hF: ContDiffAt ℝ ω F 0:=by unfold F; fun_prop
   rw [licensed (smooth_bind _ _ h).smooth.contDiffAt]; change someJ ((bound A μ u) ∘ F) 1=_; rw [← show A.average μ (fun z=> someJ (fun t:ℝ=>u (F t,z)) 1)= _ from (transport_p _ _ hF h 1).2]; congr! 1; ext1 z; rw [licensed h.smooth.contDiffAt]; simp [F] -- (x,z)+(t..)
end YM.AllOrder.Fire
