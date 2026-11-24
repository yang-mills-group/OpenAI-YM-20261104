import YM.Push.LOOP_COEFFICIENT.LogDet

/-!
# Two-variable differential and determinant on abstract color coordinates

Keep c:X orthonormal frame map; determinant convention frob. Needed for
 total divergence also on site LMs. No torus-volume factor.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Bare.Mix
open Function Set Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius
variable {E X Z I:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Z][NormedSpace ℝ Z]

lemma fstep {V: X→E}(x y:X)(h:DifferentiableAt ℝ V x): HasDerivAt (fun t:ℝ=> V (x+t • y)) (fderiv ℝ V x y) 0:= by
    have he : HasDerivAt (fun t:ℝ=>x+t • y) y 0:= by simpa using! HasDerivAt.const_add x ((hasDerivAt_id' (0:ℝ)).smul_const y)
    exact HasFDerivAt.comp_hasDerivAt_of_eq (f:=fun t:ℝ=> x+t • y) 0 h.hasFDerivAt he (by simp)
variable (F:E→X→Z) (a:E) (x:X)
local notation "H" => uncurry F

lemma part_e (h:DifferentiableAt ℝ H (a,x)): fderiv ℝ (fun v=> F v x) a= fderiv ℝ H (a,x) ∘L ContinuousLinearMap.inl ℝ E X:= (_root_.HasFDerivAt.comp (g:=H) (f:=fun v=> (v,x)) a h.hasFDerivAt (hasFDerivAt_prodMk_left a x)).fderiv
lemma part_x (h:DifferentiableAt ℝ H (a,x)): fderiv ℝ (F a) x=fderiv ℝ H (a,x) ∘L ContinuousLinearMap.inr ℝ E X:= (h.hasFDerivAt.comp x (hasFDerivAt_prodMk_right a x)).fderiv
lemma mixed_clm (e:E) (y:X)(h:ContDiffAt ℝ ω H (a,x)): fderiv ℝ (fun p=> fderiv ℝ (F p) x y) a e= fderiv ℝ (fun t=> fderiv ℝ (fun p=> F p t) a e) x y := by
    let V := fderiv ℝ H (a,x); let W:= fderiv ℝ (fderiv ℝ H) (a,x)
    have he : DifferentiableAt ℝ (fderiv ℝ H) (a,x):= (h.fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)
    have hc := h.eventually (by simp)
    have hj : (fun p=> fderiv ℝ (F p) x y) =ᶠ[𝓝 a] fun p=> fderiv ℝ H (p,x) (0,y):= ((hasFDerivAt_prodMk_left (𝕜:=ℝ) a x).continuousAt.tendsto.eventually hc).mono (fun p hp=> by dsimp only; rw [part_x _ _ _ (hp.differentiableAt (by simp))]; rfl)
    have hh : (fun t=> fderiv ℝ (fun p=> F p t) a e) =ᶠ[𝓝 x] fun t=> fderiv ℝ H (a,t) (e,0):= ((hasFDerivAt_prodMk_right (𝕜:=ℝ) a x).continuousAt.tendsto.eventually hc).mono (fun t ht=> by dsimp only; rw [part_e _ _ _ (ht.differentiableAt (by simp))]; rfl)
    have h1 := ((he.hasFDerivAt.clm_apply (hasFDerivAt_const (0,y) (a,x))).comp (f:=fun v=>(v,x)) (g:=fun z=> fderiv ℝ H z (0,y)) a (hasFDerivAt_prodMk_left (𝕜:=ℝ) a x)).congr_of_eventuallyEq hj
    have h2 := ((he.hasFDerivAt.clm_apply (hasFDerivAt_const (e,0) (a,x))).comp x (hasFDerivAt_prodMk_right a x)).congr_of_eventuallyEq hh
    rw [h1.fderiv,h2.fderiv]; simp only [ContinuousLinearMap.comp_zero,zero_add]
    exact h.isSymmSndFDerivAt_of_omega (e,0) (0,y)
lemma gradright (h:ContDiffAt ℝ ω H (a,x)) : ContDiffAt ℝ ω (fun p=> fderiv ℝ (F p) x) a:= ContDiffAt.fderiv (f:=F) (g:=fun _=>x) h contDiffAt_const (by simp)
lemma cap_mix (e:E) (y:X)(h:ContDiffAt ℝ ω H (a,x)): fderiv ℝ (fun p=> fderiv ℝ (F p) x) a e y=fderiv ℝ (fun t=> fderiv ℝ (fun p=>F p t) a e) x y:= by
    rw [← mixed_clm F a x e y h]
    have hv:= ((gradright F a x h).differentiableAt (by simp)).hasFDerivAt
    rw [(hv.clm_apply (hasFDerivAt_const y a)).fderiv]; simp

-- determinant derivative.
open Matrix
abbrev J (X:Type*)[NormedAddCommGroup X][NormedSpace ℝ X]:= X→L[ℝ] X
variable [Fintype I][DecidableEq I]
def table (b:Module.Basis I ℝ X) : J X→ₗ[ℝ] Matrix I I ℝ:= (LinearMap.toMatrix b b).toLinearMap.comp (ContinuousLinearMap.coeLM ℝ)
def tab (b:Module.Basis I ℝ X)(F:J X) := (table b F).trace
lemma tab_trace (b:Module.Basis I ℝ X)(F:J X): tab b F= ∑ i,b.repr (F (b i)) i := by simp [tab,table, Matrix.trace, LinearMap.toMatrix_apply]
lemma tableau [FiniteDimensional ℝ X](b:Module.Basis I ℝ X)(F:E→J X) (h:ContDiffAt ℝ ω F a)(he:F a=1): ContDiffAt ℝ ω (fun x=> (F x).det) a ∧ ∀ e,fderiv ℝ (fun x=> (F x).det) a e= tab b (fderiv ℝ F a e):= by
    let K := (table b).toContinuousLinearMap; let T := K ∘ F
    have hh V : (K V).det=V.det:= LinearMap.det_toMatrix b _ -- check
    rw [show (fun x=>(F x).det)= Matrix.det ∘ T from funext fun x=>(hh (F x)).symm]
    have hX: T a=1:= by unfold T; rw [Function.comp_apply,he]; exact LinearMap.toMatrix_id b
    have hT : ContDiffAt ℝ ω T a:= K.contDiff.contDiffAt.comp a h
    refine ⟨Push.Loops.det_contDiff.contDiffAt.comp a hT,fun e=>?_⟩
    rw [fderiv_comp a (_root_.ContDiff.differentiable Push.Loops.det_contDiff (by simp) _) (hT.differentiableAt (by simp)),ContinuousLinearMap.comp_apply ,hX]; erw [Push.Loops.det_variation (1:Matrix I I ℝ) (by simp)]; dsimp only [T]; rw [fderiv_comp a K.differentiableAt (h.differentiableAt (by simp))]; erw [K.fderiv]; rw [ContinuousLinearMap.comp_apply]; simp; rfl
end YM.MS.Bare.Mix
