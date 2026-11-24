import YM.Maxwell.Exterior

/-!
# Four-spacetime actual differential operator inputs

Use the same spacetime E4, Euclidean basis, group, connection and physical
color normalization as `Labels`, `Maxwell` (in particular `G.Color`, not
G.Mat with its Frobenius norm). Local continuum operators will be tested on
all smooth connections on the trivial bundle on E4. All identities below
are actually pointwise. No MS dimensional continuation or EOM projection
in this layer.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.Continuum
open Maxwell
open scoped ContDiff

variable {X E F H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Lift a finite-dimensional bilinear map to the CLM calculus. -/
def bc [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (B : E →ₗ[ℝ] F →ₗ[ℝ] H) : E →L[ℝ] F →L[ℝ] H :=
  (LinearMap.toContinuousLinearMap.toLinearMap.comp B).toContinuousLinearMap

@[simp] lemma bc_at [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (B:E →ₗ[ℝ] F →ₗ[ℝ] H)(e f): bc B e f=B e f := rfl

lemma linear_smooth [FiniteDimensional ℝ E] (L:E →ₗ[ℝ] H) {a:X→E}
    (ha:ContDiff ℝ ∞ a) : ContDiff ℝ ∞ (fun x=>L (a x)) := L.toContinuousLinearMap.contDiff.comp ha

lemma bilinear_smooth [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (B:E →ₗ[ℝ] F →ₗ[ℝ] H) {a:X→E}{b:X→F}(ha:ContDiff ℝ ∞ a)(hb:ContDiff ℝ ∞ b):
    ContDiff ℝ ∞ (fun x=>B (a x) (b x)) := ((bc B).contDiff.comp ha).clm_apply hb

lemma d_linear [FiniteDimensional ℝ E] (L:E →ₗ[ℝ] H) (v:X) {a:X→E} (ha:ContDiff ℝ ∞ a):
    Analysis.D v (fun x=>L (a x)) = fun x=>L (Analysis.D v a x) := by
  funext x
  exact congr_arg (fun k : X→L[ℝ] H => k v) ((L.toContinuousLinearMap.hasFDerivAt.comp x
    ((ha.differentiable (by simp)).differentiableAt.hasFDerivAt)).fderiv)

lemma d_bilinear [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (B:E →ₗ[ℝ] F →ₗ[ℝ] H)(v:X) {a:X→E}{b:X→F}(ha:ContDiff ℝ ∞ a)(hb:ContDiff ℝ ∞ b):
    Analysis.D v (fun x=>B (a x) (b x)) = fun x=>B (Analysis.D v a x) (b x)+B (a x) (Analysis.D v b x) := by
  funext x
  let L := bc B
  have he := L.hasFDerivAt.comp x ((ha.differentiable (by simp) x).hasFDerivAt)
  have hh := (he.clm_apply ((hb.differentiable (by simp) x).hasFDerivAt)).fderiv
  change fderiv ℝ (fun y=> (L ∘ a) y (b y)) x v = _
  rw [hh]
  change B (a x) (fderiv ℝ b x v) + B (fderiv ℝ a x v) (b x) = _
  rw [Analysis.D,Analysis.D,add_comm]

lemma grad_preserves (i:Axis){f:E4→F}(hf:ContDiff ℝ ∞ f): ContDiff ℝ ∞ (grad i f) :=
  contDiff_iff_contDiffAt.mpr fun x => grad_smooth i hf.contDiffAt (by simp)

lemma grad_plus (i:Axis){f g:E4→F}(hf:ContDiff ℝ ∞ f)(hg:ContDiff ℝ ∞ g):
    grad i (f+g)=grad i f + grad i g := by
  funext x
  rw [grad,Analysis.D,fderiv_add (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
  rfl

lemma grad_minus (i:Axis)(f:E4→F): grad i (-f) = -(grad i f) := by
  funext x; rw [grad,Analysis.D,fderiv_neg]; rfl

lemma grad_diff (i:Axis){f g:E4→F}(hf:ContDiff ℝ ∞ f)(hg:ContDiff ℝ ∞ g):
    grad i (f-g)=grad i f - grad i g := by rw [sub_eq_add_neg f,grad_plus (g := -g) i hf hg.neg,grad_minus,sub_eq_add_neg]

lemma grad_scale (i:Axis)(t:ℝ){f:E4→F}(hf:ContDiff ℝ ∞ f):
    grad i (t • f)=t • grad i f := by
  funext x; rw [grad,Analysis.D,fderiv_const_smul (hf.differentiable (by simp) x)]; rfl

lemma grad_collect {ι:Type*}(s:Finset ι){f:ι→ E4→F}(hf:∀j∈s,ContDiff ℝ ∞ (f j))(i:Axis):
    grad i (∑ j∈s, f j) = ∑ j∈s,grad i (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => funext x; simp [grad,Analysis.D,Pi.zero_def]
  | insert j s hj ih =>
    have hx: ContDiff ℝ ∞ (∑ k∈s,f k) := by
      simpa [← Finset.sum_apply] using! (ContDiff.sum (s:=s) (f:=f) fun k hk => hf k (Finset.mem_insert_of_mem hk))
    rw [Finset.sum_insert hj,Finset.sum_insert hj,grad_plus i (hf j (Finset.mem_insert_self j s))
        hx,ih (fun k hk=>hf k (Finset.mem_insert_of_mem hk))]

end YM.RG06.Continuum
