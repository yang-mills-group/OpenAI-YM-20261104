import YM.RG06.Rebase.Ray
import YM.RG06.Continuum.Prolongation

/-!
# Homogeneous spatial components of the interacting curvature/EOM constraints

To give a constructive on-shell CLASSICAL polynomial-label comparison, through
any d. No new assumption on `Final`, doesn't say which quantum relations hold
on separated or contact arrays, pre-integration algebra only. Taylor coefficient
`j !` as usual. Homogeneous global smooth components replace a multivariate Taylor
pol implementation for the PDE (we've proved connection-germ/Glyph erasure and matching
with polynomial syntax at all demands already).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.ClassicalOn
open Function Labels Analysis Continuum Tensor
open scoped ContDiff BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace Topology
variable {E F:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
variable {f g:E4→E}{u:E4→F}{k m:ℕ}

structure Level (k:ℕ)(f:E4→E):Prop where
  smooth: Good f
  morph (t:ℝ)(x:E4): f (t • x)= t^k • f x

namespace Level
lemma indicates (h:Level k f) (x:E4): Tensor.diagonal (Tensor.coeff f k 0) x=f x:=by
  unfold Tensor.coeff; simp only [Tensor.diagonal,smul_apply]; rw [show iteratedFDeriv ℝ k f 0 (fun _ : Fin k=>x) = _ from (Rebase.along (k:=k) (x:=0) (y:=x) (f:=f) ((ContDiff.contDiffAt h.smooth).of_le (WithTop.coe_le_coe.mpr le_top))).symm]
  simp only [zero_add,h.morph,iteratedDeriv_smul_const (show ContDiffAt ℝ (k:ℕ) (fun t:ℝ=>t^k) 0 from contDiffAt_id.pow _),iteratedDeriv_fun_pow_zero,if_true]
  rw [smul_smul,inv_mul_cancel₀ (by positivity),one_smul]
lemma indicates_other {j:ℕ}(h:Level k f)(hh:j≠k) (x:E4): Tensor.diagonal (Tensor.coeff f j 0) x=0:=by
  unfold Tensor.coeff; simp only [Tensor.diagonal,smul_apply]; rw [show iteratedFDeriv ℝ j f 0 (fun _ : Fin j=>x)= _ from (Rebase.along (f:=f) (k:=j) (x:=0) (y:=x) ((ContDiff.contDiffAt h.smooth).of_le (WithTop.coe_le_coe.mpr le_top))).symm]
  simp only [zero_add,h.morph,iteratedDeriv_smul_const (show ContDiffAt ℝ (j:ℕ) (fun t:ℝ=>t^k) 0 from contDiffAt_id.pow _),iteratedDeriv_fun_pow_zero,if_neg hh,Nat.cast_zero,zero_smul,smul_zero]
lemma tax (k:ℕ)(h:Tensor.T E4 E k): Level k (diagonal h):=⟨Tensor.diag_smooth _ _,fun _ _=>Tensor.homogeneous ..⟩
lemma const (v:E): Level 0 (fun _=>v):= ⟨contDiff_const,by simp⟩
lemma zero (k:ℕ): Level k (0:E4→E):=⟨contDiff_const,by simp⟩
lemma scale (h:Level k f)(c:ℝ):Level k (c • f):=by
 constructor; exact ContDiff.const_smul c h.smooth
 intro t x; change c • f (t • x)=_; rw [h.morph,smul_comm];rfl
lemma add (hf:Level k f)(hh:Level k g):Level k (f+g):= ⟨ContDiff.add hf.smooth hh.smooth,fun t x => by simp only [Pi.add_apply,hf.morph,hh.morph]; rw [smul_add]⟩
lemma neg (h:Level k f):Level k (-f):= by rw [← neg_one_smul ℝ f];exact h.scale _
lemma sub (h:Level k f)(v:Level k g):Level k (f-g):=by rw [sub_eq_add_neg]; exact h.add v.neg
lemma eval {q:E4→ℝ}(h:Level k q)(hf:Level m f):Level (k+m) (fun x=> q x • f x):=by
 -- use scalar multiplication continuity on NormedSpace
 constructor
 · exact ContDiff.smul h.smooth hf.smooth
 intro t x; rw [h.morph,hf.morph,smul_eq_mul,smul_smul,smul_smul,pow_add,mul_right_comm]
lemma component(i:Axis): Level 1 (fun x:E4=> x i):=⟨((EuclideanSpace.proj i:E4→L[ℝ]ℝ)).contDiff,by simp⟩
lemma sum {I:Type*}(i:Finset I)(F:I→E4→E)(h:∀ a∈i,Level k (F a)): Level k (∑ a∈i,F a):=by
 induction i using Finset.induction_on with
 | empty=> rw [Finset.sum_empty];exact zero k
 | insert a s h' H=>rw [Finset.sum_insert h']; exact (h _ (Finset.mem_insert_self ..)).add (H fun i hi=>h _ (Finset.mem_insert_of_mem hi))

/-- Spatial derivative decreases natural degree for k≥1. -/
lemma advance {j:ℕ}(h:Level (j+1) f)(i:Axis):Level j (par i f):=by
  have he:= ContDiff.contDiffAt (x:=(0:E4)) h.smooth|>.of_le (m:=↑(j+1:ℕ)) (WithTop.coe_le_coe.mpr le_top)
  have hp: par i f=diagonal (Tensor.coeff (par i f) j 0):=by
    funext x
    conv_lhs=> rw [← funext (indicates h)]
    exact Tensor.slot_lower he ..
  conv in Level _ _=> rw [hp]; -- maybe rewrite recursively
  exact tax ..
lemma bottom (h:Level 0 f)(i:Axis):par i f=0:=by
 have he : f=(fun _=> f 0):= funext fun x=> by simpa using! (h.morph 0 x).symm
 rw [he]; funext x; simp [par,D]
lemma advances (h:Level k f)(i:Axis) : Level (k-1) (par i f):=by
 rcases k with _|j
 · rw [h.bottom i]; exact zero 0
 exact h.advance i

-- homogeneous Euler polynomial identity. `k * f` real factor not valuation. independent
-- dimension. Later use to integrate current etc.
lemma euler (h:Level k f)(x:E4): (∑ i:Axis,x i • par i f x)=(k:ℝ) • f x:=by
  have hx:= h.morph
  have hh:HasDerivAt (fun t:ℝ=> t • x) x (1:ℝ):=by simpa using! (hasDerivAt_id' (1:ℝ)).smul_const x
  have ht:= ((h.smooth.germ x).hasFDerivAt.comp_hasDerivAt_of_eq 1 hh (one_smul ..).symm)
  rw [show f ∘ (fun t:ℝ=>t • x)=fun t:ℝ=>t^k • f x from funext fun t=>h.morph t x] at ht
  have he: HasDerivAt (fun t:ℝ=>t^k • f x) ((k:ℝ) • f x) (1:ℝ):=by
    apply ((hasDerivAt_pow k (1:ℝ)).smul_const (f x)).congr_deriv; simp
  have hp:= ht.unique he
  have hu:(∑ i:Axis,x i • basis i)=x:=by ext i; simp [WithLp.ofLp_sum,Finset.sum_apply,basis,Pi.single_apply, mul_ite]
  rw [← hp]
  conv_rhs=> arg 2; rw [← hu]
  rw [map_sum]; exact Finset.sum_congr rfl fun i _=> (map_smul (fderiv ℝ f x) ..).symm -- hp hp includes x, replacing also contDiff f x etc
end Level
end YM.RG06.ClassicalOn
