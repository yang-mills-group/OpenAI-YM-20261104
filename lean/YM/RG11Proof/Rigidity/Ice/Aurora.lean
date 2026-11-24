import YM.RG11Proof.Rigidity.Ice.Winter
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# The differential cost of a minimizing frame
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity.Ice
open Fields Labels Maxwell Function Extra.FD Reads Maxwell.Free Set Filter Pert.Position Gauge
open scoped Classical BigOperators Topology ContDiff InnerProductSpace
variable {G:Gauge}{F:Frames G}{d:ℕ}
local notation "V"=>G.Color
local notation "Y"=>V→L[ℝ] V

def skewFare (p : V) (B M : Y) := ∑ i : G.ColorIndex, ⟪spinY p (M (rays i)),B (rays i)⟫_ℝ
lemma fareCont (p : V) : Continuous fun z : Y×Y=> skewFare p z.1 z.2:= by
  have he (v:V) := (ContinuousLinearMap.apply ℝ V v).continuous
  exact continuous_finsetSum _ fun i _=> ((spinY p).continuous.comp ((he _).comp continuous_snd)).inner ((he _).comp continuous_fst)
lemma fareMul (p : V) (U B:Y)(s:ℝ) : skewFare p (s • B) U=s*skewFare p B U := by
  unfold skewFare; simp_rw [_root_.smul_apply,real_inner_smul_right, Finset.mul_sum]

lemma fare_center (p : V){b:Buffer F d}{t:ℝ}{U:Y}(h : Winner b t U): skewFare p (U-1) U=0:=by
  let E (s:ℝ):= (adSpin (caravan p s))*U
  have hd (x : V) : E 0 x=U x:= by change G.adjoint (caravan p 0) _=_; simp [caravan]
  have ht (x:V): HasDerivAt (fun s=> E s x-x) ((spinY p) (U x)) 0:= (adj_has p (U x)).sub_const _
  have hg (x : V):= HasDerivAt.inner ℝ (ht x) (ht x)
  simp_rw [hd, real_inner_comm (spinY p (U _)) (U _-_),← two_mul] at hg
  let L (s:ℝ):= nearest (E s)
  have hL: HasDerivAt L (2*skewFare p (U-1) U) 0:=by
    unfold L nearest skewFare; rw [Finset.mul_sum]; apply HasDerivAt.fun_sum; intro i _; exact hg _
  have hm : IsLocalMin L 0:=by
    apply Filter.Eventually.of_forall; intro i
    change nearest (E 0) ≤ nearest (E i)
    rw [ContinuousLinearMap.ext hd]; exact h.2 _ (h.1.vol _)
  linarith [show 2*skewFare p (U-1) U=0 from hL.deriv.symm.trans hm.deriv_eq_zero]

private lemma flare_trace (p : V)(D:Y): LinearMap.trace ℝ V (D.toLinearMap*G.ad p)= - skewFare p D 1:=by
  rw [LinearMap.trace_mul_comm, LinearMap.trace_eq_matrix_trace _ (EuclideanSpace.basisFun G.ColorIndex ℝ).toBasis,Matrix.trace]
  unfold skewFare; rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _=> ?_
  simp_rw [Matrix.diag_apply,LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,OrthonormalBasis.repr_apply_apply]
  change ⟪rays i,G.ad p (D (rays i))⟫_ℝ= -⟪G.ad p (rays i), D (rays i)⟫_ℝ
  rw [Gauge.ad_skew,neg_neg]
/-- The measured residual is orthogonal to true infinitesimal adjoint
rotations (in a subsequential normalization). -/
lemma flare {b:Buffer F d}{u:ℕ→ℝ}{U:ℕ→Y}(h : ∀ i, Winner b (u i) (U i))(ht:Tendsto U atTop (𝓝 1))
    {r:ℕ→ℝ}{D:Y}(hD:Tendsto (fun i=>r i • (U i-1)) atTop (𝓝 D)) : OffKill D.toLinearMap := by
  intro p
  have he :=
    (fareCont p).continuousAt.tendsto.comp (hD.prodMk_nhds ht)
  simp only [Function.comp_def] at he
  simp_rw [fareMul, fun i=> fare_center p (h i),mul_zero] at he
  -- sum indexed inner gives minus trace (use skew of ad already)
  have hz := tendsto_nhds_unique he tendsto_const_nhds
  rw [flare_trace,hz,neg_zero]
end YM.RG11.Rigidity.Ice
