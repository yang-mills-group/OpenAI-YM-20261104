import YM.X.Rank.Shim
/-! Average a skew tangent on real colors. Uses the given simple Lie algebra
of the group, no assumption on extra accidental discrete symmetries. -/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Rank
open Function Set Filter MeasureTheory Matrix Maxwell Wick Maxwell.Free
open Screen Next.Rank.Normal MvPolynomial
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius RealInnerProductSpace
variable {G : Gauge} (h:G.Simple)

def O (G : Gauge): Set (Mat G) :={ Q| Q.transpose*Q=1}
abbrev Sk (u:G.El) : Mat G := Matrix.of fun i j => G.adjoint u (unitColor G j) i
theorem Sk_ap (u:G.El) (A:Sample G): coatV (Sk u) A= G.adjoint u ∘ A := by
  funext x; ext1 i; change (Sk u *ᵥ (A x).ofLp) i= _; conv_rhs => rw [Function.comp_apply,← color_sum (A x),map_sum]
  simp only [WithLp.ofLp_sum,Finset.sum_apply,mulVec,dotProduct,Sk,Matrix.of_apply,map_smul, PiLp.smul_apply,smul_eq_mul]; exact Finset.sum_congr rfl fun j _=> mul_comm ..
theorem Sk_member (u:G.El): Sk u∈O G := by
  let L:= Sk u; change L.transpose*L=1; ext i j
  rw [Matrix.mul_apply]; let f : G.Color →ₗᵢ[ℝ] G.Color := ⟨G.adjoint u,G.norm_adjoint u⟩
  have he(x y:G.Color): ∑ k,x k*y k= ⟪x,y⟫:= by rw [real_inner_comm,EuclideanSpace.inner_eq_star_dotProduct]; rfl
  change (∑ k,(f (unitColor G i)) k*(f (unitColor G j)) k)=_
  rw [he (f (unitColor G i)) (f (unitColor G j)), f.inner_map_map,← he]; simp [unitPaint, Matrix.one_apply, eq_comm]
lemma turns {a:Mat G}(h:a∈O G) : a.transpose∈ O G:=by change a.transpose.transpose*_=_; rw [transpose_transpose]; exact mul_eq_one_comm.mpr h
lemma folds {a b:Mat G}(h:a∈O G)(w:b∈O G) : a*b∈ O G:= by change (a*b).transpose*_= _; rw [transpose_mul,Matrix.mul_assoc,← Matrix.mul_assoc _ a,show a.transpose*a=1 from h,one_mul]; exact w
@[fun_prop] lemma Sk_cont (G : Gauge): Continuous (Sk (G:=G)) := by apply continuous_matrix; intro i j; exact (EuclideanSpace.proj i: G.Color →L[ℝ]ℝ).continuous.comp (adj_cont (unitColor G j))

def adjX (X:Mat G)(u:G.El) := (Sk u).transpose * X * Sk u
@[fun_prop] lemma adjX_cont (X:Mat G) : Continuous (adjX X) := by
  unfold adjX; exact (((Sk_cont G).matrix_transpose).mul continuous_const).mul (Sk_cont G)

lemma adjFin {W:Type*}[NormedAddCommGroup W](f:G.El → W)(h:Continuous f): Integrable f G.probHaar := h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
include h
lemma Sk_mean {X: Mat G}(hX:X.transpose=-X) : ∫ u:G.El, adjX X u ∂G.probHaar=0:= by
  let J := G.ColorIndex
  let F:= adjX X; let M:=∫ u:G.El,F u ∂G.probHaar
  have hC:= adjFin F (adjX_cont X)
  have he(i j:J): M i j=∫ u:G.El,F u i j ∂G.probHaar:= ((Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap.integral_comp_comm hC).symm
  change M=0; ext i j; suffices hw : M j i=M i j by
    have hx (u:G.El): (F u).transpose=-(F u):=by unfold F adjX; rw [transpose_mul,transpose_mul,hX,transpose_transpose]; simp [mul_assoc]
    have hJ: M j i= -M i j:=by
      rw [he,he, ← integral_neg]; refine congr_arg (fun f: G.El→ℝ=>∫ z,f z ∂G.probHaar) (funext fun u=>?_); exact congr_fun (congr_fun (hx u) i) j
    change _=0; linarith only [hw,hJ]
  have hp i j u : F u i j=∑ a:J,∑ b:J,X b a*(line b (unitColor G i) u*line a (unitColor G j) u):= by unfold F adjX; simp only [Matrix.mul_apply, Finset.sum_mul,line, Sk, Matrix.of_apply,transpose_apply]; refine Finset.sum_congr rfl fun a _=> Finset.sum_congr rfl fun b _=> ?_; ring
  have hf a b i j:Continuous (fun u:G.El=> X b a*(line b (unitColor G i) u*line a (unitColor G j) u)):= continuous_const.mul ((show Continuous (fun u:G.El=> Sk u b i) by fun_prop).mul (show Continuous (fun u:G.El=> Sk u a j) by fun_prop))
  have hv i j:M i j=∑ a:J,∑ b:J,X b a*∫ u,line b (unitColor G i) u*line a (unitColor G j) u ∂G.probHaar:= by
     rw [he]; simp_rw [hp]; rw [integral_finsetSum]; refine Finset.sum_congr rfl fun a _=> ?_ ; rw [integral_finsetSum]; apply Finset.sum_congr rfl fun b _=>integral_const_mul ..; all_goals exact (by intro a _; apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _); first|exact hf ..|exact continuous_finsetSum _ fun _ _=> hf ..)
  rw [hv,hv]; refine Finset.sum_congr rfl fun a _=> Finset.sum_congr rfl fun b _=> ?_ ; obtain ⟨t,hr⟩:= pays_color h b a; rw [hr,hr, real_inner_comm]
end YM.PositionX.Rank
