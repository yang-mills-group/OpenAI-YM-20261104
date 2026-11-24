import YM.Integration.WilsonPublicForkLabels

/-! One finite determination of the whole measured packet allows each
running physical input, and its actual far field, to vary with the radius. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPublicForkDirections
open Function Finset
open scoped Classical BigOperators
theorem many {I:Type}[Fintype I]{V:I→Type*}[∀i,NormedAddCommGroup (V i)]
    [∀i,NormedSpace ℂ (V i)][∀i,FiniteDimensional ℂ (V i)]
    {A:I→Type*}[∀i,Fintype (A i)](b:∀i,Module.Basis (A i) ℂ (V i))
    (T:MultilinearMap ℂ V ℂ)(v:∀i,V i)(C:(∀i,A i)→ℝ)(fee:ℝ)
    (charged:∀j:∀i,A i,‖T (fun i=>b i (j i))‖≤C j*fee):
    ‖T v‖≤(∑j:∀i,A i,(∏i,‖((b i).coord (j i)).toContinuousLinearMap‖)*C j)*
      (∏i,‖v i‖)*fee:=by
  let ω:=fun (j:∀i,A i)=>∏i,(b i).repr (v i) (j i)
  have expanded:T v=∑j:∀i,A i,ω j*T (fun i=>b i (j i)):=by
    have eq:v=fun i=>∑a:A i,(b i).repr (v i) a • b i a:=funext fun i=>((b i).sum_repr _).symm
    conv_lhs=>rw [eq]
    rw [MultilinearMap.map_sum];exact Finset.sum_congr rfl (fun j _=>T.map_smul_univ _ _)
  have terms(j:∀i,A i):‖ω j‖≤(∏i,‖((b i).coord (j i)).toContinuousLinearMap‖)*(∏i,‖v i‖):=by
    dsimp only [ω];rw [norm_prod,←Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun i _=>norm_nonneg _) fun i _=>((b i).coord (j i)).toContinuousLinearMap.le_opNorm (v i)
  rw [expanded,Finset.sum_mul,Finset.sum_mul]
  apply (norm_sum_le _ _).trans;apply Finset.sum_le_sum;intro j _
  rw [norm_mul]
  exact (mul_le_mul (terms j) (charged j) (norm_nonneg _) (mul_nonneg (Finset.prod_nonneg fun _ _=>norm_nonneg _)
    (Finset.prod_nonneg fun _ _=>norm_nonneg _))).trans_eq (by ring)

theorem one {V:Type*}[NormedAddCommGroup V][NormedSpace ℂ V][FiniteDimensional ℂ V]
    {A:Type*}[Fintype A](b:Module.Basis A ℂ V)(T:V→ₗ[ℂ]ℂ)(v:V)(C:A→ℝ)(fee:ℝ)
    (charged:∀i,‖T (b i)‖≤C i*fee):
    ‖T v‖≤(∑i,‖(b.coord i).toContinuousLinearMap‖*C i)*‖v‖*fee:=by
  have expanded:T v=∑i,b.repr v i*T (b i):=by
    conv_lhs=>rw [←b.sum_repr v]
    rw [map_sum];simp only [map_smul,smul_eq_mul]
  rw [expanded,Finset.sum_mul,Finset.sum_mul]
  apply (norm_sum_le _ _).trans;apply Finset.sum_le_sum;intro i _
  rw [norm_mul]
  exact (mul_le_mul ((b.coord i).toContinuousLinearMap.le_opNorm v) (charged i) (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq (by ring)
end YM.Integration.WilsonPublicForkDirections
