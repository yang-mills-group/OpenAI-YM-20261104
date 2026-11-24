import YM.Integration.FVA1Physical.Wilson.WickTensorRent
import YM.Integration.FVA1Physical.Wilson.WickTensorStein

/-! Wick recursion for a full symmetric Taylor coefficient on the original
finite conditional covariance. The norm budget depends only on the arity
and the maximum absolute row sum, before the underlying period. -/
set_option autoImplicit false
set_option maxHeartbeats 1700000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson.SignCovariance
open Finset Matrix MeasureTheory Push.Uniform YM.Tensor YM.Next.SectorChange
open scoped BigOperators Classical
variable {ι:Type} [Fintype ι] [DecidableEq ι] {d:ℕ}
local notation "V" => (ι→ℝ)

omit [DecidableEq ι] in
private theorem linear_entry (B:Tensor.T V ℝ (d+1)) (u:V) (v:Fin d→V) :
    B.curryLeft u v = ∑ i,u i*B.curryLeft (bolt i) v := by
  calc _=B.curryLeft (∑ i,u i•bolt i) v := congrArg (fun w=>B.curryLeft w v) (combine u).symm
       _=_ := by simp only [map_sum,map_smul,_root_.sum_apply,_root_.smul_apply,smul_eq_mul]

omit [DecidableEq ι] in
private theorem split_diagonal (T:Tensor.T V ℝ (d+1)) (z:V) : Tensor.diagonal T z=T.curryLeft z (fun _=>z) := by
  change T (fun _=>z) = T (Fin.cons z (fun _=>z))
  apply congrArg T;funext k;cases k using Fin.cases <;> simp

theorem gaussian_pairTrace (K:Matrix ι ι ℝ) (pd:K.PosDef) (T:Tensor.T V ℝ (d+2)) (hs:Tensor.Sym T) :
    (∫ z,Tensor.diagonal T z ∂Gaussian.cloud K) = (d+1:ℝ)*∫ z,Tensor.diagonal (pairTrace K T) z ∂Gaussian.cloud K := by
  let μ:=Gaussian.cloud K
  let B:ι→Tensor.T V ℝ (d+1):=fun i=>T.curryLeft (bolt i)
  let CT:ι→Tensor.T V ℝ d:=fun i=>(B i).curryLeft (K i)
  have first(z:V): Tensor.diagonal T z=∑ i,z i*Tensor.diagonal (B i) z:= by
    rw [split_diagonal];exact linear_entry T z _
  have last(z:V): ∑ i,Tensor.diagonal (CT i) z=Tensor.diagonal (pairTrace K T) z := by
    change (∑ i,(B i).curryLeft (K i) (fun _=>z)) = (pairTrace K T) (fun _=>z)
    unfold pairTrace;simp only [_root_.sum_apply,_root_.smul_apply,smul_eq_mul]
    apply sum_congr rfl;intro i _;rw [linear_entry (B i) (K i)]
    apply sum_congr rfl;intro j _;rw [(isHermitian_iff_isSymm.mp pd.isHermitian).apply j i]
  calc
    _ = ∫ z,∑ i,z i*Tensor.diagonal (B i) z ∂μ := integral_congr_ae (.of_forall first)
    _ = ∑ i,∫ z,z i*Tensor.diagonal (B i) z ∂μ := integral_finsetSum _ fun i _=>tensorCoordIntegrable K pd (B i) i
    _ = ∑ i, (d+1:ℝ)*∫ z,Tensor.diagonal (CT i) z ∂μ := sum_congr rfl fun i _=>
      (tensor_stein K pd (B i) (Tensor.freeze_sym T hs (bolt i)) i).trans (integral_const_mul ..)
    _ = (d+1:ℝ)*∫ z,Tensor.diagonal (pairTrace K T) z ∂μ := by
      rw [←Finset.mul_sum,←integral_finsetSum _ (fun i _=>tensorIntegrable K pd (CT i))];exact congrArg ((d+1:ℝ)* ·) (integral_congr_ae (.of_forall last))

/-- For arity 2k this is (2k−1)!! times C^k; odd integrals vanish. -/
def wickRent (C:ℝ) : ℕ→ℝ
  | 0 => 1
  | 1 => 0
  | n+2 => (n+1:ℝ)*C*wickRent C n

lemma wickRent_nonnegative {C:ℝ} (hc:0≤C) : ∀ n,0≤wickRent C n
  | 0 => zero_le_one
  | 1 => le_rfl
  | n+2 => mul_nonneg (mul_nonneg (by positivity) hc) (wickRent_nonnegative hc n)

private theorem linear_center (K:Matrix ι ι ℝ) (T:Tensor.T V ℝ 1) :
    (∫ z,Tensor.diagonal T z ∂Gaussian.cloud K)=0 := by
  let f:ι→ℝ:=fun i=>T.curryLeft (bolt i) (fun _=>0)
  have v(z:V): Tensor.diagonal T z = ∑ i,z i*f i := by
    rw [split_diagonal,linear_entry T z];apply sum_congr rfl;intro i _;rw [show (fun _:Fin 0=>z)=(fun _:Fin 0=>(0:V)) from Subsingleton.elim ..]
  rw [show Tensor.diagonal T = fun z=>∑ i,z i*f i from funext v,integral_finsetSum]
  · simp [integral_mul_const,Gaussian.cloud_center]
  · intro i _;exact ((YM.AnalyticBridge.LocalGaussianLaws.Density.first_debit K i).integrable (by norm_num)).mul_const _

/-- Homogeneous expectation bound, with no factor for the number of torus sites. -/
theorem gaussian_tensor_bound (K:Matrix ι ι ℝ) (pd:K.PosDef) {C:ℝ} (hc:0≤C) (rows:∀i,∑j,|K i j|≤C) :
    ∀ n (T:Tensor.T V ℝ n),Tensor.Sym T→ |∫ z,Tensor.diagonal T z ∂Gaussian.cloud K|≤wickRent C n*‖T‖
  | 0,T,_ => by
    have cn(z:V):Tensor.diagonal T z= T (fun _=>0):=congrArg T (Subsingleton.elim ..)
    rw [funext cn,integral_const];simp only [Measure.real,measure_univ,ENNReal.toReal_one,one_smul,wickRent,one_mul]
    simpa only [prod_const,card_univ,Fintype.card_fin,pow_zero,mul_one,Real.norm_eq_abs] using T.le_opNorm (fun _=>(0:V))
  | 1,T,_ => by rw [linear_center K T,abs_zero];simp [wickRent]
  | n+2,T,hs => by
    rw [gaussian_pairTrace K pd T hs,abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤n+1),wickRent]
    have old := gaussian_tensor_bound K pd hc rows n (pairTrace K T) (pairTrace_sym K T hs)
    have inner := old.trans (mul_le_mul_of_nonneg_left (pairTrace_norm K hc rows T) (wickRent_nonnegative hc n))
    exact (mul_le_mul_of_nonneg_left inner (by positivity)).trans_eq (by ring)

end YM.Integration.FVA1Physical.Wilson.SignCovariance
