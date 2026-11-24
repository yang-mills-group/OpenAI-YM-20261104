import YM.Integration.FVA1Physical.Wilson.QuadraticTaylor

/-! Contract a pair of slots in a polynomial coefficient against the actual
covariance. Each move costs its row sum in the tensor operator norm,
independently of the torus and of all remaining slots. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson.SignCovariance
open Finset Matrix Push.Uniform YM.Tensor
open scoped BigOperators Classical
variable {ι:Type} [Fintype ι] [DecidableEq ι] {d:ℕ}
local notation "V" => (ι→ℝ)

/-- Tensor with two adjacent slots contracted. The order of the matrix indices
matches the Rademacher contraction and is immaterial on a physical covariance. -/
def pairTrace (K:Matrix ι ι ℝ) (T:Tensor.T V ℝ (d+2)) : Tensor.T V ℝ d :=
  ∑ i,∑ j,K j i • (T.curryLeft (bolt i)).curryLeft (bolt j)

omit [DecidableEq ι] in
private theorem read_slots (T:Tensor.T V ℝ (d+2)) (v:Fin d→V) (u w:V) :
    bilinear (fun i j=>(T.curryLeft (bolt i)).curryLeft (bolt j) v) u w = T (Fin.cons u (Fin.cons w v)) := by
  have one {n:ℕ} (B:Tensor.T V ℝ (n+1)) (a:V) (W:Fin n→V) :
      B.curryLeft a W=∑ i,a i*B.curryLeft (bolt i) W := by
    calc _ = B.curryLeft (∑ i,a i • bolt i) W := congrArg (fun t=>B.curryLeft t W) (combine a).symm
         _ = _ := by simp only [map_sum,map_smul,_root_.sum_apply,_root_.smul_apply,smul_eq_mul]
  rw [show T (Fin.cons u (Fin.cons w v))=T.curryLeft u (Fin.cons w v) from rfl,one T u]
  unfold bilinear;apply sum_congr rfl;intro i _
  change _ = u i*((T.curryLeft (bolt i)).curryLeft w v)
  rw [one (T.curryLeft (bolt i)) w v,Finset.mul_sum]
  apply sum_congr rfl;intro j _;ring

/-- All remaining directions may be chosen independently. No cardinality of the field indices enters. -/
theorem pairTrace_norm (K:Matrix ι ι ℝ) {C:ℝ} (hc:0≤C) (rows:∀i,∑j,|K i j|≤C)
    (T:Tensor.T V ℝ (d+2)) : ‖pairTrace K T‖ ≤ C*‖T‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg hc (norm_nonneg _))
  intro v
  let W : Matrix ι ι ℝ := fun i j=>(T.curryLeft (bolt i)).curryLeft (bolt j) v
  have id : pairTrace K T v = ∑ i,∑ j,W i j*K j i := by
    unfold pairTrace;simp only [_root_.sum_apply,_root_.smul_apply,smul_eq_mul];exact sum_congr rfl fun i _=>sum_congr rfl fun j _=>mul_comm ..
  rw [Real.norm_eq_abs,id]
  apply contraction W K hc rows
  intro u w hu hw
  rw [show bilinear W u w = T (Fin.cons u (Fin.cons w v)) from read_slots T v u w]
  have op:=T.le_opNorm (Fin.cons u (Fin.cons w v))
  simp only [Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ] at op
  apply op.trans
  have h := mul_le_mul hu hw (norm_nonneg w) zero_le_one
  calc ‖T‖*(‖u‖*(‖w‖*∏ i,‖v i‖)) = ‖T‖*((‖u‖*‖w‖)*(∏ i,‖v i‖)) := by ring
       _ ≤ ‖T‖*((1*C)*(∏ i,‖v i‖)) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h (prod_nonneg fun _ _=>norm_nonneg _)) (norm_nonneg _)
       _ = _ := by ring

omit [DecidableEq ι] in
theorem pairTrace_sym (K:Matrix ι ι ℝ) (T:Tensor.T V ℝ (d+2)) (hs:Tensor.Sym T) : Tensor.Sym (pairTrace K T) := by
  intro v s
  unfold pairTrace;simp only [_root_.sum_apply,_root_.smul_apply,smul_eq_mul]
  apply sum_congr rfl;intro i _;apply sum_congr rfl;intro j _
  exact congrArg (K j i * ·) (Tensor.freeze_sym _ (Tensor.freeze_sym T hs (bolt i)) (bolt j) v s)

end YM.Integration.FVA1Physical.Wilson.SignCovariance
