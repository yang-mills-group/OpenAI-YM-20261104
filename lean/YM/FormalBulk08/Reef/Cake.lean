import YM.FormalBulk08.Reef.Noisy
import YM.FormalBulk08.Orb.Stark

/-! Bookkeeping of the flat matrix Hessian, no covariance estimates here. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Reef
open Series Jets Wick Orb PowerSeries Function Matrix
open scoped BigOperators
variable {U V W : Type*} [Fintype U] [Fintype V] [Fintype W]

def crunch (M : Matrix V V ℝ) : Glyphs ℝ V := -∑ i,∑ j,MvPolynomial.C (halve (M i j))*MvPolynomial.X i*MvPolynomial.X j
lemma crunch_value (M : Matrix V V ℝ) (x:Rays V): traceP x (crunch M)= -(dotProduct x (M *ᵥ x))/2 := by
   unfold crunch; simp only [Matrix.mulVec,dotProduct,traceP,map_neg,map_sum,map_mul,MvPolynomial.aeval_C,MvPolynomial.aeval_X,Finset.mul_sum,neg_div];
   congr 1
   simp [halve,div_eq_mul_inv,Finset.sum_mul];exact Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>by ring

def draught (A : Matrix U V ℝ) (i : U) : Glyphs ℝ V := mixRows A (MvPolynomial.X i)
omit [Fintype U] in
lemma draught_fee (A : Matrix U V ℝ) (x:Rays V) : (fun i=>traceP x (draught A i))= A*ᵥ x := by ext i; simp [traceP,draught,mixRows,Matrix.mulVec,dotProduct]

-- V= coarse, U active, W all fine
variable [DecidableEq V]
lemma additive_balance (k : ℝ) (P Q : Matrix U U ℝ)
  (Y : Matrix V U ℝ) (A : Matrix U V ℝ) (Z : Matrix V V ℝ) (x : U→ ℝ) (y : V→ℝ)
  (e : P=Q+k • (Yᵀ*Y)) (s : Pᵀ=P)
  (h : P*A=k • Yᵀ) (z : Aᵀ*Q*A+k • ((1-Y*A)ᵀ*(1-Y*A))=Z) :
  let u:=A*ᵥ y; let v:=y-Y*ᵥ (x+u)
  dotProduct (x+u) (Q*ᵥ (x+u))+k*dotProduct v v=dotProduct x (P*ᵥ x)+dotProduct y (Z*ᵥ y) := by
    intro u v;let T:=y-Y*ᵥ u
    have hs : Qᵀ=Q := by rw [e, Matrix.transpose_add,transpose_smul, transpose_mul,transpose_transpose] at s; exact add_right_cancel s
    have he : Q*ᵥ u=k • (Yᵀ*ᵥ T) := by
       have ht : P*ᵥ u=k • (Yᵀ*ᵥ y) := by unfold u; rw [Matrix.mulVec_mulVec,h,Matrix.smul_mulVec]
       rw [e, Matrix.add_mulVec,Matrix.smul_mulVec,← Matrix.mulVec_mulVec] at ht; unfold T; rw [Matrix.mulVec_sub, smul_sub]; exact eq_sub_of_add_eq ht
    have hb : v=T-Y*ᵥ x := by unfold v T; rw [Matrix.mulVec_add, add_comm]; abel
    have ha : (1-Y*A)*ᵥ y=T := by rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec,Matrix.one_mulVec]
    have hy : dotProduct y (Z*ᵥ y)=dotProduct u (Q*ᵥ u)+k*dotProduct T T := by
       rw [←z, Matrix.add_mulVec,dotProduct_add, Matrix.smul_mulVec]; simp_rw [← Matrix.mulVec_mulVec,ha]; rw [dotProduct_smul,smul_eq_mul,dotProduct_transpose_mulVec,dotProduct_transpose_mulVec,ha, dotProduct_comm (Q*ᵥ (A*ᵥ y))]
    have hx : dotProduct x (P*ᵥ x)= dotProduct x (Q*ᵥ x)+k*dotProduct (Y*ᵥ x) (Y*ᵥ x) := by rw [e, Matrix.add_mulVec,dotProduct_add, Matrix.smul_mulVec,← Matrix.mulVec_mulVec,dotProduct_smul,smul_eq_mul,dotProduct_transpose_mulVec]
    have hQ : dotProduct x (Q*ᵥ u)=dotProduct u (Q*ᵥ x) := by simpa only [hs] using dotProduct_transpose_mulVec Q x u
    have hR : dotProduct x (Q*ᵥ u)= k*dotProduct T (Y*ᵥ x) := by rw [he,dotProduct_smul,smul_eq_mul,dotProduct_transpose_mulVec]
    rw [hx,hy,hb,mulVec_add]; simp_rw [dotProduct_add, add_dotProduct,dotProduct_sub,sub_dotProduct]; rw [←hQ,hR,dotProduct_comm (Y *ᵥ x) T]; ring
end YM.FormalBulk08.Reef
