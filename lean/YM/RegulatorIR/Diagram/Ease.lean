import YM.RegulatorIR.Diagram.Equations

/-! Equations for the honest, unnormalized moment and its vacuum (with
discarded leading action already factored out). Consequently one may use a
single ordinary product of all insertions. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Diagram.Interval
open Function Budget Budget.Layer Formal Finset PowerSeries
open scoped BigOperators Topology Classical Polynomial PowerSeries
variable {I:Type} [Fintype I]
variable {P : EPS I}
lemma log_sweep {K:Layer I I}(hx: coeff 0 P=0) : sweepF K (expo P)=expo P * (sweepF K P+ meetF K P P):=by
 unfold sweepF meetF
 rw [mul_add]; simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
 simp_rw [vane,derive_exp hx,Derivation.leibniz,derive_exp hx]
 change _ • (_ * _ + _* _) = _
 simp_rw [Algebra.smul_def]; ring

lemma meet_exp (K:Layer I I)(hx:coeff 0 P=0)(W:EPS I):meetF K W (expo P) = expo P*meetF K W P:=by
 unfold meetF; simp_rw [vane,derive_exp hx, Finset.mul_sum]
 refine Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>?_
 simp only [Algebra.smul_def]; ring
lemma meet_switch {K:Layer I I}(h:∀ i j,K i j=K j i)(P W:EPS I): meetF K P W=meetF K W P:=by
 unfold meetF; rw [Finset.sum_comm]
 refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_
 rw [h j i,mul_comm]
lemma sweepF_mul {K:Layer I I}(hh:∀ i j,K i j=K j i) (P W:EPS I) :
   sweepF K (P*W)=P*sweepF K W + W*sweepF K P + (2:ℝ) • meetF K W P := by
 rw [two_smul,meet_switch hh W P]
 nth_rw 1 [← meet_switch hh W P]
 unfold meetF sweepF; simp_rw [Finset.mul_sum]; simp_rw [← Finset.sum_add_distrib]
 refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_
 rw [Derivation.leibniz]; change K i j • (vane i (P*vane j W+W*vane j P)) = _
 rw [map_add, Derivation.leibniz, Derivation.leibniz]
 simp only [smul_eq_mul]; simp_rw [Algebra.smul_def]; ring

omit [Fintype I] in
lemma eqQ (x : EPS I) : (2:ℝ)⁻¹ • ((2:ℝ) • x)=x:=by rw [smul_smul,inv_mul_cancel₀ (by norm_num),one_smul]
lemma free_heat {K:Layer I I} (h : farther (clock (Jet I)) P = (2:ℝ)⁻¹ • (sweepF K P+meetF K P P))
   (hc:coeff 0 P=0) :
   farther (clock (Jet I)) (expo P)=(2:ℝ)⁻¹ • sweepF K (expo P):=by rw [derive_exp hc,h,log_sweep hc,mul_smul_comm]
lemma mark_heat {K:Layer I I}(hk:∀ i j,K i j=K j i)
   (h : farther (clock (Jet I)) P = (2:ℝ)⁻¹ • (sweepF K P+meetF K P P))
   (hc:coeff 0 P=0) {W:EPS I}(hW:farther (clock (Jet I)) W=(2:ℝ)⁻¹ • sweepF K W+meetF K W P) :
   farther (clock (Jet I)) (expo P * W)=(2:ℝ)⁻¹ • sweepF K (expo P*W):=by
 rw [Derivation.leibniz,free_heat h hc,hW]; change expo P*_+ W*_ = _; rw [sweepF_mul hk,smul_add,eqQ,meet_exp K hc,smul_add];
 rw [mul_add,mul_smul_comm,mul_smul_comm]; abel

/-- A heat solution as a time-polynomial. No convergence hypothesis on its
rank once inputs are actual polynomials. -/
def Pursues (K:Layer I I)(p:CurveT I):Prop := clock (Jet I) p = (2:ℝ)⁻¹ • sweepN K p
lemma coefficientP {K:Layer I I}{P:EPS I} (h:farther (clock (Jet I)) P=(2:ℝ)⁻¹ • sweepF K P)(i):
    Pursues K (coeff i P) := by unfold Pursues; rw [← farther_v,h, coeff_smul,sweepF_v]
lemma unique {K:Layer I I}(P Q:CurveT I)(h:Pursues K P)(hh:Pursues K Q)(he:P.coeff 0=Q.coeff 0): P=Q := by
 ext1 i; induction i with
 | zero=>exact he
 | succ i ih=>
     apply mul_right_cancel₀ (b:=(i+1:Jet I)) (by norm_cast)
     rw [← clock_v,← clock_v,h,hh,Polynomial.coeff_smul,Polynomial.coeff_smul,sweepN_v,sweepN_v,ih]
end YM.RegulatorIR.Diagram.Interval
