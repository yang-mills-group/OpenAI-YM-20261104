import YM.RegulatorIR.Diagram.Interval

/-! Convert the tensor recursions into time-polynomial differential
equations. Keep finite rank support through each order when collecting
coefficients. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Diagram
open Function Budget Budget.Layer Budget.Packet Formal Interval Finset
open scoped BigOperators Topology Classical Polynomial PowerSeries
variable {I:Type} [Fintype I]
-- keep V for other energies

def desert (t r:ℕ→ℕ)(V:ℕ→Orders I) : EPS I:= PowerSeries.mk fun e=>∑ i∈range (t e+1), Polynomial.monomial i (packed (V i e) (r e))
private lemma desert_v (t r:ℕ→ℕ)(V:ℕ→Orders I)(e i)(h:∀ j, t e<j →∀ x,V j e x=0):
   (PowerSeries.coeff e (desert t r V)).coeff i= packed (V i e) (r e) :=by
 unfold desert; rw [PowerSeries.coeff_mk,Polynomial.finsetSum_coeff]; by_cases he:i ≤ t e
 · simp [Polynomial.coeff_monomial,he]
 have he :¬ i<t e+1:=by omega
 have hz : t e < i:=by omega
 simp [Polynomial.coeff_monomial,h i hz,he,packed]

def plains (K:Layer I I)(V:Orders I):EPS I:= desert (fun e=>3*e) (fun e=>e+2) (logHeat K V true)
-- leave m+1 slots before expansions; permits convenience of ≤ positive m+1

def owned (m:ℕ)(K:Layer I I)(V W:Orders I):EPS I := desert (fun e=>3*e+(m+1)) (fun e=>e+m+1) (markHeat K (logHeat K V true) W)

lemma log_v (K:Layer I I)(V:Orders I)(e i)(h:Vacuum V) : (PowerSeries.coeff e (plains K V)).coeff i=packed (logHeat K V true i e) (e+2):= by
 apply desert_v; intro j h' x; by_contra! hf; have hv:= (heated_cap K V h true e x j hf).2.2; omega
lemma mark_v (m:ℕ)(K:Layer I I)(V W:Orders I)(e i)(h:Vacuum V)(he:∀ e,Within (e+(m+1)) (W e)) : (PowerSeries.coeff e (owned m K V W)).coeff i=packed (markHeat K (logHeat K V true) W i e) (e+m+1):= by
 apply desert_v
 intro j h' x; by_contra! hf; have hh:= (marked_cap (m+1) K V h W he true e x j hf).2; omega
lemma plain_entry (K:Layer I I)(V:Orders I)(h:Vacuum V) : PowerSeries.coeff 0 (plains K V)=0:=by
  ext1 i;rw [log_v K V _ _ h,Polynomial.coeff_zero]; apply Finset.sum_eq_zero;intro k _
  rw [show logHeat K V true i 0 k=0 from by by_contra! he; exact lt_irrefl 0 (heated_cap K V h _ _ _ _ he).1, render_zero]

private lemma pack_drift (m:ℕ)(K:Layer I I)(V W:ℕ→Orders I) (v w:EPS I) (e i:ℕ)
    (h:∀ j,gradedSymmetric (V j))(he:∀ j,gradedSymmetric (W j))
    (hp:∀ e k,Within (e+2) (V k e))(ht:∀ e k,Within (e+m+1) (W k e))
    (hc:∀ e k,(PowerSeries.coeff e v).coeff k=packed (V k e) (e+2)) (hw:∀ e k,(PowerSeries.coeff e w).coeff k=packed (W k e) (e+m+1)) :
    packed (drift K W V i e) (e+m+1)=(PowerSeries.coeff e (meetF K w v)).coeff i:=by
 rw [meetF_v,show drift K W V i e=∑ p∈antidiagonal i, carry K (W p.1) (V p.2) e by ext1; simp [drift,Finset.sum_apply],pack_sum]
 apply Finset.sum_congr rfl;intro p _
 rw [show carry K (W p.1) (V p.2) e=∑ q∈antidiagonal e, force K (W p.1 q.1) (V p.2 q.2) by ext1; simp [carry, Finset.sum_apply],pack_sum]
 apply Finset.sum_congr rfl;intro q hq; rw [hc,hw,← pack_force K (W p.1 q.1) (V p.2 q.2) (ht q.1 p.1) (hp q.2 p.2) (he p.1 q.1) (h p.2 q.2)]
 have hu:=mem_antidiagonal.mp hq; congr 1; omega

omit [Fintype I] in
private lemma clears (t:ℕ)(P:Jet I) : MvPolynomial.C ((t+1:ℝ)⁻¹)*P*((t:Jet I)+1) = P:=by
 have hz: MvPolynomial.C (t+1:ℝ)=(t:Jet I)+1:=by simp
 rw [mul_right_comm,← hz,← map_mul, inv_mul_cancel₀ (by positivity),map_one,one_mul]

lemma log_equation (K:Layer I I)(V:Orders I)(h:Vacuum V)(hp:gradedSymmetric V):
    let L:=plains K V
    farther (clock (Jet I)) L= (2:ℝ)⁻¹ • (sweepF K L+meetF K L L):=by
 let T:=logHeat K V true; let H:=plains K V; intro L
 apply PowerSeries.ext; intro e
 ext1 j
 have ht (e k): Within (e+2) (T k e):=fun x hx=> (heated_cap K V h true e x k hx).2.1
 let Q:= fun r=>drift K T T j e r
 have he:T (j+1) e=((j+1:ℝ)⁻¹) • (heating K (T j e)+ (2:ℝ)⁻¹ • Q):= by ext1 r; simp [T,logHeat_next,Q]
 rw [Formal.farther_v,PowerSeries.coeff_smul,map_add,clock_v]
 change _*( (j:Jet I)+1)=_
 rw [log_v K V _ _ h]
 change packed (T (j+1) e) _ * _ = _
 rw [he,pack_smul,pack_add,pack_multiplicity K (ht e j) (heatedSym K hp true j e),pack_smul]
 rw [clears]
 change _ + MvPolynomial.C (2:ℝ)⁻¹ * packed (drift K T T j e) (e+1+1)= _
 rw [pack_drift 1 K T T H H e j (fun j=>heatedSym K hp true j) (fun j=>heatedSym K hp true j) ht ht (fun e j=>log_v K V e j h) (fun e j=>log_v K V e j h)]
 rw [Polynomial.coeff_smul,Polynomial.coeff_add, sweepF_v,sweepN_v, log_v K V _ _ h, Algebra.smul_def,mul_add]; rfl

lemma mark_equation (m:ℕ)(K:Layer I I)(V W:Orders I)(h:Vacuum V)(hx:∀ e,Within (e+(m+1)) (W e))(hp:gradedSymmetric V)(hh:gradedSymmetric W) :
   let P:= owned m K V W
   farther (clock (Jet I)) P= (2:ℝ)⁻¹ • sweepF K P + meetF K P (plains K V) := by
 let T:=logHeat K V true; let S:=markHeat K T W;intro p; apply PowerSeries.ext; intro e; ext1 j
 have ht e k: Within (e+2) (T k e):=fun x hx=> (heated_cap K V h true e x k hx).2.1
 have hS e k: Within (e+m+1) (S k e):=fun x h'=> by have hj:= (marked_cap (m+1) K V h W hx true e x k h').1;omega
 have he:S (j+1) e=((j+1:ℝ)⁻¹) • (heating K (S j e)+ drift K S T j e):= by ext1 r; rw [show S (j+1) e r=_ from rfl]; exact markHeat_next ..
 rw [Formal.farther_v,map_add, Polynomial.coeff_add,clock_v,mark_v m K V W e _ h hx]
 change packed (S (j+1) e) _ * _ = _
 rw [he,pack_smul,clears,pack_add,
   pack_multiplicity K (hS e j) (fun i=>markedSym K T hh j e i)]
 rw [pack_drift m K T S (plains K V) p e j (fun j=>heatedSym K hp true j) (fun j=>markedSym K T hh j) ht hS (fun e k=> log_v K V e k h) (fun e k=> mark_v m K V W e k h hx)]
 rw [PowerSeries.coeff_smul, Polynomial.coeff_smul, sweepF_v, sweepN_v, mark_v _ _ _ _ _ _ h hx, Algebra.smul_def]; rfl
end YM.RegulatorIR.Diagram
