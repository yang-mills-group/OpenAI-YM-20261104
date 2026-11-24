import YM.SchemeRG11.Storm.Honey
/-!
Orientation of the integrated action trilinear form. Tαbcd are here completely
OPEN ordered tests, with additional derivative on the leg numbered by T. Sum
over all d tangent indices only coming from the action; projecting pinned cuts
at d4. `turnTx` will instantiate the simultaneous-translation derivative
at separated, uncut measure.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.SchemeRG11.Flare
open Hot Maxwell Analysis Set MeasureTheory Metric Function Filter TopologicalSpace Cluster Steam MSbar Pert Triangle Storm
open scoped Topology ContDiff BigOperators Real RealInnerProductSpace

abbrev Banner := Axis→Axis→Axis→Axis→ℝ
abbrev Roll (K : Type) := Eye→Axis→Axis→Axis→Axis→K
variable (T : Roll ℝ)
def std : Banner:= fun a b c d=> if a=c ∧ b=d then 1 else 0

def midway : Banner := fun a b c d=> (1/2:ℝ)*(std a b c d-std a b d c)
def low : Banner := fun a b c d=> ∑ t:Eye, fan false t a b*fan false t c d

def theta : Banner:=fun a b c d=> midway a b c d-low a b c d
section
private def swift (a b c d : Axis) : ℤ := if a=c ∧ b=d then 1 else 0
private def thin (a b c d : Axis) : ℤ:= swift a b c d-swift a b d c-∑ t:Fin 3, fanI false t a b * fanI false t c d
private lemma rise (a b c d) : 2*theta a b c d=(thin a b c d : ℝ) := by
  have hs a b c d : std a b c d=(swift a b c d:ℤ):= by unfold std swift; split <;> simp_all
  unfold theta midway thin low; rw [hs,hs]
  have hp t : 2* (fan false t a b * fan false t c d)= (fanI false t a b * fanI false t c d:ℤ):= by unfold fan; rw [div_mul_div_comm,sqrt_two_rule]; push_cast; ring
  rw [mul_sub,Finset.mul_sum]; simp only [hp,←Int.cast_sum,Int.cast_sub]; ring
set_option maxRecDepth 9000 in
set_option maxHeartbeats 3000000 in
private lemma tango : ∀ a b c d,thin a b c d=thin a c d b := by decide
lemma pivot (a b c d : Axis) : theta a b c d=theta a c d b:= mul_left_cancel₀ (by norm_num : (2:ℝ)≠0) (by rw [rise,rise,tango a b c d])
end

def strum {K : Type} [Add K] (T : Roll K) (a b c d : Axis) := T 0 a b c d + T 1 a d b c + T 2 a c d b
/-- δ ab interactions, roles `(A_b_deriv a, A_a, A_b)`; both permutations of the undifferentiated A leaves, plus all three anchors. `T` in this use does NOT yet negate the differentiating line. So two signs (derivative from opposite endpoint and negative action). -/
def street {K : Type} [AddCommGroup K] (T : Roll K) := ∑ a,∑ b,(strum T a b a b - strum T a b b a)

def rum (P : Banner) : ℝ:= ∑ a,∑ b, ∑ c,∑ d,P a b c d*strum T a b c d
lemma rum_std : street T = 2*rum T midway := by
  unfold street rum midway; simp only [mul_sub,sub_mul,Finset.sum_sub_distrib, Finset.mul_sum, ← mul_assoc,show (2:ℝ)*(1/2)=1 by norm_num,one_mul]
  have hp a b : (∑ c : Axis,∑ d,std a b c d * strum T a b c d)=strum T a b a b:=by simp [std,ite_mul,ite_and]
  have hq a b : (∑ c : Axis,∑ d,std a b d c *strum T a b c d)= strum T a b b a:=by rw [Finset.sum_comm]; simp [std,ite_mul,ite_and]
  simp only [hp,hq]

variable (h : ∀ a b c d, T 0 a b c d+T 1 a b c d+T 2 a b c d=0)
section
private lemma scan {V : Banner} (a : Axis) : (∑ b,∑ c,∑ d,theta a b c d * V a d b c)=∑ b,∑ c,∑ d,theta a b c d*V a b c d := by
   rw [show (∑ b, ∑ c,∑ d, theta a b c d*V a d b c)=∑ b,∑ d,∑ c,theta a b c d*V a d b c from Finset.sum_congr rfl (fun b _=> Finset.sum_comm)]
   rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro d _; apply Finset.sum_congr rfl; intro b _; exact Finset.sum_congr rfl (fun c _=> by rw [pivot a d b c])
private lemma scans (V: Banner) (a:Axis): (∑ b,∑ c,∑ d,theta a b c d * V a c d b)=∑ b,∑ c,∑ d,theta a b c d*V a b c d:= (scan (V:=fun a b c d=> V a c d b) a).symm
include h
lemma sheds : rum T theta=0:= by
 unfold rum; apply Finset.sum_eq_zero; intro a _
 simp only [strum,mul_add,Finset.sum_add_distrib,scan (V:=T 1),scans (T 2)]; simp only [← Finset.sum_add_distrib,←mul_add,h,mul_zero,Finset.sum_const_zero]
lemma ledger : street T = 2*rum T low := by
 rw [rum_std]
 have hh:= sheds T h
 unfold rum theta at hh; simp only [sub_mul, Finset.sum_sub_distrib] at hh
 exact congrArg _ (sub_eq_zero.mp hh)
end
end YM.SchemeRG11.Flare
