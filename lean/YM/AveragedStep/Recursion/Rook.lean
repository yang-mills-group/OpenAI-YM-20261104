import YM.AveragedStep.Recursion.Earning
/- Pointwise recursion engine. -/
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep.SD
open Filter Function Lattice RG Loops Tree Wilson Precision Metric Set MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical InnerProductSpace
open Matrix Push.Uniform
variable {c f:Side}{G:Gauge}{S:StepData c f}{A:ChartRatio G}(F:Forest S.ratio)
variable (x:Site f)(R:ℕ→Lips G c f→ℝ)
    {τ:ℝ}{w:Lips G c f}{n k d q:ℕ}{a B:ℝ}
    (hT:1≤τ)(hA:0<a)(hB:0≤B)(hk:w.length+1≤k)(hc:clips w≤n)

/- Accounting *in the very law*. rust assumption below will be exact
physical-by-plant bill on this law. No formal witness assumed equals
physical, just use Azure polynomial SD equation to compute defect.
-/
include hT hA hB hk hc in
lemma row {L:ℝ}{C:ℕ→ℝ}(i:Key F G)
    (HG:Fund (S:=S) (τ:=τ) (a:=a) x (R d) d n k B q)
    (HT:∀ j∈active d,Fund (S:=S) (τ:=τ) (a:=a) x (R (d-j)) (d-j) (k+d+1) (k+d+1) B q)
    (hF:Signed (Shy S (fkey F i) w) (friends F A i w) L)
    (hJ:∀ p∈active d,Signed (Joy S (fkey F i) (p+1) w) (leap (A:=A) S (fkey F i) p w) (C p))
    (hI: ∃ r:ℝ, (offer (R d) (weigh F A i w)=offer (R d) (friends F A i w) - ∑ p∈active d,τ⁻¹^p *offer (R (d-p)) (leap (A:=A) S (fkey F i) p w)-r) ∧
       |r| ≤ B*stale τ d q*lens S a x (fkey F i::w)):
    |offer (R d) (weigh F A i w)| ≤ (L+(∑ p∈active d,C p)+1)*B*stale τ d q*coupon S a d x (fkey F i).1 w:=by
 let Z:= stale τ d q*coupon S a d x (fkey F i).1 w
 let T(p:ℕ):= τ⁻¹^p * offer (R (d-p)) (leap (A:=A) S (fkey F i) p w)
 obtain ⟨r,he,hr⟩:=hI
 have h(i:ℕ)(hi:i∈active d):|T i|≤ C i*(B*Z):=by
   refine (joy_price (HT i hi) hT hA hB ((on_tape ..).mp hi).2 (hJ i hi) hk).trans_eq ?_; unfold Z; ring
 have hf: |offer (R d) (friends F A i w)| ≤ L*(B*Z):= (shy_price HG hT hA hB hF hk hc).trans_eq (by unfold Z; ring)
 have hs: |r| ≤ B*Z:= by
   unfold Z; rw [← mul_assoc]; refine hr.trans (mul_le_mul_of_nonneg_left (coupon_border S a hA d x (n:=1) (by omega) (fkey F i).1 w ?_) (mul_nonneg hB (stale_pos hT ..)))
   rw [steps_cons,Nat.cast_one,one_mul,add_comm _ (steps (S:=S) _ _)]; simp
 have hl : |∑ p∈active d,T p| ≤ (∑ p∈active d,C p)*(B*Z):=by
   refine (Finset.abs_sum_le_sum_abs ..).trans ?_; rw [Finset.sum_mul]; exact Finset.sum_le_sum h
 rw [he]
 refine (abs_sub ..).trans ((add_le_add ((abs_sub _ _).trans (add_le_add hf hl)) hs).trans_eq ?_); unfold Z; ring

/- Sealed inverse action. -/
omit hT hB hk hc in
include hA in
lemma discharge (E:Wage G S.patch S.kernel A)(hS: Bid.Larger (G:=G) S){b:ℝ}(hS':a*(d+1:ℝ)≤b)(hZ:a*(d+1:ℝ)≤E.η/2){L:ℝ}(hL:0≤L)
    (h:∀ i:Key F G, |offer (R d) (weigh F A i w)| ≤ L * coupon S a d x (fkey F i).1 w)(j:Key F G):
    |R d (fkey F j::w)| ≤ L * (|E.μ*((↑(keyMask G):ℝ)*countCost (E.η-E.η/2))| *reachBit S.patch d a)*lens S b x (fkey F j::w):=by
 let T:=body A F
 let M(i:Key F G):=R d (fkey F i::w)
 have hu :IsUnit T.det:=(E.lawful S F rfl rfl hS).1
 let D:=T *ᵥ M
 have he(i:Key F G): offer (R d) (weigh F A i w)=D i:=by simp [weigh,map_sum,mulVec,dotProduct,T,D,M]
 have hz:T⁻¹ *ᵥ D=M:= by rw [show D=T *ᵥ M from rfl,mulVec_mulVec,T.nonsing_inv_mul hu,one_mulVec]
 simp_rw [he] at h
 let C (i:Key F G):=coupon S a d x (fkey F i).1 w
 let J:=E.μ*((↑(keyMask G):ℝ)*countCost (E.η-E.η/2))
 change |M j| ≤ _
 rw [← hz,mulVec,dotProduct]
 apply (Finset.abs_sum_le_sum_abs ..).trans
 calc
   _ ≤ L*(∑ i,|T⁻¹ j i| *C i):=by
      rw [Finset.mul_sum]; refine Finset.sum_le_sum ?_; intro i _; rw [abs_mul,mul_left_comm]; exact mul_le_mul_of_nonneg_left (h i) (abs_nonneg _)
   _ ≤ L*(J*reachBit S.patch d a*lens S b x (fkey F j::w)):=mul_le_mul_of_nonneg_left (back_shift S F E hS hA hS' hZ x j w) hL
   _ ≤ L*(|J| * reachBit S.patch d a)*lens S b x (fkey F j::w):=by
     rw [mul_assoc L]; apply mul_le_mul_of_nonneg_left _ hL; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le) (lens_pos ..).le
end YM.AveragedStep.SD
