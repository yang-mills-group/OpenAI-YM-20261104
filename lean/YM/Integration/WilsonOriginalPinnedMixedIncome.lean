import YM.Integration.WilsonOriginalRelativeMixedFields
import YM.Integration.WilsonOriginalRelativePageIncome

/-! A designated true source lift pays the sum over the centers of every contributing word. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPinnedMixedIncome
open Function Finset Lattice RG Wilson Marker Push.AbsoluteSums QuadraticLocal QuadraticLocal.Earn Stationary
open Further.PhysicalPeriodLimitF933 Macrame FVA1Physical FVA1Physical.TwoReset
open WilsonOriginalCenteredSeamSalary WilsonOriginalRelativeMixedFields WilsonOriginalSuspendedTensor
open WilsonEmittedRootedJetWage WilsonOriginalJointDeckMotion UVNext.PricedKernels
open scoped Classical BigOperators ContDiff
variable {G:Gauge} {n N:Side} {V X ι:Type} [DecidableEq V] {o:Passport n V} {J:Census V}

theorem range (S:Finset (Site N)) (z x:Site N) (near:z∈S):
    separation z x ≤ radius x S ∧ radius z S ≤ 2*radius x S:=by
  have born:separation z x≤radius x S:=by rw [separation_comm];exact le_sup near
  refine ⟨born,Finset.sup_le fun y hy=>?_⟩
  have endpt:separation x y≤radius x S:=le_sup hy
  exact (separation_triangle z x y).trans ((Nat.add_le_add born endpt).trans_eq (two_mul _).symm)

theorem decay (S:Finset (Site N)) (z x:Site N) (near:z∈S) {σ:ℝ} (hs:0<σ):
    Real.exp ((σ/8)*(radius z S:ℝ))≤ Real.exp (-(σ/4)*(separation z x:ℝ))*Real.exp ((σ/2)*(radius x S:ℝ)):=by
  have both:=range S z x near
  have D:(separation z x:ℝ)≤(radius x S:ℝ):=Nat.cast_le.mpr both.1
  have Smax:(radius z S:ℝ)≤2*(radius x S:ℝ):=by exact_mod_cast both.2
  rw [←Real.exp_add,Real.exp_le_exp]
  nlinarith [mul_le_mul_of_nonneg_left D hs.le,mul_le_mul_of_nonneg_left Smax hs.le]

variable (h:n.val∣N.val) (M:ι→Row o J G X) (t:X) (s:J.Mode)
theorem original {w:V→ℝ} {grades:V→ℕ} {σ C:ℝ} {order seats shelf:ℕ}
    (stock:Scene.Armada M w grades σ C order seats shelf) (hs:0<σ) (j r:ℕ) (v:s.val) (b:Fin (Pages n N)):
    let z:Site N:=(page h (o.origin v.val) b).val
    (∑x:Site N,∑u:Choice s.val n N G r,if u.2.1 v=b then
        Poly.toll w s * Real.exp ((σ/8)*span h o s.val z u) * ‖entry r (joined h M t s x j u) u.2.2‖ else 0)
       ≤ UVNext.PricedKernels.basin (σ/4) * (fee G σ r*C):=by
  intro z
  have w0:0≤Poly.toll w s:=prod_nonneg (fun v _=>(stock.positive v).le)
  let E:=fun x:Site N=>Real.exp (-(σ/4)*(separation z x:ℝ))
  have bound (x:Site N):
      (∑u:Choice s.val n N G r,if u.2.1 v=b then Poly.toll w s*Real.exp ((σ/8)*span h o s.val z u)*‖entry r (joined h M t s x j u) u.2.2‖ else 0)
      ≤ E x*(fee G σ r*C):=by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (WilsonOriginalRelativeMixedFields.original h M t s x stock hs j r) (Real.exp_pos _).le)
    rw [mul_sum]
    apply sum_le_sum
    intro u _
    by_cases eq:u.2.1 v=b
    · rw [if_pos eq]
      let S:=WilsonOriginalSuspendedFootprint.trace u.2.2 ∪ rootset h o s.val u.2.1
      have zmem:z∈S:=mem_union_right _ (mem_image.mpr ⟨v,mem_univ _,by rw [eq]⟩)
      have T:=decay S z x zmem hs
      have paid:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left T w0) (norm_nonneg (entry r (joined h M t s x j u) u.2.2))
      unfold span E;convert paid using 1; ring
    · rw [if_neg eq]
      exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (mul_nonneg w0 (Real.exp_pos _).le) (norm_nonneg _))
  have all:=Finset.sum_le_sum (s:=univ) (fun x _=>bound x)
  rw [←sum_mul] at all
  exact all.trans (mul_le_mul_of_nonneg_right (funnel (by positivity:0<σ/4) z)
    (mul_nonneg (nonnegative G hs r) (budget_nonneg (stock.suggests (0:Site n)))))

end YM.Integration.WilsonOriginalPinnedMixedIncome
