import YM.Integration.WilsonOriginalRelativeFieldPartition

/-! The entire signed germ at one real occupied source, before fixing its remaining marked positions or Taylor directions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPinnedFieldWage
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise Stationary
open Further.PhysicalPeriodLimitF933 Macrame FVA1Physical FVA1Physical.TwoReset
open WilsonOriginalOccupiedFieldLayout WilsonOriginalRelativeMixedFields WilsonOriginalNamedRelativeRows
open WilsonOriginalPinnedDeckOrbit WilsonEmittedRootedJetWage WilsonOriginalSuspendedFootprint WilsonOriginalJointDeckMotion
open WilsonOriginalCenteredSeamSalary WilsonOriginalSuspendedTensor
open scoped Classical BigOperators ContDiff
variable {G:Gauge} {n N:Side} {V X ι:Type} [DecidableEq V] {o:Passport n V} {J:Census V}
  (h:n.val∣N.val) (M:ι→Row o J G X) (t:X) (s:J.Mode) (v:s.val)

private theorem entries {K:Type*} [Fintype K] (r:ℕ) (u:Fin r→Slot G N)
    (F:K→Joint G N→ℂ) (can:∀k,ContDiff ℝ r (F k)):
    entry r (∑k:K,F k) u=∑k:K,entry r (F k) u:=by
  unfold entry
  rw [iteratedFDeriv_sum_apply (fun k _=>(can k).contDiffAt),_root_.sum_apply]

theorem triangle {w:V→ℝ} {grades:V→ℕ} {σ C:ℝ} {order seats shelf:ℕ}
    (stock:Scene.Armada M w grades σ C order seats shelf) (hs:0<σ) (j r:ℕ) (b:PagesOf n N) (u:Fin r→Slot G N):
    ‖entry r (needle h M t s v j b) u‖ ≤
    ∑p:PagesOf n N,∑x:Site N,∑Y:s.val→PagesOf n N,if Y v=b then ‖entry r (joined h M t s x j (p,Y,u)) u‖ else 0:=by
  let term:=fun (p:PagesOf n N) (a:Site N×(s.val→PagesOf n N))=>if a.2 v=b then joined h M t s a.1 j (p,a.2,u) else 0
  have smooth (p:PagesOf n N) (a:Site N×(s.val→PagesOf n N)):ContDiff ℝ r (term p a):=by
    by_cases ok:a.2 v=b
    · rw [show term p a=joined h M t s a.1 j (p,a.2,u) from if_pos ok]
      exact (WilsonOriginalPaidMixedRegularity.suspended h M t p (selected h M s a.1 (p,a.2,u)) stock hs j).of_le (by simp)
    · rw [show term p a=0 from if_neg ok];exact contDiff_const
  have summed (p:PagesOf n N):ContDiff ℝ r (∑a,term p a):=by
    simp_rw [Finset.sum_fn];exact ContDiff.sum (fun a _=>smooth p a)
  rw [WilsonOriginalRelativeFieldPartition.parts h M t s v stock hs j r b u]
  change ‖entry r (∑p:PagesOf n N,∑a,term p a) u‖≤_
  rw [entries r u _ summed]
  refine (norm_sum_le _ _).trans (sum_le_sum fun p _=>?_ )
  rw [entries r u _ (smooth p)]
  refine (norm_sum_le _ _).trans_eq ?_
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl;intro x _;apply sum_congr rfl;intro Y _
  by_cases ok:Y v=b
  · simp [term,ok]
  · simp [term,ok,entry]

theorem original {w:V→ℝ} {grades:V→ℕ} {σ C:ℝ} {order seats shelf:ℕ}
    (stock:Scene.Armada M w grades σ C order seats shelf) (hs:0<σ) (j r:ℕ) (b:PagesOf n N):
    let z:Site N:=(page h (o.origin v.val) b).val
    (∑u:Fin r→Slot G N, Poly.toll w s * Real.exp ((σ/8)*(radius z (trace u):ℝ))*‖entry r (needle h M t s v j b) u‖)
      ≤ UVNext.PricedKernels.basin (σ/4)*(fee G σ r*C):=by
  intro z
  let D:=fun (x:Site N)(p:PagesOf n N)(Y:s.val→PagesOf n N)(u:Fin r→Slot G N)=>if Y v=b then
    Poly.toll w s*Real.exp ((σ/8)*span h o s.val z (p,Y,u))*‖entry r (joined h M t s x j (p,Y,u)) u‖ else 0
  have W:0≤Poly.toll w s:=prod_nonneg (fun v _=>(stock.positive v).le)
  calc
    _ ≤ ∑u:Fin r→Slot G N,∑p:PagesOf n N,∑x:Site N,∑Y:s.val→PagesOf n N,D x p Y u:=by
      apply sum_le_sum;intro u _
      apply (mul_le_mul_of_nonneg_left (triangle h M t s v stock hs j r b u) (mul_nonneg W (Real.exp_pos _).le)).trans
      simp_rw [mul_sum]
      apply sum_le_sum;intro p _;apply sum_le_sum;intro x _;apply sum_le_sum;intro Y _
      by_cases ok:Y v=b
      · simp only [D,if_pos ok]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        apply mul_le_mul_of_nonneg_left _ W
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact_mod_cast Finset.sup_mono (s₁:=trace u) (s₂:=trace u ∪ rootset h o s.val Y) Finset.subset_union_left
      · simp [D,ok]
    _ = ∑p:PagesOf n N,∑u:Fin r→Slot G N,∑x:Site N,∑Y:s.val→PagesOf n N,D x p Y u:=sum_comm
    _ = ∑p:PagesOf n N,∑x:Site N,∑u:Fin r→Slot G N,∑Y:s.val→PagesOf n N,D x p Y u:=sum_congr rfl fun p _=>sum_comm
    _ = ∑p:PagesOf n N,∑x:Site N,∑Y:s.val→PagesOf n N,∑u:Fin r→Slot G N,D x p Y u:=sum_congr rfl fun p _=>sum_congr rfl fun x _=>sum_comm
    _ = ∑x:Site N,∑p:PagesOf n N,∑Y:s.val→PagesOf n N,∑u:Fin r→Slot G N,D x p Y u:=sum_comm
    _ ≤ _:=by simpa only [Fintype.sum_prod_type,D,z] using WilsonOriginalPinnedMixedIncome.original h M t s stock hs j r v b

end YM.Integration.WilsonOriginalPinnedFieldWage
