import YM.Integration.WilsonCenteredMaskHardBudget

/-! Original hard-owner sets chosen by the complete captured source. One
forced allowance pays the whole nonempty family before the capture divides. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredOccupiedHardSets
open Finset RG Wilson Marker Lattice QuadraticLocal Push.Local WilsonCenteredOccupiedFamilies WilsonCenteredKeptOwners
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V X : Type} [DecidableEq V] {R : Census V} {o : V→Site n}
    {P : Rep G n} (H : Hard X P.p P.activities.forced P.activities.K o R) (w : V→ℝ) (hw : ∀v,0<w v)

abbrev Chosen := { I : Finset ℕ // I.Nonempty }

/-- The polynomial is retained for mixing with regular deposited letters. -/
def word (s : R.Mode) (I : Chosen) (x : X) (U : Config G n) : Poly R :=
  ∏j∈I.val,dye s (H.hard x j U)

include hw in
theorem original (s : R.Mode) (Z : Support n) (home : ∀v∈s.val,o v∈Z) {κ : ℝ}
    (paid : H.Paid w P.p.B P.p.supportExponent κ) :
    ∃ k : Chosen→ℝ,(∀I,0≤k I) ∧ (∀I,k I≠0 → ∀j∈I.val,∃v∈Z,v∈Push.Local.patch P.activities j) ∧
    (∀I x U, Poly.price w (word H s I x U)≤k I) ∧
    SumBudget (salary P Subtype.val k) (Real.exp (s.val.card*κ)-1) :=by
  obtain ⟨e,pos,location,cap,fee⟩:=WilsonCenteredMaskHardBudget.original H w hw s paid
  let k (I : Chosen) :=∏j∈I.val,e j
  have nonneg (I) : 0≤k I := prod_nonneg (fun j _=>pos j)
  refine ⟨k,nonneg,?_,?_,?_⟩
  · intro I active j inside
    have used : e j≠0 :=fun absent=>active (prod_eq_zero inside absent)
    obtain ⟨v,inS,hit⟩:=location j used
    exact ⟨o v,home v inS,hit⟩
  · intro I x U
    apply (Poly.multiple hw I.val (fun j=>dye s (H.hard x j U))).trans
    exact prod_le_prod (fun j _=>Poly.nonnegative hw _) (fun j _=>cap j x U)
  · have pile:=sumBudget_subtype (fun I : Finset ℕ=>I.Nonempty) (sumBudget_exponential fee)
    convert pile using 1
    ext I
    simp only [salary,if_pos I.property,k,mul_sum,Real.exp_sum,prod_mul_distrib]

theorem divided {r κ : ℝ} (r0 : 0≤r) (k0 : 0≤κ) (small : κ≤1) :
    Real.exp (r*κ)-1 ≤ (r*κ)*Real.exp r :=by
  have le := Real.add_one_le_exp (-(r*κ))
  have h : 1-Real.exp (-(r*κ))≤r*κ :=by linarith
  have rev : Real.exp (r*κ)*Real.exp (-(r*κ))=1 :=by rw [←Real.exp_add,add_neg_cancel,Real.exp_zero]
  calc
    _ = Real.exp (r*κ)*(1-Real.exp (-(r*κ))) :=by rw [mul_sub,mul_one,rev]
    _ ≤ Real.exp (r*κ)*(r*κ) :=mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ ≤ _ := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_of_le_one_right r0 small)) (mul_nonneg r0 k0)

end YM.Integration.WilsonCenteredOccupiedHardSets
