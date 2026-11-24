import YM.Integration.WilsonOriginalCoverNominalPairSource

/-! Recover a single connected angular tensor from its full-period copy sum.
The root, the other centres and the angular addresses are translated together.
For positive angular rank an address in the tuple separates distinct copies. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOriginalConnectedDeckLocality
open Finset Function
open scoped BigOperators
variable {C X:Type*} [Fintype C] [Fintype X]

private theorem subtotal {I:Type*} [Fintype I] (r:I→X) (hr:Injective r)
    (fee:X→ℝ) (hn:∀x,0 ≤ fee x) : (∑i,fee (r i)) ≤ ∑x,fee x:=by
  classical
  rw [←sum_image (fun a _ b _ h=>hr h)]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun x _ _=>hn x)

theorem original (base:C) (roll:C→X≃X) (home:∀x,roll base x=x)
    (K:X→ℂ) (span:X→ℝ) {side diameter ρ M:ℝ} (native:0 ≤ side) (cable:diameter ≤ side/8) (strip:0 ≤ ρ)
    (apart:∀c d x y,c≠d → roll c x=roll d y → side-2*diameter ≤ span x+span y)
    (orbit:∀x,∑c,K (roll c x)=0) (income:(∑x,Real.exp (ρ*span x)*‖K x‖) ≤ M) :
    (∑x,Real.exp (ρ*span x/2)*‖K x‖) ≤ 2*Real.exp (-(ρ*side)/8)*M:=by
  classical
  let Near:={x:X//span x < side/4}
  let Far:={x:X//¬span x < side/4}
  let Away:={c:C//c≠base}
  let image (a:Near×Away):X:=roll a.2.val a.1.val
  let fee (x:X):=Real.exp (ρ*span x)*‖K x‖
  let spent (x:X):=Real.exp (ρ*span x/2)*‖K x‖
  let discount:=Real.exp (-(ρ*side)/8)
  have fee0 (x:X):0 ≤ fee x:=mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  have inject:Injective image:=by
    intro a b h
    by_cases pages:a.2.val=b.2.val
    · have cp:a.2=b.2:=Subtype.ext pages
      apply Prod.ext _ cp
      apply Subtype.ext
      apply (roll a.2.val).injective
      simpa only [image,cp] using h
    · have split:=apart _ _ _ _ pages h
      have ax:=a.1.prop
      have bx:=b.1.prop
      linarith only [ax,bx,split,cable,native]
  have localFee (a:Near×Away):Real.exp (ρ*span a.1.val/2)*‖K (image a)‖ ≤ discount*fee (image a):=by
    have shift:roll a.2.val a.1.val=roll base (image a):=(home _).symm
    have spacing:=apart _ _ _ _ a.2.prop shift
    have s:span a.1.val/2+side/8 ≤ span (image a):=by linarith only [a.1.prop,spacing,cable,native]
    dsimp only [discount,fee]
    rw [←mul_assoc,←Real.exp_add]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_nonneg strip (sub_nonneg.mpr s)]
  have isolate (x:X):‖K x‖ ≤ ∑c:Away,‖K (roll c.val x)‖:=by
    let only:={c:C//¬c≠base}
    let o:only:=⟨base,by simp⟩
    have one:(univ:Finset only)={o}:=by
      ext c;simp only [mem_univ,mem_singleton,true_iff]
      exact Subtype.ext (not_ne_iff.mp c.prop)
    have cut: (∑c:only,K (roll c.val x))=K x:=by rw [one,sum_singleton];exact congrArg K (home x)
    have balance:=Fintype.sum_subtype_add_sum_subtype (fun c:C=>c≠base) (fun c=>K (roll c x))
    rw [cut,orbit] at balance
    have cancel:(∑c:Away,K (roll c.val x)) = -(K x):=by rw [eq_neg_iff_add_eq_zero];exact balance
    calc
      _ = ‖∑c:Away,K (roll c.val x)‖ := by rw [cancel,norm_neg]
      _  ≤  _ := norm_sum_le _ _
  have near:(∑x:Near,spent x.val) ≤ discount*M:=calc
    _  ≤  ∑x:Near,∑c:Away,Real.exp (ρ*span x.val/2)*‖K (roll c.val x.val)‖:=by
      apply sum_le_sum;intro x _;rw [←mul_sum]
      exact mul_le_mul_of_nonneg_left (isolate _) (Real.exp_pos _).le
    _ = ∑a:Near×Away,Real.exp (ρ*span a.1.val/2)*‖K (image a)‖:=by rw [Fintype.sum_prod_type]
    _  ≤  ∑a:Near×Away,discount*fee (image a):=sum_le_sum (fun a _=>localFee a)
    _  ≤  _ :=by rw [←mul_sum];exact mul_le_mul_of_nonneg_left ((subtotal image inject fee fee0).trans income) (Real.exp_pos _).le
  have far:(∑x:Far,spent x.val) ≤ discount*M:=calc
    _  ≤  ∑x:Far,discount*fee x.val:=by
      apply sum_le_sum;intro x _
      dsimp only [spent,discount,fee];rw [←mul_assoc,←Real.exp_add]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _);apply Real.exp_le_exp.mpr
      have lower:=le_of_not_gt x.prop
      nlinarith only [mul_nonneg strip (sub_nonneg.mpr lower)]
    _  ≤  _ :=by rw [←mul_sum];exact mul_le_mul_of_nonneg_left ((subtotal Subtype.val Subtype.val_injective fee fee0).trans income) (Real.exp_pos _).le
  have split:=Fintype.sum_subtype_add_sum_subtype (fun x=>span x < side/4) spent
  change (∑x,spent x) ≤ 2*discount*M
  linarith only [near,far,split]

end YM.Integration.WilsonOriginalConnectedDeckLocality
