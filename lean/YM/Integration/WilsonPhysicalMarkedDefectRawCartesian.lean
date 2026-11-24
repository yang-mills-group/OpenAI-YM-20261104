import YM.Integration.WilsonPhysicalMarkedDefectRawConvolution

/-! A finite signed partition reads one truncation of the whole product; the
price for dropping terms above this degree is the product of the original
finite absolute coefficient sums, with one factor per actual block. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalMarkedDefect.RawProduct
open PowerSeries Finset RawBank
open scoped BigOperators Classical

theorem positive (p:ℕ) (T:PowerSeries ℂ):0≤belt p T:=sum_nonneg fun _ _=>norm_nonneg _

theorem unit (p:ℕ) (g:ℝ):cash p g 1=1 ∧ belt p 1=1:=by
  simp [cash,belt,coeff_one,apply_ite]

theorem menu {ι:Type} (p:ℕ) (s:Finset ι) (f:ι→PowerSeries ℂ):
    belt p (∏i∈s,f i)≤∏i∈s,belt p (f i):=by
  classical
  induction s using Finset.induction_on with
  | empty=>simp only [prod_empty,(unit p 0).2,le_refl]
  | @insert a s ha ih=>
    rw [prod_insert ha,prod_insert ha]
    exact (entries p _ _).trans (mul_le_mul_of_nonneg_left ih (positive p _))

theorem whole {ι:Type} (p:ℕ) {g:ℝ} (gp:0≤g) (small:g≤1) (s:Finset ι) (f:ι→PowerSeries ℂ):
    ‖(∏i∈s,cash p g (f i))-cash p g (∏i∈s,f i)‖≤
      s.card*g^(p+1)*(∏i∈s,belt p (f i)):=by
  classical
  induction s using Finset.induction_on with
  | empty=>simp [(unit p g).1]
  | @insert a s ha ih=>
    let T:=∏i∈s,f i
    let H:=∏i∈s,cash p g (f i)
    let B:=∏i∈s,belt p (f i)
    have add:‖cash p g (f a)*H-cash p g (f a*T)‖≤
        ‖cash p g (f a)‖*‖H-cash p g T‖+‖cash p g (f a)*cash p g T-cash p g (f a*T)‖:=by
      rw [←norm_mul]
      have form:cash p g (f a)*H-cash p g (f a*T)=
        cash p g (f a)*(H-cash p g T)+(cash p g (f a)*cash p g T-cash p g (f a*T)):=by ring
      rw [form]
      exact norm_add_le _ _
    have single:‖cash p g (f a)*cash p g T-cash p g (f a*T)‖≤g^(p+1)*(belt p (f a)*B):=by
      rw [norm_sub_rev]
      exact (response p gp small (f a) T).trans
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (menu p s f) (positive p _)) (pow_nonneg gp _))
    rw [prod_insert ha,prod_insert ha,prod_insert ha,card_insert_of_notMem ha,Nat.cast_add,Nat.cast_one]
    calc
      _ ≤ _ := add
      _ ≤ belt p (f a)*(s.card*g^(p+1)*B)+g^(p+1)*(belt p (f a)*B):=
        add_le_add (mul_le_mul (bounded p gp small (f a)) ih (norm_nonneg _) (positive p _)) single
      _ = _:=by ring

end YM.Integration.WilsonPhysicalMarkedDefect.RawProduct
