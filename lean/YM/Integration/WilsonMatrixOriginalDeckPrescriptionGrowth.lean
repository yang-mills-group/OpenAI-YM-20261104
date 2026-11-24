import YM.Integration.WilsonMatrixOriginalDeckPrescriptionResolvent
import YM.Integration.WilsonMatrixOriginalDeckError

/-! Finite sums and products of the complete before-regulator two-clock matrices preserve a polynomial budget. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckPrescriptionGrowth
open Finset WilsonMatrixOriginalDeckRelative WilsonMatrixOriginalDeckError
open scoped Classical BigOperators Matrix
variable {I:Type*} [Fintype I]

abbrev Accounts (I:Type*) :=ℝ→ℝ→Matrix I I ℂ
def size (μ ν:ℝ):ℝ:=1+‖μ‖+‖ν‖
theorem size_ge (μ ν:ℝ):1 ≤ size μ ν:=by unfold size;linarith [norm_nonneg μ,norm_nonneg ν]

def Bound (A:Accounts I):Prop:=∃ C:ℝ,0<C ∧ ∃d:ℕ,∀μ ν,amount (A μ ν)≤C*(size μ ν)^d

theorem fixed (A:Matrix I I ℂ):Bound (fun _ _=>A):=by
  refine ⟨amount A+1,by linarith [nonneg A],0,?_⟩;intro μ ν;simp

variable {A B:Accounts I}

theorem add (ha:Bound A)(hb:Bound B):Bound (fun μ ν=>A μ ν+B μ ν):=by
  obtain ⟨C,hC,d,a⟩:=ha;obtain ⟨K,hK,e,b⟩:=hb
  refine ⟨C+K,add_pos hC hK,max d e,?_⟩;intro μ ν
  calc _≤ C*(size μ ν)^d+K*(size μ ν)^e:=(add_cost _ _).trans (add_le_add (a μ ν) (b μ ν))
       _≤ C*(size μ ν)^(max d e)+K*(size μ ν)^(max d e):=add_le_add
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (size_ge μ ν) (le_max_left _ _)) hC.le)
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (size_ge μ ν) (le_max_right _ _)) hK.le)
       _=_:=(add_mul _ _ _).symm

theorem negate (ha:Bound A):Bound (fun μ ν=> -(A μ ν)):=by
  obtain ⟨C,hC,d,c⟩:=ha;refine ⟨C,hC,d,?_⟩;intro μ ν;simpa [WilsonMatrixOriginalDeckRelative.amount] using c μ ν

theorem minus (ha:Bound A)(hb:Bound B):Bound (fun μ ν=>A μ ν-B μ ν):=by
  simpa only [sub_eq_add_neg] using add ha (negate hb)

theorem multiply (ha:Bound A)(hb:Bound B):Bound (fun μ ν=>A μ ν*B μ ν):=by
  obtain ⟨C,hC,d,a⟩:=ha;obtain ⟨K,hK,e,b⟩:=hb
  refine ⟨C*K,mul_pos hC hK,d+e,?_⟩;intro μ ν
  calc _≤(C*(size μ ν)^d)*(K*(size μ ν)^e):=(product_cost _ _).trans
          (mul_le_mul (a μ ν) (b μ ν) (nonneg _) ((nonneg _).trans (a μ ν)))
       _=_:=by rw [pow_add];ring

theorem powers (ha:Bound A)(n:ℕ):Bound (fun μ ν=>(A μ ν)^n):=by
  induction n with
  | zero => simpa only [pow_zero] using fixed (1:Matrix I I ℂ)
  | succ n ih=>simpa only [pow_succ] using multiply ih ha

theorem total {J:Type*}(s:Finset J)(A:J→Accounts I)(paid:∀j∈s,Bound (A j)):
    Bound (fun μ ν=>∑j∈s,A j μ ν):=by
  induction s using Finset.induction_on with
  | empty =>simpa only [Finset.sum_empty] using fixed (0:Matrix I I ℂ)
  | @insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact add (paid j (Finset.mem_insert_self _ _)) (ih fun i hi=>paid i (Finset.mem_insert_of_mem hi))

end YM.Integration.WilsonMatrixOriginalDeckPrescriptionGrowth
