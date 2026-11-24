import YM.Integration.WilsonSeparatedPrefixCanonicalWallet
import YM.Lodestar.TwinCost

/-! Clear the physical source wallet only once per actually present slot. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCanonicalSourceDebit
open Function Finset Lattice Wilson Marker Lodestar
open scoped BigOperators Classical
variable {V:Type}[Fintype V][DecidableEq V]

theorem original {x:ℝ}(hot:2+32*((Fintype.card V:ℝ)+1)≤x)(D:ℕ)(w₀ P B:V → ℝ)
    (wp:∀v,0<w₀ v)(pp:∀v,0≤P v)(bp:∀v,0≤B v)
    (old:∀v,(w₀ v)⁻¹≤x^D)(heads:∀v,P v≤x^D)(debt:∀v,B v≤x^D):
    let a:=fun v=>x^6*P v+x^2*B v
    let w:=WilsonSeparatedPrefixCanonicalWallet.seat w₀ a B
    (∀v,0<w v) ∧ ∀s:(Marks V).Mode,(Poly.toll (fun v=>w v^2) s)⁻¹≤x^((D+7)*Fintype.card V):=by
  intro a w
  have xn:1≤x:=by linarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  have xp:0≤x:=zero_le_one.trans xn
  have ap(v):0≤a v:=add_nonneg (mul_nonneg (pow_nonneg xp _) (pp v)) (mul_nonneg (pow_nonneg xp _) (bp v))
  obtain ⟨positive,_,inverse,_,_⟩:=WilsonSeparatedPrefixCanonicalWallet.original w₀ a B wp ap bp
  have raised:x^D≤x^(D+6):=pow_le_pow_right₀ xn (by omega)
  have one:1≤x^(D+6):=one_le_pow₀ xn
  have six:x^2≤x^6:=pow_le_pow_right₀ xn (by omega)
  have fee(v):a v≤2*x^(D+6):=by
    change x^6*P v+x^2*B v≤_
    have l:=mul_le_mul (show x^6≤x^6 from le_rfl) (heads v) (pp v) (pow_nonneg xp _)
    have r:=mul_le_mul six (debt v) (bp v) (pow_nonneg xp _)
    have prod:x^6*x^D=x^(D+6):=by rw [pow_add,mul_comm]
    linarith
  have seat(v):(w v^2)⁻¹≤x^(D+7):=by
    rw [inverse]
    unfold WilsonSeparatedPrefixCanonicalWallet.debit
    have original:1+(w₀ v)⁻¹≤2*x^(D+6):=by linarith [old v]
    have bank:1+a v+B v≤4*x^(D+6):=by linarith [fee v,debt v]
    have group:0≤8*((Fintype.card V:ℝ)+1):=by positivity
    calc
      _ ≤ 2*x^(D+6)+(8*((Fintype.card V:ℝ)+1))*(4*x^(D+6)):=add_le_add original (mul_le_mul_of_nonneg_left bank group)
      _ = (2+32*((Fintype.card V:ℝ)+1))*x^(D+6):=by ring
      _ ≤ x*x^(D+6):=mul_le_mul_of_nonneg_right hot (pow_nonneg xp _)
      _ = x^(D+7):=by simpa only [pow_succ] using (mul_comm x (x^(D+6)))
  refine ⟨positive,fun s=>?_⟩
  simp only [Poly.toll,←Finset.prod_inv_distrib]
  calc
    _ ≤ ∏_v∈s.val,x^(D+7):=Finset.prod_le_prod (fun v _=>inv_nonneg.mpr (sq_nonneg _)) (fun v _=>seat v)
    _ = x^((D+7)*s.val.card):=by rw [Finset.prod_const,pow_mul]
    _ ≤ _:=pow_le_pow_right₀ xn (Nat.mul_le_mul_left _ (Finset.card_le_univ _))

end YM.Integration.WilsonSeparatedPrefixCanonicalSourceDebit
