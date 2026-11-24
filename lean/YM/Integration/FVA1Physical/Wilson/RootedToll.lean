import YM.Integration.FVA1Physical.Wilson.DistributedBank
import YM.Integration.FVA1Physical.Round2.UnitGrid

/-! Polynomial size of the full normalized cumulant cost and coefficient
recovery from bounded evaluations on the unit interval. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Matrix MSbar MSbar.Lis MSbar.Cacao MSbar.Bakery MSbar.Mosaic
open scoped Classical Topology

private def moderate (f : ℝ→ℝ) := ∃ b : ℝ, Mosaic.Run atTop id f b

private lemma moderate_const (a:ℝ) : moderate (fun _=>a) := ⟨0,Mosaic.Run.token tendsto_id a⟩

private lemma moderate_id : moderate id := by
  refine ⟨1,(Mosaic.Run.core (X:=id) tendsto_id 1).alter ?_⟩
  exact Eventually.of_forall fun x=>Real.rpow_one x

private lemma moderate_add {f h : ℝ→ℝ} (hf : moderate f) (hh : moderate h) :
    moderate (fun x=> f x+h x) := by
  obtain ⟨a,A⟩:=hf
  obtain ⟨b,B⟩:=hh
  exact ⟨max a b,(A.loosen (le_max_left a b)).addR tendsto_id (B.loosen (le_max_right ..))⟩

private lemma moderate_mul {f h : ℝ→ℝ} (hf : moderate f) (hh : moderate h) :
    moderate (fun x=> f x*h x) := by
  obtain ⟨a,A⟩:=hf
  obtain ⟨b,B⟩:=hh
  exact ⟨a+b,A.mulR tendsto_id B⟩

private lemma moderate_pow {f : ℝ→ℝ} (hf : moderate f) (n : ℕ) : moderate (fun x=>f x^n) := by
  obtain ⟨a,A⟩:=hf
  exact ⟨_,A.raise tendsto_id n⟩

private lemma moderate_rail {f:ℝ→ℝ} (p m n : ℕ) (c:ℝ) (hf:moderate f) (i:ℕ) :
    moderate (fun x=>Whisk.rail p m n c (f x) i) := by
  induction i with
  | zero=>exact hf
  | succ i ih=>
    unfold Whisk.rail Whisk.stair
    exact moderate_add ih (moderate_add (moderate_add ih (moderate_mul (moderate_const _) ih))
      (moderate_mul (moderate_const _) (moderate_mul (moderate_const _)
        (moderate_add (moderate_pow ih 2) (moderate_mul (moderate_const _) (moderate_pow ih 2))))))

/-- All polynomial growth in the ambient mean, coefficient bank and divided
Schur correction is absorbed by the genuine distance to the native boundary. -/
theorem rooted_toll (p m q : ℕ) (C A B : ℝ) :
    ∀ᶠ y:ℝ in atTop,
      Real.exp (-Mosaic.Issue.thorn y m*spotN y) *
        ((p+1:ℕ)*(Spruce.cardK p m C (y*(1+y^3)^(m+1))*(A+y*B))) ≤ y^(-(q:ℝ)) := by
  have hf:=moderate_mul moderate_id (moderate_pow (moderate_add (moderate_const 1) (moderate_pow moderate_id 3)) (m+1))
  have hp:moderate (fun y=>Spruce.cardK p m C (y*(1+y^3)^(m+1))) :=
    moderate_mul (moderate_const _) (moderate_rail _ _ _ C (moderate_add hf hf) _)
  obtain ⟨b,poly⟩:=moderate_mul (moderate_const ((p+1:ℕ):ℝ))
    (moderate_mul hp (moderate_add (moderate_const A) (moderate_mul moderate_id (moderate_const B))))
  have decay:=(Mosaic.Issue.nearB (X:=id) tendsto_id 1 zero_lt_one m 0).1
  have vanish:=Mosaic.Van.mulL tendsto_id poly decay
  exact (vanish (-(q:ℝ)-1) (-(q:ℝ)) (by linarith)).mono fun y hy=>(le_abs_self _).trans hy

/-- A bound on the entire formal polynomial for 0≤t≤1 bounds each of its
coefficients with a constant depending only on the extraction order. -/
theorem price_from_taste (p : ℕ) (F H : PowerSeries ℝ) {B : ℝ} (cap : ∀ t∈ Set.Icc (0:ℝ) 1,
    |taste p F t - taste p H t|≤B) (i : Fin (p+1)) :
    |PowerSeries.coeff i.val F-PowerSeries.coeff i.val H|≤Round2.gridPrice p i*B := by
  let x:=Round2.unitGrid p
  let M:=Matrix.vandermonde x
  have unit : IsUnit M.det := by
    rw [isUnit_iff_ne_zero,Matrix.det_vandermonde_ne_zero_iff]
    intro j k eqn
    have h : (j.val:ℝ)/((p:ℝ)+1) = (k.val:ℝ)/((p:ℝ)+1) := eqn
    have ne : (p:ℝ)+1 ≠ 0 := by positivity
    apply Fin.ext
    exact_mod_cast (div_left_inj' ne).mp h
  let v (j : Fin (p+1)) := PowerSeries.coeff j.val F - PowerSeries.coeff j.val H
  have val(j : Fin (p+1)): taste p F (x j)-taste p H (x j)=∑ k, M j k * v k := by
    unfold taste
    rw [←sum_sub_distrib]
    change _=∑ k : Fin (p+1), x j ^ k.val * (PowerSeries.coeff k.val F - PowerSeries.coeff k.val H)
    rw [Fin.sum_univ_eq_sum_range (fun k:ℕ=>x j^k*(PowerSeries.coeff k F-PowerSeries.coeff k H)) (p+1)]
    exact sum_congr rfl fun k _=>(mul_sub _ _ _).symm
  have row : ∑ j, M⁻¹ i j * (taste p F (x j)-taste p H (x j))=v i := by
    simp_rw [val]
    simp only [mul_sum,←mul_assoc]
    rw [sum_comm]
    simp only [←sum_mul,←Matrix.mul_apply,Matrix.nonsing_inv_mul M unit]
    simp [Matrix.one_apply]
  change |v i|≤_
  rw [←row]
  refine (abs_sum_le_sum_abs ..).trans ?_
  rw [Round2.gridPrice,sum_mul]
  exact sum_le_sum fun j _=> (abs_mul ..).trans_le
    (mul_le_mul_of_nonneg_left (cap _ (Round2.unitGrid_mem p j)) (abs_nonneg _))

end YM.Integration.FVA1Physical.Wilson
