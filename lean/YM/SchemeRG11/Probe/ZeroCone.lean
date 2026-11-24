import YM.SchemeRG11.Probe.Harmonic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.MvPolynomial.Funext

/-!
Harmonic displacement numerators are determined even from the NONZERO complex
null cone. Used to detect all shell derivatives through the leading pole only;
knowing the span of arbitrary real separated readings of the whole rational
functions would not by itself suffice. No assumptions on an interacting tube.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.ConeProbe

open MvPolynomial Finset
open scoped BigOperators Classical ComplexConjugate

private abbrev Pol' := MvPolynomial (Fin 3) ℂ

private def rad : Pol' := ∑ i : Fin 3, X i * X i
private def divMap := MvPolynomial.finSuccEquiv ℂ 3
private lemma form_split : divMap quad = Polynomial.X^2 + Polynomial.C rad := by
  unfold quad rad divMap
  change MvPolynomial.finSuccEquiv ℂ 3 (∑ i : Fin (3+1), X i * X i) = _
  rw [Fin.sum_univ_succ]
  simp_rw [map_add, map_sum, map_mul, MvPolynomial.finSuccEquiv_X_zero,
    MvPolynomial.finSuccEquiv_X_succ]
  rw [pow_two]

private lemma rad_nz : rad ≠ 0 := by
  intro h
  have ht := congrArg (eval fun _ : Fin 3 => (1:ℂ)) h
  norm_num [rad,Fin.sum_univ_succ] at ht

lemma divide_of_zero_null (p : Pol)
    (hp : ∀ x : Vec, x ≠ 0 → eval x quad = 0 → eval x p = 0) : quad ∣ p := by
  let A := divMap p
  let Q := divMap quad
  have hQ : Q.Monic := by
    unfold Q
    rw [form_split]
    exact Polynomial.monic_X_pow_add_C rad (by decide : 2 ≠ 0)
  have hdeg : Q.natDegree = 2 := by
    unfold Q; rw [form_split,Polynomial.natDegree_X_pow_add_C]
  let S := Polynomial.modByMonic A Q
  have hd := Polynomial.natDegree_modByMonic_lt A hQ (fun h => by rw [h] at hdeg; simp at hdeg)
  rw [hdeg] at hd
  have hs : S.natDegree ≤ 1 := Nat.le_of_lt_succ hd
  obtain ⟨B,D,hBD⟩ := Polynomial.exists_eq_X_add_C_of_natDegree_le_one hs
  have test (w : Fin 3 → ℂ) (z : ℂ) (hz : z^2 = -eval w rad) (hw : z ≠ 0) :
      eval w B * z + eval w D = 0 := by
    let y := Fin.cons (α:=fun _ : Fin (3+1) => ℂ) z w
    have hv : y ≠ 0 := fun h => hw (congrFun h 0)
    have hh (p' : Pol) : eval y p' = ((divMap p').map (eval w)).eval z := MvPolynomial.eval_eq_eval_mv_eval' ..
    have HQ : (Q.map (eval w)).eval z = 0 := by
      unfold Q; simp only [form_split, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
        Polynomial.map_C, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_C, hz, neg_add_cancel]
    have HE : (A.map (eval w)).eval z=0 := (hh p).symm.trans (hp y hv ((hh quad).trans HQ))
    let Y := Polynomial.divByMonic A Q
    have hg : S + Q * Y = A := Polynomial.modByMonic_add_div A Q
    -- don't rewrite inside Y
    rw [hBD] at hg
    calc
      eval w B * z + eval w D = (((Polynomial.C B * Polynomial.X + Polynomial.C D + Q * Y).map (eval (R:=ℂ) w)).eval z) := by
        rw [Polynomial.map_add, Polynomial.map_mul (p:=Q), Polynomial.eval_add,
          Polynomial.eval_mul (p:= Q.map _), HQ]; simp
      _ = 0 := by rw [hg]; exact HE
  have hx (w : Fin 3 → ℂ) (hn : eval w rad ≠ 0) : eval w B = 0 ∧ eval w D = 0 := by
    obtain ⟨z,hz⟩ := IsAlgClosed.exists_pow_nat_eq (-eval w rad) (zero_lt_two (α:=ℕ))
    have he : z ≠ 0 := pow_ne_zero_iff (by decide : 2 ≠ 0) |>.mp (hz.trans_ne (neg_ne_zero.mpr hn))
    have ht := test w z hz he
    have hu := test w (-z) (by rw [neg_sq,hz]) (neg_ne_zero.mpr he)
    have h : 2*z * eval w B = 0 := by linear_combination ht - hu
    have hr : eval w B = 0 := (mul_eq_zero.mp h).resolve_left (mul_ne_zero (by norm_num) he)
    exact ⟨hr, by rw [hr,zero_mul,zero_add] at ht; exact ht⟩
  have zeroed (V : Pol') (hv : ∀ w, eval w rad ≠ 0 → eval w V = 0) : V = 0 := by
    refine (mul_eq_zero.mp (show rad*V=0 from MvPolynomial.funext ?_)).resolve_left rad_nz
    intro w; by_cases h : eval w rad=0
    · rw [map_mul,h,zero_mul,map_zero]
    · rw [map_mul,hv w h,mul_zero,map_zero]
  rw [zeroed B (fun w h => (hx w h).1), zeroed D (fun w h => (hx w h).2), map_zero,
    zero_mul, add_zero] at hBD
  obtain ⟨Y,hY⟩ := (Polynomial.modByMonic_eq_zero_iff_dvd hQ).mp hBD
  exact ⟨divMap.symm Y, divMap.injective (by rw [map_mul,AlgEquiv.apply_symm_apply]; exact hY)⟩

-- Fischer inner product. (Our star is on ordinary complex coefficients.)
def price (v : Axis →₀ ℕ) : ℕ := ∏ a, (v a).factorial
lemma price_pos (v) : 0 < price v := Finset.prod_pos fun _ _ => Nat.factorial_pos _
lemma price_up (v : Axis →₀ ℕ) (i : Axis) : price (v+Finsupp.single i 1) = (v i+1)*price v := by
  unfold price
  rw [← Finset.mul_prod_erase _ _ (mem_univ i), ← Finset.mul_prod_erase _ _ (mem_univ i)]
  simp only [Finsupp.add_apply,Finsupp.single_eq_same, Nat.factorial_succ]
  rw [mul_assoc]
  congr 2
  exact Finset.prod_congr rfl fun j hj => by
    rw [Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase hj), add_zero]

def pairP (p r : Pol) : ℂ :=
    Finsupp.sum (AddMonoidAlgebra.coeff p) (fun i x => star x * (price i : ℂ) * r.coeff i)

lemma pairP_add (p q r : Pol) : pairP (p+q) r = pairP p r + pairP q r := by
  unfold pairP
  change Finsupp.sum (AddMonoidAlgebra.coeff p+AddMonoidAlgebra.coeff q) _ = _
  exact Finsupp.sum_add_index' (by intro; simp) (by intros; simp [add_mul])

lemma pairP_monomial (k : Axis →₀ ℕ) (u : ℂ) (r : Pol) :
    pairP (monomial k u) r = star u * price k * r.coeff k := by
  unfold pairP
  exact sum_monomial_eq (by simp)

lemma pairP_X (i : Axis) (p r : Pol) : pairP (X i * p) r = pairP p (pderiv i r) := by
  induction p using MvPolynomial.induction_on' with
  | monomial n c =>
    rw [X,monomial_mul,one_mul, add_comm (Finsupp.single i 1), pairP_monomial, pairP_monomial,
      price_up, coeff_pderiv]
    push_cast
    ring
  | add p q hp hq => rw [mul_add,pairP_add,pairP_add,hp,hq]

lemma pairP_first_sum {ι : Type*} (s : Finset ι) (p : ι → Pol) (r : Pol) :
    pairP (∑ i ∈ s,p i) r = ∑ i ∈ s,pairP (p i) r := by
  induction s using Finset.induction_on with
  | empty => simp [pairP,MvPolynomial.sum_def]
  | insert i s hi ih => rw [sum_insert hi, sum_insert hi, pairP_add, ih]

lemma pairP_quad (p r : Pol) : pairP (quad*p) r = pairP p (lap r) := by
  unfold quad
  rw [sum_mul, pairP_first_sum]
  simp_rw [mul_assoc (X _) (X _), pairP_X]
  unfold pairP lap
  simp_rw [MvPolynomial.sum_def, MvPolynomial.coeff_sum, Finset.mul_sum]
  exact sum_comm

lemma self_ne (p : Pol) (hp : p ≠ 0) : pairP p p ≠ 0 := by
  have H (i : Axis →₀ ℕ) : star (p.coeff i) * (price i : ℂ) * p.coeff i =
      ((Complex.normSq (p.coeff i) * (price i : ℝ) : ℝ) : ℂ) := by
    push_cast
    rw [← Complex.mul_conj]
    change starRingEnd ℂ _ * _ * _ = _
    ring
  apply_fun Complex.re
  rw [Complex.zero_re, pairP, MvPolynomial.sum_def]
  simp_rw [H]
  rw [Complex.re_sum]; simp only [Complex.ofReal_re]
  apply ne_of_gt
  apply Finset.sum_pos
  · exact fun i hi => mul_pos (Complex.normSq_pos.mpr (MvPolynomial.mem_support_iff.mp hi)) (by exact_mod_cast price_pos i)
  exact Finset.nonempty_iff_ne_empty.mpr (fun h => hp (MvPolynomial.support_eq_empty.mp h))

lemma Lap_zeroCone (p : Pol) (h : lap p = 0)
    (he : ∀ x : Vec, x ≠ 0 → eval x quad = 0 → eval x p = 0) : p = 0 := by
  obtain ⟨A,hA⟩ := divide_of_zero_null p he
  by_contra hp
  apply self_ne p hp
  nth_rw 1 [hA]
  rw [pairP_quad,h]; simp [pairP]

end YM.SchemeRG11.ConeProbe
