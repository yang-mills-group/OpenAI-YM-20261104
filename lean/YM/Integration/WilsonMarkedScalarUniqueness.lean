import YM.Integration.WilsonMarkedScalarEquation

/-! Coefficient uniqueness in the normalized scalar kinetic equation. Only the
primitive Hessian prices enter; the complete reciprocal and every homogeneous
marked mode are then fixed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMarkedScalarUniqueness
open Function Finset PowerSeries FormalBulk08 Wine Comparison.RG02 Adjacent Moving.Path
open WilsonMarkedKineticDefect WilsonMarkedKineticGerm WilsonMarkedScalarEquation
open scoped BigOperators Classical

private theorem unique {A B : PowerSeries ℂ} {p cap : ℕ} {a b : ℕ → ℂ}
    (oneA : coeff 0 A=1) (oneB : coeff 0 B=1)
    (fees : ∀ j ≤ p, a j = b j)
    (left : Series.Through p (A^2) (table cap a A))
    (right : Series.Through p (B^2) (table cap b B)) :
    Series.Through p A B := by
  intro e
  induction e using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hn0 : n = 0
    · simp only [hn0,oneA,oneB]
    have hs : coeff n (A^2) = coeff n (B^2) := by
      rw [left n hn,right n hn,table,table,map_sum,map_sum]
      apply sum_congr rfl
      intro j _
      have Aterm := term (a j) A (1:PowerSeries ℂ) j n
      have Bterm := term (b j) B (1:PowerSeries ℂ) j n
      simp only [mul_one] at Aterm Bterm
      rw [Aterm,Bterm]
      by_cases hje : j ≤ n
      · simp only [if_pos hje]
        rw [fees j (hje.trans hn)]
        by_cases hj0 : j = 0
        · simp only [hj0,pow_zero]
        · have hprev : Series.Through (n-j) A B :=
            fun m hm => ih m (by omega) (by omega)
          rw [hprev.pow j (n-j) le_rfl]
      · simp only [if_neg hje,zero_mul]
    have hline : coeff n ((A-B)*(A+B)) = (coeff n A-coeff n B)*2 := by
      rw [coeff_mul,Finset.sum_eq_single (n,0)]
      · simp only [map_sub,map_add,oneA,oneB,one_add_one_eq_two]
      · intro ij hij hother
        have ht : ij.1+ij.2=n := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
        have hlt : ij.1 < n := by
          by_contra! hnot
          apply hother
          apply Prod.ext <;> dsimp <;> omega
        rw [map_sub,ih ij.1 hlt (by omega),sub_self,zero_mul]
      · intro bad
        exact (bad (Finset.HasAntidiagonal.mem_antidiagonal.mpr (Nat.add_zero n))).elim
    have hz : (coeff n A - coeff n B)*(2 : ℂ)=0 := by
      rw [←hline,show (A-B)*(A+B)=A^2-B^2 by ring,map_sub,hs,sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (by norm_num))

/-- Agreement of the independently prescribed scalar with the measured
incoming kinetic coefficients through p determines the genuine physical
reverse rate at all orders through p. -/
theorem primitive (c : Caliber) (cap p : ℕ) (hp : p ≤ cap) (H : Pence) (hH : Wine.Fresh H)
    (fees : ∀ j ≤ p, c.measure j = PowerSeries.coeff j H) :
    WilsonMarkedKineticGerm.Through p (rate (c.back cap))
      (PowerSeries.map Complex.ofRealHom (Wine.bookH H)) := by
  let A := rate (c.back cap)
  let B := PowerSeries.map Complex.ofRealHom (Wine.bookH H)
  have a₀ : coeff 0 A = 1 := by
    dsimp only [A,rate,germ]
    rw [PowerSeries.coeff_mk,Moving.Shift.mzero,(c.back cap).origin,Complex.ofReal_one]
  have b₀ : coeff 0 B = 1 := by
    change coeff 0 (PowerSeries.map Complex.ofRealHom (Wine.bookH H))=1
    rw [coeff_map,Wine.book_fresh]
    rfl
  exact unique a₀ b₀ (fun j hj => congrArg Complex.ofReal (fees j hj))
    (fun n _ => congrArg (coeff n) (WilsonMarkedScalarEquation.physical c cap))
    (fun n hn => WilsonMarkedScalarEquation.formal H hH cap n (hn.trans hp))

/-- The native coupling and field factors therefore agree for every
marked angular rank, independent of the choice of marked source. -/
theorem weight (c : Caliber) (cap p : ℕ) (hp : p ≤ cap) (H : Pence) (hH : Wine.Fresh H)
    (fees : ∀ j ≤ p, c.measure j = PowerSeries.coeff j H)
    {e : ℕ} (he : e ≤ p) (j r : ℕ) :
    physicalWeight c cap e j r = formalWeight H e j r :=
  WilsonMarkedKineticGerm.homogeneous c cap p H (primitive c cap p hp H hH fees) he r

end YM.Integration.WilsonMarkedScalarUniqueness
