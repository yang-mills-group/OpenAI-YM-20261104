import YM.Integration.WilsonMarkedScalarEquation

/-! Coefficientwise continuity through a fixed order of the triangular
change of coupling and its true multiplicative inverse. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonKineticRebookingContinuity
open Filter Finset PowerSeries FormalBulk08 FormalBulk08.Series FormalBulk08.Wine
open scoped Classical Topology
variable {ι : Type*} {l : Filter ι}

def middle (n : ℕ) := ((antidiagonal n).erase (n,0)).erase (0,n)

private theorem low {n : ℕ} {u : ℕ×ℕ} (inside : u∈middle n) : u.1<n ∧ u.2<n := by
  obtain ⟨h0,hn,ht⟩ := (show u≠(0,n) ∧ u≠(n,0) ∧ u.1+u.2=n by
    simpa only [middle,mem_erase,HasAntidiagonal.mem_antidiagonal] using inside)
  constructor
  · by_contra! h
    exact hn (Prod.ext (by omega) (by omega))
  · by_contra! h
    exact h0 (Prod.ext (by omega) (by omega))

private theorem pair (n : ℕ) (hn : 0<n) (A B : PowerSeries ℝ)
    (ha : Fresh A) (hb : Fresh B) :
    coeff n (A*B)=coeff n A+coeff n B+∑u∈middle n,coeff u.1 A*coeff u.2 B := by
  let f := fun u : ℕ×ℕ=>coeff u.1 A*coeff u.2 B
  have one : (n,0)∈antidiagonal n := by simp
  have two : (0,n)∈(antidiagonal n).erase (n,0) := by
    simp [hn.ne']
  rw [coeff_mul]
  change (∑u∈antidiagonal n,f u)=_
  rw [←add_sum_erase _ _ one,←add_sum_erase _ _ two]
  change coeff n A*coeff 0 B+(coeff 0 A*coeff n B+_) = _
  rw [ha,hb,one_mul,mul_one,add_assoc]
  rfl

private theorem power (A : ι→PowerSeries ℝ) (B : PowerSeries ℝ) (m : ℕ)
    (paid : ∀i ≤ m,Tendsto (fun t=>coeff i (A t)) l (𝓝 (coeff i B)))
    (q : ℕ) : ∀i ≤ m,Tendsto (fun t=>coeff i ((A t)^q)) l (𝓝 (coeff i (B^q))) := by
  induction q with
  | zero => intro i _; simp only [pow_zero]; exact tendsto_const_nhds
  | succ q ih =>
    intro i hi
    simp_rw [pow_succ,coeff_mul]
    apply tendsto_finsetSum
    intro u hu
    have ht : u.1+u.2=i := HasAntidiagonal.mem_antidiagonal.mp hu
    exact (ih _ (by omega)).mul (paid _ (by omega))

private theorem earnings (H : PowerSeries ℝ) (hH : Fresh H) (n : ℕ) :
    coeff n ((bookH H)^2)=∑ j∈range (n+1),coeff j H * coeff (n-j) ((bookH H)^j) := by
  let A := bookH H
  let U := bookU H
  have unit : A*U=1 := book_equal H
  have relation : H.subst (X*A)*U^2=1 := by rw [show X*A=runic H from forward_green H];exact correction_read H hH
  have square : A^2=H.subst (X*A) := by
    calc
      _=1*A^2 := (one_mul _).symm
      _=(H.subst (X*A)*U^2)*A^2 := by rw [relation]
      _=H.subst (X*A)*(A*U)^2 := by ring
      _=_ := by rw [unit,one_pow,mul_one]
  have head : coeff 0 (X*A)=0 := by rw [show X*A=runic H from forward_green H];exact runic_phi H
  change coeff n (A^2)=_
  rw [square,Series.subst_coeff head H n n le_rfl]
  apply sum_congr rfl
  intro j hj
  have order : j≤n := Nat.le_of_lt_succ (mem_range.mp hj)
  have h := WilsonMarkedScalarEquation.term (coeff j H) A (1:PowerSeries ℝ) j n
  have cost : coeff j H * coeff n ((X*A)^j) = coeff (n-j) (A^j) * coeff j H := by
    simpa only [mul_one,coeff_C_mul,if_pos order] using h
  exact cost.trans (mul_comm _ _)

private theorem half (n : ℕ) (hn : 0<n) (A : PowerSeries ℝ) (hA : Fresh A) :
    (coeff n (A^2)-(∑u∈middle n,coeff u.1 A*coeff u.2 A))/2=coeff n A := by
  rw [pow_two,pair n hn A A hA hA]
  ring

theorem forward (p : ℕ) (H : ι→PowerSeries ℝ) (C : PowerSeries ℝ)
    (honest : ∀t,Fresh (H t)) (hC : Fresh C)
    (income : ∀j ≤ p,Tendsto (fun t=>coeff j (H t)) l (𝓝 (coeff j C))) :
    ∀ e ≤ p,Tendsto (fun t=>coeff e (bookH (H t))) l (𝓝 (coeff e (bookH C))) := by
  intro e
  induction e using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hz : n=0
    · subst n
      simp only [show ∀T : PowerSeries ℝ,coeff 0 (bookH T)=1 from book_fresh]
      exact tendsto_const_nhds
    have hn0 : 0<n := Nat.pos_of_ne_zero hz
    have square : Tendsto (fun t=>coeff n ((bookH (H t))^2)) l (𝓝 (coeff n ((bookH C)^2))) := by
      simp_rw [earnings _ (honest _),earnings _ hC]
      apply tendsto_finsetSum
      intro j hj
      have hjn := Nat.le_of_lt_succ (mem_range.mp hj)
      apply (income j (hjn.trans hn)).mul
      by_cases zero : j=0
      · subst j; simp only [pow_zero]; exact tendsto_const_nhds
      exact power _ _ (n-j) (fun i hi=>ih i (by omega) (by omega)) j _ le_rfl
    have cross : Tendsto (fun t=>∑u∈middle n,coeff u.1 (bookH (H t))*coeff u.2 (bookH (H t))) l
        (𝓝 (∑u∈middle n,coeff u.1 (bookH C)*coeff u.2 (bookH C))) := by
      apply tendsto_finsetSum
      intro u hu
      exact (ih _ (low hu).1 ((low hu).1.le.trans hn)).mul (ih _ (low hu).2 ((low hu).2.le.trans hn))
    simpa only [half n hn0 _ (book_fresh _)] using (square.sub cross).div_const (2:ℝ)

private theorem complement (n : ℕ) (hn : 0<n) (H : PowerSeries ℝ) :
    -(coeff n (bookH H))-(∑u∈middle n,coeff u.1 (bookH H)*coeff u.2 (bookU H)) = coeff n (bookU H) := by
  have h := pair n hn _ _ (book_fresh H) (book_guard H)
  rw [book_equal,coeff_one,if_neg hn.ne'] at h
  linarith

theorem inverse (p : ℕ) (H : ι→PowerSeries ℝ) (C : PowerSeries ℝ)
    (honest : ∀t,Fresh (H t)) (hC : Fresh C)
    (income : ∀j ≤ p,Tendsto (fun t=>coeff j (H t)) l (𝓝 (coeff j C))) :
    ∀ e ≤ p,Tendsto (fun t=>coeff e (bookU (H t))) l (𝓝 (coeff e (bookU C))) := by
  have first := forward p H C honest hC income
  intro e
  induction e using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hz : n=0
    · subst n
      simp only [show ∀T : PowerSeries ℝ,coeff 0 (bookU T)=1 from book_guard]
      exact tendsto_const_nhds
    have hn0 := Nat.pos_of_ne_zero hz
    have cross : Tendsto (fun t=>∑u∈middle n,coeff u.1 (bookH (H t))*coeff u.2 (bookU (H t))) l
        (𝓝 (∑u∈middle n,coeff u.1 (bookH C)*coeff u.2 (bookU C))) := by
      apply tendsto_finsetSum
      intro u hu
      exact (first _ ((low hu).1.le.trans hn)).mul (ih _ (low hu).2 ((low hu).2.le.trans hn))
    simpa only [complement n hn0] using (first n hn).neg.sub cross

end YM.Integration.WilsonKineticRebookingContinuity
end
