import YM.AllOrder.Iron.Gate

/-! A quadratic determinant-free test of a covariance on the sup-norm cube.
Every sign vector and its covariance image can be tested without looking at
how many lattice coordinates there are. A summable spatial kernel supplies
the entire cost of the latter vector. -/
set_option autoImplicit false
set_option maxHeartbeats 1450000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson.SignCovariance
open Function Finset Matrix Lattice AllOrder.Iron Push.Uniform
open scoped Classical BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]
private abbrev Signs (ι : Type) := ι → Bool
private def sign (s : Signs ι) (i : ι) : ℝ := if s i then 1 else -1
private def flip (i : ι) (s : Signs ι) : Signs ι := fun j=>if j=i then !(s j) else s j
private def flips (i : ι) : Signs ι ≃ Signs ι where
  toFun := flip i
  invFun := flip i
  left_inv s := by funext j;by_cases h:j=i <;> simp [flip,h]
  right_inv s := by funext j;by_cases h:j=i <;> simp [flip,h]

omit [Fintype ι] in
private lemma sign_flip (i j : ι) (s : Signs ι) :
    sign (flips i s) j = if j=i then -sign s j else sign s j := by
  by_cases e:j=i
  · subst j
    cases h:s i <;> simp [sign,flips,flip,h]
  · simp [sign,flips,flip,e]

omit [Fintype ι] [DecidableEq ι] in
private lemma sign_abs (s : Signs ι) (i : ι) : |sign s i|=1 := by
  cases h:s i <;> simp [sign,h]

private lemma diagonal (i j : ι) :
    (∑ s:Signs ι,sign s i*sign s j)= if i=j then (Fintype.card (Signs ι):ℝ) else 0 := by
  by_cases e:i=j
  · subst j;rw [if_pos rfl];simp_rw [show ∀s:Signs ι,sign s i*sign s i=1 from fun s=>by cases h:s i <;> simp [sign,h]];simp
  · rw [if_neg e]
    let h:=fun s:Signs ι=>sign s i*sign s j
    have a:=Equiv.sum_comp (flips i) h
    have reverse (s:Signs ι) : h (flips i s) = -h s := by simp [h,sign_flip,Ne.symm e]
    simp_rw [reverse] at a
    rw [Finset.sum_neg_distrib] at a
    change (∑ s,h s)=0
    linarith

private abbrev count (ι : Type) [Fintype ι] [DecidableEq ι] : ℝ := Fintype.card (Signs ι)

private lemma centered_draw (K : Matrix ι ι ℝ) (i j : ι) :
    (∑ s:Signs ι,sign s i*(K *ᵥ sign s) j)=count ι * K j i := by
  change (∑ s,sign s i * ∑ k, K j k*sign s k)=_
  simp_rw [Finset.mul_sum,show ∀ (s:Signs ι) k,sign s i*(K j k*sign s k)=K j k*(sign s i*sign s k) from fun _ _=>by ring]
  rw [Finset.sum_comm]
  simp_rw [←Finset.mul_sum,diagonal]
  simp [count,mul_comm]

omit [DecidableEq ι] in
/-- The weighted sum of one absolute row of the actual exponentially decaying
covariance costs only its site multiplicity and the declared decay rate. -/
theorem capped_row {n:Side} {a:ι→Site n} {η C:ℝ} (K:Matrix ι ι ℝ)
    (hc:0≤C) (hη:0<η) (cap:Capped n a a η C K) {k:ℕ} (mult:Multiplicity a k) (i:ι) :
    ∑ j,|K i j| ≤ C * metric η k := by
  calc _ ≤ ∑ j,C * Decay η (a i) (a j) := sum_le_sum fun j _=>cap i j
       _ ≤ _ := by rw [←Finset.mul_sum];exact mul_le_mul_of_nonneg_left (mult.count a hη (a i)) hc

/-- Bilinear test of all the contributing entries. This avoids the full torus
maximum of a Gaussian vector, even for coefficients supported everywhere. -/
def bilinear (W : Matrix ι ι ℝ) (u v : ι→ℝ) := ∑ i,∑ j,W i j*u i*v j

theorem contraction (W K : Matrix ι ι ℝ) {C D:ℝ} (hC:0≤C)
    (rows : ∀ i,∑ j,|K i j| ≤ C)
    (budget : ∀ u v:ι→ℝ, ‖u‖≤1 → ‖v‖≤C → |bilinear W u v|≤D) :
    |∑ i,∑ j,W i j*K j i| ≤ D := by
  have exactSum : (∑ s:Signs ι,bilinear W (sign s) (K *ᵥ sign s)) = count ι * ∑ i,∑ j,W i j*K j i := by
    unfold bilinear
    rw [Finset.sum_comm]
    simp_rw [show ∀ i, (∑ s:Signs ι,∑ j,W i j*sign s i*(K *ᵥ sign s) j) =
        ∑ j,∑ s:Signs ι,W i j*sign s i*(K *ᵥ sign s) j from fun i=>Finset.sum_comm]
    simp_rw [mul_assoc,←Finset.mul_sum,centered_draw,show ∀ i j,W i j*(count ι*K j i)=count ι*(W i j*K j i) from fun _ _=>by ring]
    simp_rw [←Finset.mul_sum]
  have pos : 0 < count ι := by exact_mod_cast Fintype.card_pos (α:=Signs ι)
  have test (s:Signs ι) : |bilinear W (sign s) (K *ᵥ sign s)| ≤ D := by
    apply budget
    · exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i=>by rw [Real.norm_eq_abs,sign_abs]
    · apply (pi_norm_le_iff_of_nonneg hC).2
      intro i
      change |∑ j, K i j*sign s j|≤ C
      refine (Finset.abs_sum_le_sum_abs ..).trans ?_
      simpa only [abs_mul,sign_abs,mul_one] using rows i
  have sumBound: |∑ s:Signs ι,bilinear W (sign s) (K *ᵥ sign s)| ≤ count ι * D := by
    refine (Finset.abs_sum_le_sum_abs ..).trans ((sum_le_sum fun s _=>test s).trans_eq ?_)
    simp [count]
  rw [exactSum,abs_mul,abs_of_pos pos] at sumBound
  exact le_of_mul_le_mul_left sumBound pos

end YM.Integration.FVA1Physical.Wilson.SignCovariance
