import YM.Integration.WilsonOriginalPublicFigureWickCharge

/-! At the finite planting mesh, keep the engineering powers on the two
actual indices of each matrix entry, including zero-grade entries. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicPivotWeights
open Finset Matrix
open scoped Classical BigOperators
variable {I J K:Type*}

def Paid (δ:ℝ) (w:I→ℕ) (n:J→ℕ) (X:I→J→ℂ) (B:ℝ):Prop :=
  ∀i j, ‖X i j‖*δ^(n j)≤B*δ^(w i)

theorem larger {δ B C:ℝ} (pos:0≤δ) {w:I→ℕ} {n:J→ℕ} {X:I→J→ℂ}
    (p:Paid δ w n X B) (bud:B≤C) : Paid δ w n X C :=
  fun i j=>(p i j).trans (mul_le_mul_of_nonneg_right bud (pow_nonneg pos _))

theorem plus {δ B C:ℝ} (pos:0≤δ) {w:I→ℕ} {n:J→ℕ} {X Y:Matrix I J ℂ}
    (p:Paid δ w n X B) (q:Paid δ w n Y C):Paid δ w n (X+Y) (B+C):=by
  intro i j
  calc
    _ ≤ (‖X i j‖+‖Y i j‖)*δ^(n j):=mul_le_mul_of_nonneg_right (norm_add_le ..) (pow_nonneg pos _)
    _ ≤ _:=by rw [add_mul,add_mul];exact add_le_add (p i j) (q i j)

theorem opposite {δ B:ℝ} {w:I→ℕ} {n:J→ℕ} {X:Matrix I J ℂ}
    (p:Paid δ w n X B):Paid δ w n (-X) B:=by
  intro i j
  simpa only [Matrix.neg_apply,norm_neg] using p i j

theorem zeros {δ B:ℝ} (pos:0≤δ) (nonneg:0≤B) (w:I→ℕ) (n:J→ℕ):
    Paid δ w n (0:Matrix I J ℂ) B:=by
  intro i j;simpa using mul_nonneg nonneg (pow_nonneg pos (w i))

theorem identity [DecidableEq I] {δ:ℝ} (pos:0≤δ) (w:I→ℕ):
    Paid δ w w (1:Matrix I I ℂ) 1:=by
  intro i j
  by_cases e:i=j
  · subst j;simp
  · simp [e,pow_nonneg pos]

theorem times [Fintype J] {δ B C:ℝ} (pos:0≤δ) (nn:0≤C) {w:I→ℕ} {u:J→ℕ} {n:K→ℕ}
    {X:Matrix I J ℂ} {Y:Matrix J K ℂ} (p:Paid δ w u X B) (q:Paid δ u n Y C):
    Paid δ w n (X*Y) ((Fintype.card J:ℝ)*B*C):=by
  intro i k
  calc
    _ ≤ (∑j,‖X i j*Y j k‖)*δ^(n k):=mul_le_mul_of_nonneg_right (norm_sum_le ..) (pow_nonneg pos _)
    _ = ∑j,‖X i j‖*(‖Y j k‖*δ^(n k)):=by simp only [Finset.sum_mul,norm_mul,mul_assoc]
    _ ≤ ∑_j:J,C*(B*δ^(w i)):=by
      apply sum_le_sum;intro j _
      calc
        _ ≤ ‖X i j‖*(C*δ^(u j)):=mul_le_mul_of_nonneg_left (q j k) (norm_nonneg _)
        _ = C*(‖X i j‖*δ^(u j)):=by ring
        _ ≤ _:=mul_le_mul_of_nonneg_left (p i j) nn
    _ = _:=by simp [nsmul_eq_mul];ring

theorem terms {δ B:ℝ} (pos:0≤δ) {w:I→ℕ} {n:J→ℕ} {D:Type*} (S:Finset D)
    (X:D→Matrix I J ℂ) (p:∀a∈S,Paid δ w n (X a) B):
    Paid δ w n (∑a∈S,X a) ((S.card:ℝ)*B):=by
  intro i j
  simp only [Finset.sum_apply]
  calc
    _ ≤ (∑a∈S,‖X a i j‖)*δ^(n j):=mul_le_mul_of_nonneg_right (norm_sum_le ..) (pow_nonneg pos _)
    _ ≤ ∑_a∈S,B*δ^(w i):=by rw [Finset.sum_mul];exact sum_le_sum (fun a ha=>p a ha i j)
    _ = _:=by simp [nsmul_eq_mul,mul_assoc]

theorem masked {δ B:ℝ} (pos:0≤δ) (nn:0≤B) {w:I→ℕ} {n:J→ℕ} {X:Matrix I J ℂ}
    (p:Paid δ w n X B) (gate:I→J→Prop) [DecidableRel gate]:
    Paid δ w n (fun i j=>if gate i j then X i j else 0) B:=by
  intro i j
  by_cases h:gate i j
  · simpa only [h,if_true] using p i j
  · simpa only [h,if_false,norm_zero,zero_mul] using mul_nonneg nn (pow_nonneg pos (w i))

/-- A rectangular raw-to-active input or an actual inverse is applied at finite
regulator. No norm of the raw rectangle's inverse occurs. -/
theorem applied [Fintype J] {δ B:ℝ} (pos:0≤δ) {w:I→ℕ} {n:J→ℕ} {X:Matrix I J ℂ}
    (p:Paid δ w n X B) (v:J→ℂ) (i:I):
    ‖∑j,X i j*((δ:ℂ)^(n j)*v j)‖ ≤ (B*δ^(w i))*∑j,‖v j‖:=by
  calc
    _ ≤ ∑j,‖X i j*((δ:ℂ)^(n j)*v j)‖:=norm_sum_le ..
    _ = ∑j,(‖X i j‖*δ^(n j))*‖v j‖:=by
      simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg pos,mul_assoc]
    _ ≤ _:=by rw [Finset.mul_sum];exact sum_le_sum (fun j _=>mul_le_mul_of_nonneg_right (p i j) (norm_nonneg _))

/-- The re-announced transmission has an extra δ^h on its row. Applying
the inverse at this date preserves that power for all earlier residuals. -/
theorem residual [Fintype I] {δ E B:ℝ} (pos:0<δ) (nn:0≤B) (h:ℕ) (w:I→ℕ) (n:J→ℕ)
    (err:I→ℂ) (inv:Matrix I J ℂ) (paid:∀i,‖err i‖*δ^(w i)≤E*δ^h)
    (back:Paid δ w n inv B) (j:J):
    ‖∑i,err i*inv i j‖ ≤ (Fintype.card I:ℝ)*E*B*(δ^h/δ^(n j)):=by
  have p:=times (I:=Unit) pos.le nn (X:=fun _ i=>err i) (Y:=inv)
    (w:=fun _=>h) (u:=w) (n:=n) (fun _ i=>paid i) back () j
  rw [←mul_div_assoc]
  exact (le_div_iff₀ (pow_pos pos _)).mpr p

end YM.Integration.WilsonOriginalPublicPivotWeights
end
