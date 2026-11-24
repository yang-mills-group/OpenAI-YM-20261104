import YM.Integration.WilsonIndependentGroupedInversionMesh

/-! Suppression of the restored finite-board charge on the actual prescribed
inversion mesh, uniformly in the measured coefficients inside their paid dose. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMeasuredPeriod
open XSpace

theorem length (V:Run) (i m:ℕ) (room : 8*m ≤ i):
    (((V.den i:ℝ)^m)^8) ≤ ((V.step i).p.side.val:ℝ) := by
  have base : 0<V.ratio := by have h:=V.large; omega
  have mag : i*(m*8) ≤ i*i := Nat.mul_le_mul_left i (by omega)
  have add : i*i ≤ i+V.reserve*i*i := by
    have h:=Nat.mul_le_mul_right (i*i) V.spare
    simpa only [one_mul, Nat.mul_assoc] using h.trans (Nat.le_add_left _ i)
  have paid : (V.den i ^ m)^8 ≤ V.side i := by
    unfold Run.den Run.side
    simp only [← pow_mul]
    rw [Nat.mul_assoc]
    exact (Nat.pow_le_pow_right base (mag.trans add)).trans
      (Nat.le_mul_of_pos_left _ V.finalSide.side.pos)
  exact_mod_cast paid

theorem width (V:Run)(i m:ℕ)(room : 8 * m ≤ i):
    (V.den i:ℝ)^m ≤ ((V.step i).p.side.val:ℝ)^(1/8:ℝ) := by
  have hh:=Real.rpow_le_rpow (by positivity : 0≤(((V.den i:ℝ)^m)^8))
    (length V i m room) (by norm_num : 0≤(1/8:ℝ))
  rw [← Real.rpow_natCast ((V.den i:ℝ)^m) 8,
    ← Real.rpow_mul (by positivity : 0≤(V.den i:ℝ)^m)] at hh
  norm_num at hh
  exact hh

theorem meter (k:ℕ)(μ:ℝ)(hμ:1≤μ):
    (1+Real.log μ)^k ≤ (1+8*((k:ℝ)+1))^k * μ^(1/8:ℝ) := by
  let u : ℝ := (8*((k:ℝ)+1))⁻¹
  have hu : 0<u := by dsimp [u]; positivity
  have pos : 0<μ := by linarith
  have hm : 1≤μ^u := Real.one_le_rpow hμ hu.le
  have hh := Real.add_one_le_exp (u*Real.log μ)
  rw [mul_comm u, ← Real.rpow_def_of_pos pos] at hh
  have h1 : u*(1+Real.log μ) ≤ u*(1+u⁻¹)*μ^u := by
    rw [show u*(1+u⁻¹) = u+1 by rw [mul_add,mul_one,mul_inv_cancel₀ hu.ne']]
    nlinarith [mul_le_mul_of_nonneg_left hm hu.le]
  have h2 : 1+Real.log μ ≤ (1+u⁻¹)*μ^u := by
    by_contra! bad
    have contra:=mul_lt_mul_of_pos_left bad hu
    linarith only [h1, (by simpa only [mul_assoc] using contra : u * (1+u⁻¹) * μ^u < u*(1+Real.log μ))]
  have hk : u*(k:ℝ) ≤ 1/8 := by
    dsimp [u]; rw [inv_mul_eq_div]; apply (div_le_iff₀ (by positivity)).2; linarith
  have z:=pow_le_pow_left₀ (by linarith [Real.log_nonneg hμ]) h2 k
  rw [mul_pow, ← Real.rpow_mul_natCast (by positivity : 0≤μ)] at z
  have fin := z.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hμ hk)
    (by positivity : 0≤(1+u⁻¹)^k))
  simpa [u] using fin

theorem original (V:Run)(i D p k:ℕ)(room : 8 * (D+p) ≤ i)(v B A:ℝ)(hB:0≤B)(hA:0≤A)
    (paid:v≤B*(V.den i:ℝ)^D*(A*(1+Real.log ((V.step i).p.side.val:ℝ))^k*
      ((V.step i).p.side.val:ℝ)^(-(1/4:ℝ)))) :
    v ≤ (B*A*(1+8*((k:ℝ)+1))^k)*(V.step i).spacing^p := by
  let μ:ℝ:=(V.step i).p.side.val
  have hp:0<μ := by dsimp only [μ]; exact_mod_cast (V.step i).p.side.pos
  have hμ:1≤μ := by dsimp only [μ]; exact_mod_cast (V.step i).p.side.pos
  have hb:0<(V.den i:ℝ) := by exact_mod_cast V.den_pos i
  have w := width V i (D+p) room
  change (V.den i:ℝ)^(D+p) ≤ μ^(1/8:ℝ) at w
  have cost := mul_le_mul_of_nonneg_left (meter k μ hμ) (by positivity : 0≤ B*(V.den i:ℝ)^D*A)
  have c := mul_le_mul_of_nonneg_right cost (Real.rpow_nonneg hp.le (-(1/4:ℝ)))
  have a : μ^(1/8:ℝ)*μ^(-(1/4:ℝ))=(μ^(1/8:ℝ))⁻¹ := by
    rw [← Real.rpow_add hp, ← Real.rpow_neg hp.le]
    norm_num
  rw [pow_add] at w
  have scale : (V.den i:ℝ)^D/μ^(1/8:ℝ) ≤ ((V.den i:ℝ)⁻¹)^p := by
    rw [inv_pow,div_le_iff₀ (Real.rpow_pos_of_pos hp _),← div_eq_inv_mul,
      le_div_iff₀ (pow_pos hb _),mul_comm]
    simpa only [mul_comm] using w
  change v ≤ (B*A*(1+8*((k:ℝ)+1))^k)*((V.den i:ℝ)⁻¹)^p
  calc v ≤ B*(V.den i:ℝ)^D*A*(1+Real.log μ)^k*μ^(-(1/4:ℝ)) := by
        simpa only [mul_assoc] using paid
    _ ≤ _ := c
    _ = (B*A*(1+8*((k:ℝ)+1))^k)*((V.den i:ℝ)^D/μ^(1/8:ℝ)) := by
        rw [div_eq_mul_inv ((V.den i:ℝ)^D) (μ^(1/8:ℝ)),← a];ring
    _ ≤ _ := mul_le_mul_of_nonneg_left scale (by positivity)
end YM.Integration.WilsonIndependentMeasuredPeriod
