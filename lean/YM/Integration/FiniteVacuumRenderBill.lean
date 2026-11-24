import YM.IterationFour.Vacuum.Render

/-!
Finite intrinsic rendering bills, indexed by the original list occurrences.
The supplied credit and cost functions both take the original Piece as input.
The credit-only map may identify records; no cost on its image is selected.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.FiniteVacuumRenderBill

open Lattice IterationFour IterationFour.Currency IterationFour.Vacuum
open scoped BigOperators

/-- A finite fee constant, chosen before the list and all scalar data. -/
def unitConstant (r rankCap : ℕ) : ℝ :=
  ∑ p ∈ Finset.range (r + 1), ∑ d ∈ Finset.range (rankCap + 1),
    gainFee (((p : ℤ) - d : ℤ) : ℝ)

/-- The corresponding finite shift-fee constant. -/
def shiftConstant (r rankCap : ℕ) : ℝ :=
  ∑ p ∈ Finset.range (r + 1), ∑ d ∈ Finset.range (rankCap + 1),
    tiltFee (((p : ℤ) - d : ℤ) : ℝ)

private lemma unitConstant_nonneg (r rankCap : ℕ) :
    0 ≤ unitConstant r rankCap :=
  Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => (gainFee_pos _).le

private lemma shiftConstant_nonneg (r rankCap : ℕ) :
    0 ≤ shiftConstant r rankCap :=
  Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => tiltFee_nonneg _

private lemma fee_le_sum (F : ℝ → ℝ) (hF : ∀ x, 0 ≤ F x)
    {p d r rankCap : ℕ} (hp : p ≤ r) (hd : d ≤ rankCap) :
    F (((p : ℤ) - d : ℤ) : ℝ) ≤
      ∑ i ∈ Finset.range (r + 1), ∑ j ∈ Finset.range (rankCap + 1),
        F (((i : ℤ) - j : ℤ) : ℝ) := by
  calc
    F (((p : ℤ) - d : ℤ) : ℝ) ≤
        ∑ j ∈ Finset.range (rankCap + 1),
          F (((p : ℤ) - j : ℤ) : ℝ) :=
      Finset.single_le_sum
        (s := Finset.range (rankCap + 1))
        (f := fun j : ℕ => F (((p : ℤ) - j : ℤ) : ℝ))
        (fun _ _ => hF _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hd))
    _ ≤ ∑ i ∈ Finset.range (r + 1), ∑ j ∈ Finset.range (rankCap + 1),
          F (((i : ℤ) - j : ℤ) : ℝ) :=
      Finset.single_le_sum
        (s := Finset.range (r + 1))
        (f := fun i : ℕ => ∑ j ∈ Finset.range (rankCap + 1),
          F (((i : ℤ) - j : ℤ) : ℝ))
        (fun _ _ => Finset.sum_nonneg fun _ _ => hF _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hp))

private lemma gain_range {b : ℝ} (hb : 1 ≤ b) :
    0 < gain b ∧ gain b ≤ 1 ∧ gain b ^ 2 = b⁻¹ := by
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb0
  refine ⟨?_, ?_, ?_⟩
  · exact inv_pos.mpr hs
  · change (Real.sqrt b)⁻¹ ≤ 1
    apply (inv_le_one₀ hs).mpr
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hb
  · change ((Real.sqrt b)⁻¹) ^ 2 = b⁻¹
    rw [inv_pow, Real.sq_sqrt hb0.le]

private lemma repriced_power {g threshold W : ℝ}
    (hg : 0 < g) (hg1 : g ≤ 1) (ht : 0 ≤ threshold)
    (hW : 1 ≤ W) (htW : threshold / g ≤ W)
    {p d rankCap : ℕ} (hp : 3 ≤ p) (hd : d ≤ rankCap) :
    g ^ ((p : ℤ) - d) * threshold ^ d ≤ W ^ rankCap * g ^ 3 := by
  have hratio : (threshold / g) ^ d ≤ W ^ rankCap :=
    (pow_le_pow_left₀ (div_nonneg ht hg.le) htW d).trans
      (pow_le_pow_right₀ hW hd)
  calc
    g ^ ((p : ℤ) - d) * threshold ^ d =
        (threshold / g) ^ d * g ^ p := by
      rw [zpow_natCast_sub_natCast₀ hg.ne', div_pow]
      ring
    _ ≤ W ^ rankCap * g ^ 3 :=
      mul_le_mul hratio (pow_le_pow_of_le_one hg.le hg1 hp)
        (pow_nonneg hg.le p) (pow_nonneg (zero_le_one.trans hW) rankCap)

private lemma sum_cost_bound {α : Type*} (S : List α)
    (f t : α → ℝ) (D : ℝ) (h : ∀ a ∈ S, f a ≤ D * t a) :
    (S.map f).sum ≤ D * (S.map t).sum := by
  revert h
  induction S with
  | nil =>
      intro _
      simp only [List.map_nil, List.sum_nil, mul_zero, le_refl]
  | cons a S ih =>
      intro h
      have htail : ∀ v ∈ S, f v ≤ D * t v :=
        fun v hv => h v (List.mem_cons_of_mem a hv)
      simpa only [List.map_cons, List.sum_cons, mul_add] using
        add_le_add (h a List.mem_cons_self) (ih htail)

private lemma credit_sum_bound {G : Gauge} {n : Side}
    (S : List (Piece G n)) (k c t : Piece G n → ℝ)
    (threshold C B P : ℝ) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hk : ∀ a ∈ S, 0 ≤ k a)
    (hc : ∀ a ∈ S, c a ≤ C * threshold ^ a.rank * t a)
    (ht : ∀ a ∈ S, 0 ≤ t a)
    (hprice : ∀ a ∈ S, k a * threshold ^ a.rank ≤ P)
    (hsum : (S.map t).sum ≤ B) :
    (S.map fun a => k a * c a).sum ≤ C * B * P := by
  have hterm : ∀ a ∈ S, k a * c a ≤ (C * P) * t a := by
    intro a ha
    calc
      k a * c a ≤ k a * (C * threshold ^ a.rank * t a) :=
        mul_le_mul_of_nonneg_left (hc a ha) (hk a ha)
      _ = (C * t a) * (k a * threshold ^ a.rank) := by ring
      _ ≤ (C * t a) * P :=
        mul_le_mul_of_nonneg_left (hprice a ha) (mul_nonneg hC (ht a ha))
      _ = (C * P) * t a := by ring
  calc
    (S.map fun a => k a * c a).sum ≤ (C * P) * (S.map t).sum :=
      sum_cost_bound S _ t (C * P) hterm
    _ ≤ (C * P) * B :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg hC hP)
    _ = C * B * P := by ring

/-- The original occurrence sum for the unit bill. No image cost is needed. -/
theorem unit_sum_bound (r rankCap : ℕ) {G : Gauge} {n : Side}
    (S : List (Piece G n)) (c t : Piece G n → ℝ)
    (b threshold C B W : ℝ)
    (hb : 1 ≤ b) (hthreshold : 0 ≤ threshold) (hC : 0 ≤ C) (_hB : 0 ≤ B)
    (hW : 1 ≤ W) (htW : threshold / gain b ≤ W)
    (hp : Render.gradings S r) (hrank : ∀ a ∈ S, a.rank ≤ rankCap)
    (hc : ∀ a ∈ S, c a ≤ C * threshold ^ a.rank * t a)
    (ht : ∀ a ∈ S, 0 ≤ t a) (hsum : (S.map t).sum ≤ B) :
    (S.map fun a =>
      gainFee (Render.stepOrder a : ℝ) * gain b ^ Render.stepOrder a * c a).sum ≤
        unitConstant r rankCap * C * B * W ^ rankCap * gain b ^ 3 := by
  obtain ⟨hg, hg1, _⟩ := gain_range hb
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have hK := unitConstant_nonneg r rankCap
  have hprice : ∀ a ∈ S,
      (gainFee (Render.stepOrder a : ℝ) * gain b ^ Render.stepOrder a) *
        threshold ^ a.rank ≤ unitConstant r rankCap * W ^ rankCap * gain b ^ 3 := by
    intro a ha
    have hfee : gainFee (Render.stepOrder a : ℝ) ≤ unitConstant r rankCap := by
      simpa only [Render.stepOrder, unitConstant] using
        fee_le_sum gainFee (fun x => (gainFee_pos x).le) (hp a ha).2 (hrank a ha)
    have hpow : gain b ^ Render.stepOrder a * threshold ^ a.rank ≤
        W ^ rankCap * gain b ^ 3 := by
      exact repriced_power hg hg1 hthreshold hW htW (hp a ha).1 (hrank a ha)
    calc
      (gainFee (Render.stepOrder a : ℝ) * gain b ^ Render.stepOrder a) *
          threshold ^ a.rank =
          gainFee (Render.stepOrder a : ℝ) *
            (gain b ^ Render.stepOrder a * threshold ^ a.rank) := by ring
      _ ≤ unitConstant r rankCap * (W ^ rankCap * gain b ^ 3) :=
        mul_le_mul hfee hpow
          (mul_nonneg (zpow_nonneg hg.le _) (pow_nonneg hthreshold _)) hK
      _ = unitConstant r rankCap * W ^ rankCap * gain b ^ 3 := by ring
  have hP : 0 ≤ unitConstant r rankCap * W ^ rankCap * gain b ^ 3 :=
    mul_nonneg (mul_nonneg hK (pow_nonneg hW0 _)) (pow_nonneg hg.le _)
  have h := credit_sum_bound S
    (fun a => gainFee (Render.stepOrder a : ℝ) * gain b ^ Render.stepOrder a)
    c t threshold C B _ hC hP
    (fun a _ => mul_nonneg (gainFee_pos _).le (zpow_nonneg hg.le _))
    hc ht hprice hsum
  calc
    (S.map fun a =>
      gainFee (Render.stepOrder a : ℝ) * gain b ^ Render.stepOrder a * c a).sum ≤
        C * B * (unitConstant r rankCap * W ^ rankCap * gain b ^ 3) := h
    _ = unitConstant r rankCap * C * B * W ^ rankCap * gain b ^ 3 := by ring

/-- The original occurrence sum for the shift bill, with two extra gain powers. -/
theorem shift_sum_bound (r rankCap : ℕ) {G : Gauge} {n : Side}
    (S : List (Piece G n)) (c t : Piece G n → ℝ)
    (b threshold C B W : ℝ)
    (hb : 1 ≤ b) (hthreshold : 0 ≤ threshold) (hC : 0 ≤ C) (_hB : 0 ≤ B)
    (hW : 1 ≤ W) (htW : threshold / gain b ≤ W)
    (hp : Render.gradings S r) (hrank : ∀ a ∈ S, a.rank ≤ rankCap)
    (hc : ∀ a ∈ S, c a ≤ C * threshold ^ a.rank * t a)
    (ht : ∀ a ∈ S, 0 ≤ t a) (hsum : (S.map t).sum ≤ B) :
    (S.map fun a =>
      tiltFee (Render.stepOrder a : ℝ) * b⁻¹ * gain b ^ Render.stepOrder a * c a).sum ≤
        shiftConstant r rankCap * C * B * W ^ rankCap * gain b ^ 5 := by
  obtain ⟨hg, hg1, hgsq⟩ := gain_range hb
  have hb0 : 0 ≤ b := zero_le_one.trans hb
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have hK := shiftConstant_nonneg r rankCap
  have hprice : ∀ a ∈ S,
      (tiltFee (Render.stepOrder a : ℝ) * b⁻¹ * gain b ^ Render.stepOrder a) *
        threshold ^ a.rank ≤ shiftConstant r rankCap * W ^ rankCap * gain b ^ 5 := by
    intro a ha
    have hfee : tiltFee (Render.stepOrder a : ℝ) ≤ shiftConstant r rankCap := by
      simpa only [Render.stepOrder, shiftConstant] using
        fee_le_sum tiltFee tiltFee_nonneg (hp a ha).2 (hrank a ha)
    have hpow : gain b ^ Render.stepOrder a * threshold ^ a.rank ≤
        W ^ rankCap * gain b ^ 3 :=
      repriced_power hg hg1 hthreshold hW htW (hp a ha).1 (hrank a ha)
    have hpow5 : (b⁻¹ * gain b ^ Render.stepOrder a) * threshold ^ a.rank ≤
        W ^ rankCap * gain b ^ 5 := by
      calc
        (b⁻¹ * gain b ^ Render.stepOrder a) * threshold ^ a.rank =
            b⁻¹ * (gain b ^ Render.stepOrder a * threshold ^ a.rank) := by ring
        _ ≤ b⁻¹ * (W ^ rankCap * gain b ^ 3) :=
          mul_le_mul_of_nonneg_left hpow (inv_nonneg.mpr hb0)
        _ = W ^ rankCap * gain b ^ 5 := by rw [← hgsq]; ring
    calc
      (tiltFee (Render.stepOrder a : ℝ) * b⁻¹ * gain b ^ Render.stepOrder a) *
          threshold ^ a.rank =
          tiltFee (Render.stepOrder a : ℝ) *
            ((b⁻¹ * gain b ^ Render.stepOrder a) * threshold ^ a.rank) := by ring
      _ ≤ shiftConstant r rankCap * (W ^ rankCap * gain b ^ 5) :=
        mul_le_mul hfee hpow5
          (mul_nonneg (mul_nonneg (inv_nonneg.mpr hb0) (zpow_nonneg hg.le _))
            (pow_nonneg hthreshold _)) hK
      _ = shiftConstant r rankCap * W ^ rankCap * gain b ^ 5 := by ring
  have hP : 0 ≤ shiftConstant r rankCap * W ^ rankCap * gain b ^ 5 :=
    mul_nonneg (mul_nonneg hK (pow_nonneg hW0 _)) (pow_nonneg hg.le _)
  have h := credit_sum_bound S
    (fun a => tiltFee (Render.stepOrder a : ℝ) * b⁻¹ * gain b ^ Render.stepOrder a)
    c t threshold C B _ hC hP
    (fun a _ => mul_nonneg
      (mul_nonneg (tiltFee_nonneg _) (inv_nonneg.mpr hb0)) (zpow_nonneg hg.le _))
    hc ht hprice hsum
  calc
    (S.map fun a =>
      tiltFee (Render.stepOrder a : ℝ) * b⁻¹ * gain b ^ Render.stepOrder a * c a).sum ≤
        C * B * (shiftConstant r rankCap * W ^ rankCap * gain b ^ 5) := h
    _ = shiftConstant r rankCap * C * B * W ^ rankCap * gain b ^ 5 := by ring

private lemma dollars_repriced {G : Gauge} {n : Side}
    (S : List (Piece G n)) (c k : Piece G n → ℝ)
    (hk : ∀ a, k {a with credit := c a} = k a) :
    Render.dollars k (S.map fun a => {a with credit := c a}) =
      (S.map fun a => k a * c a).sum := by
  induction S with
  | nil => rfl
  | cons a S ih =>
      simpa only [List.map_cons, List.sum_cons, Render.dollars, hk] using
        congrArg (fun x => k a * c a + x) ih

/-- Exact credit-only repricing, without injectivity or a cost on the image. -/
theorem unitBill_reprice {G : Gauge} {n : Side}
    (S : List (Piece G n)) (c : Piece G n → ℝ) (b : ℝ) :
    Render.unitBill (S.map fun a => {a with credit := c a}) b =
      (S.map fun a =>
        gainFee (Render.stepOrder a : ℝ) * gain b ^ Render.stepOrder a * c a).sum :=
  dollars_repriced S c _ (fun _ => rfl)

/-- The same exact occurrence identity for the native shift bill. -/
theorem shiftBill_reprice {G : Gauge} {n : Side}
    (S : List (Piece G n)) (c : Piece G n → ℝ) (b : ℝ) :
    Render.shiftBill (S.map fun a => {a with credit := c a}) b =
      (S.map fun a =>
        tiltFee (Render.stepOrder a : ℝ) * b⁻¹ * gain b ^ Render.stepOrder a * c a).sum :=
  dollars_repriced S c _ (fun _ => rfl)

end YM.Integration.FiniteVacuumRenderBill
end
