import YM.RG12.Frames.Motions

/-! # Log budgets for moving frames on the fixed physical filtration -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Frames
open Function Finset Filter
open scoped Topology BigOperators
variable {d : ℕ} {V : Grade d → Type} [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℂ (V i)]
variable {F : Type} [AddCommGroup F] [Module ℂ F]
variable {s t u : ℕ → ℝ} {Y : ℕ → Col V ≃ₗ[ℂ] F} {P : Col V ≃ₗ[ℂ] F}
  {A : ℕ → Col V ≃ₗ[ℂ] Col V} {g : ℕ → Currency V} {K : ℝ} {p b n₀ : ℕ}
  (h : Moves s t u Y P A g K p b n₀)

lemma norm_le_coins {g : Currency V} (hg : Fits g K) (hs : 1 ≤ s n₀) (x : Col V) :
    ‖x‖ ≤ K * coins b g (s n₀) x := by
  have hp : 0 ≤ K := zero_le_one.trans hg.legal
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hp (coins_nonneg hg (zero_le_one.trans hs) _))).2
  intro i
  apply (hg.lower ..).trans; apply mul_le_mul_of_nonneg_left _ hp
  have hx j : 1 ≤ price b (d:=d) j (s n₀) := one_le_pow₀ hs
  exact (le_mul_of_one_le_left (hg.nonneg ..) (hx i)).trans
    (single_le_sum (f:=fun j => price b j (s n₀)*g j (x j)) (fun j _=> mul_nonneg (zero_le_one.trans (hx j)) (hg.nonneg ..)) (mem_univ i))

lemma coins_le {g : Currency V} (hg : Fits g K) (hs : 1 ≤ s n₀) (x : Col V) :
    coins b g (s n₀) x ≤ ((d+1:ℕ):ℝ) * K * (s n₀)^(d*(b+1)) * ‖x‖ := by
  have hp := zero_le_one.trans hg.legal
  calc
    _ ≤ ∑ _i : Grade d, K * (s n₀)^(d*(b+1))*‖x‖ := sum_le_sum fun i _=>
      (mul_le_mul (pow_le_pow_right₀ hs (Nat.mul_le_mul_right (b+1) i.is_le)) ((hg.upper ..).trans
        (mul_le_mul_of_nonneg_left (norm_le_pi_norm ..) hp)) (hg.nonneg ..) (pow_nonneg (zero_le_one.trans hs) _)).trans_eq (by ring)
    _ = _ := by simp [Grade,mul_assoc]

include h
set_option quotPrecheck false
local notation "Fwd" => p + (d+1)
local notation "Bwd" => d*(b+1)+(p+(d+1))

/-- One fee for every frame row from a starting point. -/
theorem row_from_start (L : F →ₗ[ℂ] ℂ) {w : Grade d}
    (hl : ∀ n : ℕ, n₀ ≤ n → ∀ x : Col V, L (Y n x) = L (Y n (trimBelow w x)))
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x : Col V, ‖L (Y n₀ x)‖ ≤ B * coins b (g n₀) (s n₀) (trimBelow w x)) :
    ∀ n : ℕ, n₀ ≤ n → ∀ x : Col V,
      ‖L (Y n x)‖ ≤ B*(t n/t n₀)^w.val*(s n/s n₀)^(p+(d+1)) *
        coins b (g n) (s n) (trimBelow w x) := by
  intro n hn
  induction hn with
  | refl=>
    rw [div_self (zero_lt_one.trans_le (h.clock n₀ le_rfl).1).ne', one_pow, mul_one,
      div_self (h.spacing n₀ le_rfl).1.ne',one_pow,mul_one]
    exact hf
  | @step n hn IH =>
    intro x
    obtain ⟨ht,hu,hu'⟩:= h.spacing n hn
    obtain ⟨h₀,h₁⟩:= h.clock n₀ le_rfl
    obtain ⟨ha,hc⟩:= h.clock n hn
    let y:= dilate (u n)⁻¹ (trimBelow w x); let r:= s (n+1)/s n
    have ht₀:0<t n₀:= (h.spacing n₀ le_rfl).1; have hf:= h.forward_step n hn
    have he:= h.unit_ratio n hn
    rw [hl (n+1) (Nat.le_trans hn (Nat.le_succ n)) x, h.realized n hn]; apply (IH (A n y)).trans
    have hsum : coins b (g n) (s n) (trimBelow w ((A n) y)) ≤
        r^Fwd * ((u n)⁻¹^w.val * coins b (g (n+1)) (s (n+1)) (trimBelow w x)) := by
      have hp := shrink_price (b:=b) hf.basic_i (zero_le_one.trans (h.clock (n+1) (Nat.le_trans hn (Nat.le_succ n))).1) hu w x
      have hr : 0 ≤ r^Fwd := zero_le_one.trans (one_le_pow₀ he)
      exact ((coins_trim hf.basic_o (zero_le_one.trans ha) _ _).trans
        (hf.pay_all ha (h.clock_ratio n hn) y)).trans
        (mul_le_mul_of_nonneg_left ((coin_mono hf.basic_i (zero_le_one.trans ha) (by linarith) y).trans hp) hr)
    have hz : B*(t n/t n₀)^w.val*(s n/s n₀)^Fwd ≥ 0 := by unfold GE.ge; positivity
    apply (mul_le_mul_of_nonneg_left hsum hz).trans_eq
    rw [hu']; dsimp only [r]; rw [inv_pow, div_pow,div_pow,div_pow,div_pow,div_pow,div_pow]; simp only [Nat.succ_eq_add_one]; field_simp

-- Precision on columns of Y^-1 on each grade (and hence also on full inverse at fixed d).
variable [FiniteDimensional ℂ (Col V)]

theorem col_from_start (w : Grade d) (x : F) (hx : P.symm x ∈ flag V w) :
    ∀ n : ℕ, n₀ ≤ n →
      coins b (g n) (s n) ((Y n).symm x) ≤ (t n₀/t n)^w.val*(s n/s n₀)^Bwd *
        coins b (g n₀) (s n₀) ((Y n₀).symm x) := by
  intro n hn
  induction hn with
  | refl=> simp only [div_self (h.spacing n₀ le_rfl).1.ne', div_self (zero_lt_one.trans_le (h.clock n₀ le_rfl).1).ne',one_pow,one_mul, le_refl]
  | @step n hn IH=>
    have hn' := Nat.le_trans hn (Nat.le_succ n)
    obtain ⟨hs,hh⟩:=h.clock n hn; obtain ⟨hk,-⟩:=h.clock n₀ le_rfl; obtain ⟨hf,hu,he⟩:= h.spacing n hn
    have hf₀:= (h.spacing n₀ le_rfl).1
    let r:=s (n+1)/s n; have hr : 1 ≤ r:= h.unit_ratio n hn
    let y := (A n).symm ((Y n).symm x); have ho:=h.return_step n hn
    have h₁ : y ∈ flag V w:=by
      apply (triangular_iff_stays _ _).1 ho.stays w
      rw [← P.apply_symm_apply x]; exact (triangular_iff_stays _ _).1 (h.always n hn).inv w _ hx
    rw [h.backward n hn]
    have h₂ : coins b (g (n+1)) (s (n+1)) (dilate (u n) y) ≤
        (u n)^w.val * (r^Bwd * coins b (g n) (s n) ((Y n).symm x)):=by
      have h':= ho.pay_all hs (h.clock_ratio n hn) ((Y n).symm x)
      change _≤ r^Fwd*_ at h'
      apply (grow_price ho.basic_o (zero_le_one.trans (h.clock _ hn').1) hu h₁).trans
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (zero_le_one.trans hu) _)
      have ht : s (n+1) = r*(s n):= (div_mul_cancel₀ _ (zero_lt_one.trans_le hs).ne').symm
      rw [pow_add,mul_assoc]
      exact (enlarge ho.basic_o hs hr ht y).trans (mul_le_mul_of_nonneg_left h' (pow_nonneg (zero_le_one.trans hr) _))
    apply h₂.trans
    have hm: ∀ (q:ℕ), 0≤r^q∧0≤(u n)^q:= fun _=> ⟨pow_nonneg (zero_le_one.trans hr) _,pow_nonneg (zero_le_one.trans hu) _⟩
    apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left IH (hm _).1) (hm _).2).trans_eq
    rw [he]; dsimp only [r]; simp only [div_pow]; field_simp
    try ring
end YM.RG12.Frames
