import YM.RG12.Frames.Settle

/-! # Transport costs in plain physical norms

Track a comparison to reference at any finite grade. The exponents are coarse, NOT anomalous
dimension identifications, but they give cost with the polynomial-log growth requested in the
ticket, once supplied by moving probes. -/
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
  [FiniteDimensional ℂ (Col V)]

include h
omit [FiniteDimensional ℂ (Col V)] in
lemma Moves.release (L : F →ₗ[ℂ] ℂ) {w : Grade d}
    (hl : ∀ x ∈ prev V w, L (P x) = 0) : ∀ n : ℕ, n₀ ≤ n → ∀ x : Col V,
    L (Y n x) = L (Y n (trimBelow w x)) := by
  intro n hn x
  rw [← sub_eq_zero, ← map_sub,← map_sub]
  let v:= x-trimBelow w x
  have he : v∈ prev V w:=by intro i hi; simp [v,trimBelow,hi]
  exact (P.apply_symm_apply (Y n v) ▸ hl (P.symm (Y n v)) ((h.always _ hn).prev w v he))

/-- Operator norm on the finite coordinates of the starting frame of a march. -/
def startNorm (Y : ℕ → Col V ≃ₗ[ℂ] F) (L : F →ₗ[ℂ] ℂ) (n₀ : ℕ) :=
    ‖LinearMap.toContinuousLinearMap (L.comp (Y n₀).toLinearMap)‖

/-- Single exponent for both directions. Uses just the step exponents and the finite
field-demand occupation. -/
def transportPower (d p b : ℕ) := (p+(d+1))+d*(b+1)

lemma row_ticket (L : F →ₗ[ℂ] ℂ) {w : Grade d}
    (hl : ∀ x ∈ prev V w, L (P x) = 0) (i : ℕ) (he : n₀ ≤ i) (x : Col V) :
    ‖L (Y i x)‖ ≤ ((d+1:ℕ):ℝ) * K^2 * startNorm Y L n₀ * (t i/t n₀)^w.val * (s i)^transportPower d p b * ‖x‖ := by
  let N := startNorm Y L n₀; have hN : 0 ≤ N := norm_nonneg _
  have hb := (h.forward_step n₀ le_rfl).basic_o
  have hK := hb.legal; have hT := h.spacing i he; have hT' := h.spacing n₀ le_rfl
  obtain ⟨hk,-⟩:= h.clock i he; obtain ⟨hk',-⟩:= h.clock n₀ le_rfl; have hK₀:=zero_le_one.trans hK
  have hx (x) : ‖L (Y n₀ x)‖ ≤ N*K*coins b (g n₀) (s n₀) (trimBelow w x):=by
    let M := LinearMap.toContinuousLinearMap (L.comp (Y n₀).toLinearMap)
    rw [h.release L hl n₀ le_rfl]
    change ‖M (trimBelow w x)‖ ≤ _; rw [mul_assoc]; exact (M.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_le_coins hb hk' _) hN)
  have hg:= row_from_start h L (h.release L hl) (mul_nonneg hN hK₀) hx i he x
  have hF:0≤ N*K*(t i/t n₀)^w.val := mul_nonneg (mul_nonneg hN hK₀) (pow_pos (div_pos hT.1 hT'.1) _).le
  have h₁:0 ≤ s i/s n₀:= div_nonneg (by positivity) (by positivity)
  have hb':= (h.forward_step i he).basic_o
  calc
    _ ≤ _ := hg
    _ ≤ N*K*(t i/t n₀)^w.val * (s i)^(p+(d+1)) *
          (((d+1:ℕ):ℝ)*K*(s i)^(d*(b+1))*‖x‖) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h₁ (div_le_self (zero_le_one.trans hk) hk') _) hF)
        ((coins_trim hb' (zero_le_one.trans hk) w x).trans (coins_le hb' hk x))
        (coins_nonneg hb' (zero_le_one.trans hk) _) (mul_nonneg hF (by positivity))
    _ = _ := by rw [transportPower,pow_add]; unfold N; ring

lemma col_ticket (w : Grade d) (x : F) (hx : P.symm x ∈ flag V w) (i : ℕ) (he : n₀ ≤ i) :
    ‖(Y i).symm x‖ ≤ K * coins b (g n₀) (s n₀) ((Y n₀).symm x) * (t n₀/t i)^w.val * (s i)^transportPower d p b := by
  have ht:=h.spacing i he; have ht':=h.spacing n₀ le_rfl; obtain ⟨hk,-⟩:=h.clock i he; obtain ⟨hk',-⟩:=h.clock n₀ le_rfl
  have hb:= (h.forward_step i he).basic_o; have hK:= zero_le_one.trans hb.legal
  refine (norm_le_coins (b:=b) hb hk _).trans ?_
  let r:= transportPower d p b; have ho:0≤ s i/s n₀:=by positivity
  have hr : d*(b+1)+(p+(d+1)) = r := Nat.add_comm ..
  have ha := col_from_start h w x hx _ he
  rw [hr] at ha
  let z:= coins b (g n₀) (s n₀) ((Y n₀).symm x)
  have hz:0≤z:= coins_nonneg (h.forward_step n₀ le_rfl).basic_o (by positivity) _
  apply (mul_le_mul_of_nonneg_left ha hK).trans
  change K*(_*z) ≤ _
  have hf := (pow_pos (div_pos ht'.1 ht.1) w.val).le
  calc
    _ ≤ K*(((t n₀/t i)^w.val*(s i)^r)*z):= mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ho (div_le_self (zero_le_one.trans hk) hk') _) hf) hz) hK
    _ = _ := by dsimp [r,z]; ring
end YM.RG12.Frames
