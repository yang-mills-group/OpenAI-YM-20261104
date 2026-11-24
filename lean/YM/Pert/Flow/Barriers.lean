import YM.Pert.Flow.Bend
/-! Polynomial and super-polynomial barriers for bounded-step matrix laws. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Pert.Flow.Price
open Function Filter Topology
open scoped Topology Classical

def duration (i : ℕ) : ℝ := (i:ℝ)+1
def tame (f : ℕ→ℝ) : Prop := ∃ (q : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ i, |f i| ≤ C*(duration i)^q
def flat (f : ℕ → ℝ) : Prop := ∀ q : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i, |f i| ≤ C/(duration i)^q
lemma duration_leads : Tendsto duration atTop atTop := tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
lemma duration_large (i) : 1 ≤ duration i := by simp [duration]

private lemma eventually_tamed {f : ℕ→ℝ} {q:ℕ} {R:ℝ} (h : ∀ᶠ n : ℕ in atTop, |f n| ≤ R*(duration n)^q) : tame f := by
   obtain ⟨n,hN⟩:=eventually_atTop.mp h
   let S:=∑i∈Finset.range n, |f i|
   let A:=|R|+S
   have hs : 0≤S := Finset.sum_nonneg (fun i _=> abs_nonneg _)
   refine ⟨q,A,by dsimp [A]; positivity, fun i=> ?_⟩
   have hi:=duration_large i
   have hW : 0 ≤ (duration i)^q:=by positivity
   by_cases hn : n ≤ i
   · exact (hN i hn).trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (le_add_of_nonneg_right hs)) hW)
   exact (Finset.single_le_sum (s:=Finset.range n) (f:=fun j=>|f j|) (fun j _=>abs_nonneg (f j)) (Finset.mem_range.mpr (Nat.lt_of_not_ge hn))).trans
      ((le_add_of_nonneg_left (abs_nonneg R)).trans (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hi)))

private lemma eventually_level {f : ℕ→ℝ} {q:ℕ} {R:ℝ} (h : ∀ᶠ n : ℕ in atTop, |f n| * (duration n)^q ≤ R) :
   ∃ C, 0 ≤ C ∧ ∀ n, |f n| ≤ C/(duration n)^q := by
   obtain ⟨n,hN⟩:=eventually_atTop.mp h
   let g i:= |f i| * (duration i)^q
   have hg i : 0 ≤ g i := mul_nonneg (abs_nonneg _) (pow_nonneg (zero_le_one.trans (duration_large _)) _)
   let S:=∑i∈Finset.range n, g i
   let A:= |R|+S
   have hs :0 ≤ S:=Finset.sum_nonneg (fun i _=> hg i)
   refine ⟨A, add_nonneg (abs_nonneg R) hs, fun i=> ?_⟩
   by_cases hn : n ≤ i
   · refine (le_div_iff₀ (pow_pos (lt_of_lt_of_le zero_lt_one (duration_large _)) _)).2 ?_
     exact (hN i hn).trans ((le_abs_self _).trans (le_add_of_nonneg_right hs))
   refine (le_div_iff₀ (pow_pos (lt_of_lt_of_le zero_lt_one (duration_large _)) _)).2 ?_
   exact (Finset.single_le_sum (s:=Finset.range n) (fun j _=>hg j) (Finset.mem_range.mpr (Nat.lt_of_not_ge hn))).trans (le_add_of_nonneg_left (abs_nonneg R))

theorem rate_barrier {f : ℕ→ℝ} (hf : ∀ i, 0 ≤ f i) {k : ℝ} (hk : 0 ≤ k)
    (H : ∀ᶠ i in atTop, f (i+1) ≤ (1+k/(duration i)) * f i) : tame f := by
   obtain ⟨N,h⟩:=eventually_atTop.mp H
   obtain ⟨q,hq⟩:=exists_nat_ge k
   let C:= f N
   suffices h' : ∀ i, N ≤ i → f i ≤ C*(duration i)^q by
       exact eventually_tamed ((eventually_ge_atTop N).mono fun i hi=> abs_of_nonneg (hf i) ▸ h' i hi)
   intro i hi
   induction i, hi using Nat.le_induction with
   | base => exact le_mul_of_one_le_right (hf N) (one_le_pow₀ (duration_large _))
   | succ i hi IH =>
      have hz := h i hi
      have hg := duration_large i
      have hg' : 0<duration i := lt_of_lt_of_le zero_lt_one hg
      have h₁ : 1+k/(duration i) ≤ 1+(q:ℝ)*(1/duration i) := by change 1+k/duration i ≤ 1+_; rw [mul_one_div]; gcongr
      have h₂ : _ ≤ (1+(1:ℝ)/(duration i))^q := one_add_mul_le_pow (le_trans (show (-2:ℝ) ≤ 0 by norm_num) (show 0 ≤ (1:ℝ)/duration i by positivity)) q
      have h₃ : (1+1/duration i)*duration i=duration (i+1) := by field_simp; simp [duration]
      calc
         _ ≤ (1+k/duration i)*_ := hz
         _ ≤ (1+1/(duration i))^q * (C*(duration i)^q) := mul_le_mul (h₁.trans h₂) IH (hf _) (by positivity)
         _ = C*(duration (_+1))^q := by rw [←h₃,mul_pow];ring

lemma consecutive_weight (q : ℕ) : Tendsto (fun i : ℕ=> (duration i / duration (i+1))^q) atTop (𝓝 1) := by
   have hv:= (tendsto_add_atTop_iff_nat 1).2 duration_leads
   have hh := (tendsto_const_nhds (x:=(1:ℝ))).sub (hv.const_div_atTop (1:ℝ))
   rw [sub_zero] at hh
   have hh := hh.congr (fun i:ℕ => show (1:ℝ)-1/duration (i+1)=duration i/duration (i+1) by
       have hx := duration_large (i+1); field_simp; simp [duration])
   simpa only [one_pow] using hh.pow q

/-- Recursing across dyadic increments with arbitrary-order control of the
forcing yields flat error on the decaying block. -/
theorem barrier_decay {f:ℕ→ℝ} {c : ℝ} (hc : 0 ≤ c) (hu : c < 1)
    (H : ∀ q:ℕ, ∃ C, 0 ≤ C ∧ ∀ᶠ i:ℕ in atTop, |f (i+1)| ≤ c*|f i| + C/(duration i)^q) : flat f := by
   intro q
   obtain ⟨C,hC,h⟩:=H q
   let τ:= (1-c)/2
   have hτ: 0<τ := half_pos (sub_pos.mpr hu)
   have hθ : c+τ<1 := by dsimp [τ]; linarith
   obtain ⟨N,hN⟩:=eventually_atTop.mp (h.and ((consecutive_weight q).eventually (lt_mem_nhds hθ)))
   let R:=max (|f N| * (duration N)^q) (C/τ)
   have hr : 0 ≤ R:= (div_nonneg hC hτ.le).trans (le_max_right ..)
   suffices hb : ∀ i, N ≤ i → |f i| * (duration i)^q ≤ R from
       eventually_level ((eventually_ge_atTop N).mono fun i hi=>hb i hi)
   intro i hi
   induction i,hi using Nat.le_induction with
   | base => exact le_max_left ..
   | succ i hi IH =>
       obtain ⟨h₁,h₂⟩:=hN _ hi
       have hh:= duration_large i;have hh' := duration_large (i+1)
       have h0 := lt_of_lt_of_le zero_lt_one hh
       apply le_of_mul_le_mul_right (a:=(duration i/duration (i+1))^q) _ (by positivity)
       have hI : c*R+C ≤ c*R+τ*R := add_le_add_right ((div_le_iff₀ hτ).mp (le_max_right ..) |>.trans_eq (mul_comm ..)) _
       calc
          (|f (i+1)| * (duration (i+1))^q)* _ = |f (i+1)| * (duration i)^q := by rw [div_pow];field_simp
          _ ≤ (c*|f i|+C/(duration i)^q)*(duration i)^q := mul_le_mul_of_nonneg_right h₁ (by positivity)
          _ = c*(|f i| * (duration i)^q)+C := by field_simp
          _ ≤ c*R+C := add_le_add_left (mul_le_mul_of_nonneg_left IH hc) _
          _ ≤ R*(c+τ) := hI.trans_eq (by ring)
          _ ≤ _ := mul_le_mul_of_nonneg_left h₂.le hr

end YM.Pert.Flow.Price
