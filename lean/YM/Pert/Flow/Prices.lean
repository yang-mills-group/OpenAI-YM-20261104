import YM.Pert.Flow.StepPrice
/-! Prices in powers of an asymptotically logarithmic-slope coupling. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.Pert.Flow
open Function Filter Topology
open Price Layer
open scoped Topology
variable {u : ℝ → ℝ} {B : ℝ}

def couplingTame (u f : ℕ→ℝ) : Prop := ∃ p:ℕ, ∃ D ≥ (0:ℝ),
      ∀ᶠ n in atTop, |u n|^p * |f n| ≤ D
def couplingFlat (u f : ℕ→ℝ) : Prop :=
   ∀ q:ℕ, ∃ D ≥ (0:ℝ), ∀ᶠ n in atTop, |f n| ≤ D*|u n|^q
lemma couplingTame_cost {u f:ℕ→ℝ} (h : couplingTame u f) (hp : ∀ᶠ n in atTop, u n ≠ 0) :
     ∃ p:ℕ, ∃ D ≥ (0:ℝ), ∀ᶠ n in atTop, |f n| ≤ D / |u n|^p := by
   obtain ⟨p,D,hD,h⟩:=h
   refine ⟨p,D,hD,?_⟩
   filter_upwards [hp,h] with n hn hi
   rw [le_div_iff₀ (by positivity)]
   linarith only [hi]

variable (h : Signature B u)
include h
lemma coupling_late : ∀ᶠ n : ℕ in atTop, 0 < u (Nat.cast n) :=
   tendsto_natCast_atTop_atTop (R:=ℝ)|>.eventually h.positive

variable {f : ℕ → ℝ}
theorem pricedUpon (hf : tame f) (hg : 0 < B) : couplingTame (fun n=>u (n:ℝ)) f := by
   obtain ⟨p,D,hD,hP⟩:=hf
   have hb : ∃ d,0<d ∧ ∀ᶠ n : ℕ in atTop, |u (n:ℝ)|^2*n ≤ d := by
       have he := (h.scale.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).pow 2
       let d:=((Real.sqrt (2*B))⁻¹)^2+1
       refine ⟨d,(by dsimp [d]; positivity),?_⟩
       filter_upwards [he.eventually (gt_mem_nhds (show _ < d by dsimp [d];linarith)),coupling_late h] with n hn hx
       have hn : (u (n:ℝ)*Real.sqrt (n:ℝ))^2 < d:=hn
       rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)] at hn; rw [abs_of_pos hx]
       exact hn.le
   obtain ⟨d,hd,hk⟩:=hb
   refine ⟨2*p,D*(2*d)^p,by positivity,?_⟩
   filter_upwards [hk,coupling_late h, eventually_ge_atTop (1:ℕ)] with n hn hx h'
   let u0:=u (n:ℝ)
   rw [abs_of_pos hx] at hn;change u0^2*(n:ℝ) ≤ d at hn
   have hr : u0^2*(duration n) ≤ 2*d := by unfold duration; nlinarith only [hn,(show (1:ℝ)≤n from by exact_mod_cast h')]
   rw [abs_of_pos hx,pow_mul]
   calc
       _ ≤ (u0^2)^p * (D*(duration n)^p) := mul_le_mul_of_nonneg_left (hP n) (by positivity)
       _ = D*(u0^2*duration n)^p:= by rw [mul_pow];ring
       _ ≤ _:= mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg (sq_nonneg _) (zero_le_one.trans (duration_large _))) hr _) hD

theorem flatUpon (hf : flat f) (hg : 0 < B) : couplingFlat (fun n=>u (n:ℝ)) f := by
   intro p
   obtain ⟨D,hD,hP⟩:=hf p
   have hb : ∃ d,0<d ∧ ∀ᶠ n : ℕ in atTop, 1 ≤ d*u (n:ℝ)^2*(n:ℝ) := by
       have he := (h.scale.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).pow 2
       let a:=((Real.sqrt (2*B))⁻¹)^2
       have ha : 0<a:= by dsimp [a]; positivity
       refine ⟨2/a, by positivity,?_⟩
       filter_upwards [he.eventually (lt_mem_nhds (half_lt_self ha))] with n hn
       have hn : a/2<(u (n:ℝ)*Real.sqrt (n:ℝ))^2:=hn
       rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)] at hn
       field_simp
       linarith only [hn]
   obtain ⟨d,hd,h'⟩:=hb
   refine ⟨D*d^p,by positivity,?_⟩
   filter_upwards [h',(h.concentration.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually (gt_mem_nhds (zero_lt_one : (0:ℝ) < 1)),coupling_late h] with n hn hx h'
   let u0:=u (n:ℝ)
   have hW:=duration_large n
   have hr : 1 ≤ d*u0^2*duration n := by dsimp only [duration,u0]; nlinarith only [hn,(sq_nonneg (u n)),hd]
   apply (hP n).trans
   rw [div_le_iff₀ (by positivity),abs_of_pos h',show _*duration n^p=D*(d*u0*duration n)^p by simp only [u0, mul_pow];ring]
   apply le_mul_of_one_le_right hD (one_le_pow₀ ?_)
   apply hr.trans
   have : u0<1:=hx
   gcongr
   change 0 < u0 at h'
   nlinarith only [this,h']

end YM.Pert.Flow
