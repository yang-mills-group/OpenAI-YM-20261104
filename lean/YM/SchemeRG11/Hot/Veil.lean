import YM.SchemeRG11.Hot.Forge

/-! Integrable envelopes for a single-time line. -/
set_option autoImplicit false
set_option maxHeartbeats 220000
noncomputable section
namespace YM.SchemeRG11.Hot
open Function Set MeasureTheory Filter Metric Asymptotics
open scoped Topology ContDiff BigOperators

lemma rain {c : ℝ} (h : 0<c) (n : ℕ) : ∃ C>0, ∀ R≥(0:ℝ), R^n * Real.exp (-c*R) ≤ C := by
  let f := fun R:ℝ=> R^n*Real.exp (-c*R)
  have he : Tendsto f atTop (𝓝 0) := by
    simpa only [f,Real.rpow_natCast] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero n _ h
  obtain ⟨B,hB⟩:= eventually_atTop.mp (he.eventually (gt_mem_nhds (a:=(1:ℝ)) zero_lt_one))
  obtain ⟨C,hC⟩:= (isCompact_Icc (a:=0) (b:=B)).exists_bound_of_continuousOn (f:=f) (by unfold f; fun_prop)
  refine ⟨|C|+1,by positivity,fun R hR=>?_⟩
  rcases le_total B R with u|u
  · have H : f R < 1 := hB R u
    exact le_trans H.le (by linarith [abs_nonneg C])
  exact (le_trans ((le_abs_self _).trans (hC R (mem_Icc.mpr ⟨hR,u⟩))) (by linarith [le_abs_self C]))

lemma enough {U : Set ℂ} (hu : IsCompact U) : ∃ n : ℕ, ∀ z∈U, -(n:ℝ) ≤ z.re-2 ∧ z.re-2 ≤ (n:ℝ) := by
  obtain ⟨C,hC⟩ := hu.exists_bound_of_continuousOn (f:= fun z:ℂ=>z.re-2) (by fun_prop)
  obtain ⟨n,hn⟩:= exists_nat_ge C
  exact ⟨n,fun z hz=> abs_le.mp ((hC z hz).trans hn)⟩
lemma strength {I X : Type} [Fintype I] [NormedAddCommGroup X] [NormedSpace ℝ X] (φ : I→X→ℝ) (P : Tint I X) {t : ℝ} (ht : 0<t) (r : I→ℝ) (e : ℂ) (x : X) :
    ‖tongs φ P t r e x‖ = t^(e.re-2)*Real.exp (-(∑ i,r i*φ i x))*‖Tint.read e r x P‖ := by
  simp only [tongs,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos ht,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le,Complex.sub_re,Complex.re_ofNat]

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {φ : Unit→X→ℝ} (P : Tint Unit X) {c : ℝ} (h : 0<c) {U : Set ℂ} (hu : IsCompact U) {K : Set X} (hk : IsCompact K) (hc : ∀ x∈K,c≤φ () x)
local notation "tap" => tongs φ P

include h hu hk hc in
lemma respite (B : ℝ) : ∃ C>0, ∀ z∈U, ∀ x∈K, ∀ t∈Ioc 0 B,
    ‖tap t (fun _=>t⁻¹) z x‖ ≤ C := by
  obtain ⟨n,hn⟩:=enough hu
  obtain ⟨C,hC,k,hK⟩:= Tint.top P hu hk
  obtain ⟨D,hD,hQ⟩:=rain h (n+k)
  refine ⟨C*(D+(1+|B|)^n),by positivity,fun z hz x hx t ht=>?_⟩
  have hp : 0<t:=ht.1
  rw [strength _ _ hp,Fintype.sum_unique, show (default:Unit)=() from rfl]
  have hv:= hc x hx
  have hw : 0 ≤ φ () x := h.le.trans hv
  rcases le_total t 1 with u|u
  · have hT := Real.rpow_le_rpow_of_exponent_ge hp u (hn z hz).1
    have ha : 1 ≤ t⁻¹:= one_le_inv₀ hp |>.mpr u
    grw [hK z hz x hx t⁻¹ ha _ (fun i=> le_of_eq (Real.norm_of_nonneg (by positivity : 0≤t⁻¹))), hT, show -(t⁻¹*φ () x) ≤ -c*t⁻¹ from by nlinarith [inv_pos.mpr hp]]
    rw [Real.rpow_neg_natCast,zpow_neg,zpow_natCast, ← inv_pow]
    calc _ = C*((t⁻¹)^(n+k)*Real.exp (-c*t⁻¹)) := by rw [pow_add]; ring
         _ ≤ _ := by gcongr; exact (hQ _ (by positivity)).trans (le_add_of_nonneg_right (by positivity))
  have ha : ‖t⁻¹‖ ≤ 1 := by rw [Real.norm_of_nonneg (by positivity : 0 ≤ t⁻¹)]; exact (inv_le_one₀ hp).mpr u
  have hT : t^(z.re-2) ≤ (1+|B|)^n := by
    have hu' : t ≤ 1+|B| := ht.2.trans (by linarith [le_abs_self B])
    exact (Real.rpow_le_rpow_of_exponent_le u (hn z hz).2).trans (by rw [Real.rpow_natCast]; gcongr)
  grw [hK z hz x hx 1 le_rfl _ (fun _=>ha),Real.exp_le_one_iff.mpr (by apply neg_nonpos.mpr; positivity : -(t⁻¹*φ () x) ≤ 0),hT]
  rw [one_pow,mul_one,mul_one,mul_comm]; gcongr; linarith

include h hk hc in
lemma mist : ∃ C>0, ∀ x∈K, ∀ t : ℝ, 0<t →
    ‖tap t (fun _=>t⁻¹) 0 x‖ ≤ C*(1+t)⁻¹^2 := by
  obtain ⟨C,hC,hS⟩:=respite P h (isCompact_singleton (x:=(0:ℂ))) hk hc 1
  obtain ⟨D,hD,l,hM⟩:=Tint.top P (isCompact_singleton (x:=(0:ℂ))) hk
  refine ⟨(max C D)*4,by positivity,fun x hx t ht=>?_⟩
  rcases le_total t 1 with u|u
  · refine (hS _ rfl x hx t ⟨ht,u⟩).trans ((le_max_left C D).trans ?_)
    rw [mul_assoc]
    refine le_mul_of_one_le_right (by positivity) ?_
    field_simp; nlinarith
  rw [strength _ _ ht, Fintype.sum_unique, show (default:Unit)=() from rfl, Complex.zero_re,zero_sub,Real.rpow_neg ht.le,Real.rpow_two]
  have ha : ‖t⁻¹‖ ≤ 1 := by rw [Real.norm_of_nonneg (by positivity : 0 ≤ t⁻¹)]; exact (inv_le_one₀ ht).mpr u
  have hw : 0 ≤ φ () x := h.le.trans (hc x hx)
  grw [hM _ rfl x hx 1 le_rfl _ (fun _=>ha),Real.exp_le_one_iff.mpr (by apply neg_nonpos.mpr; positivity : -(t⁻¹*φ () x) ≤ 0)]
  rw [one_pow,mul_one,mul_one, mul_assoc,mul_comm _ D]; gcongr; exact le_max_right ..; field_simp; nlinarith

end YM.SchemeRG11.Hot
