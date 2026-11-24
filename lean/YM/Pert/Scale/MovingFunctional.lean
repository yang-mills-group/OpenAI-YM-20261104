import YM.Pert.FirstTarget
/-! Finite test nondegeneracy price to recover a column in moving coordinates. Does NOT apply a costly inverse of an *absolute* bare trajectory over UV history. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Scale
open Function Filter Topology Set Metric
variable {E A : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [ProperSpace E]

omit [ProperSpace E] in
lemma moving_linear {a : ℕ → E} {a0 : E} (ha : Tendsto a atTop (𝓝 a0))
   {f : ℕ → E →ₗ[ℂ] ℂ} {g : E →ₗ[ℂ] ℂ} (h : ∀ b, Tendsto (fun n => f n b) atTop (𝓝 (g b))) :
   Tendsto (fun n=> f n (a n)) atTop (𝓝 (g a0)) := by
  let B := Module.finBasis ℂ E
  let F := fun n:ℕ=> ∑ i, B.equivFun (a n) i • f n (B i)
  have he : F = (fun n:ℕ => f n (a n)) := funext fun n=>by
    change F n = f n (a n)
    conv_rhs=> rw [←B.sum_equivFun (a n),map_sum]; simp only [map_smul]
  have hx : (∑ i, B.equivFun a0 i • g (B i))=g a0 := by conv_rhs=> rw [←B.sum_equivFun a0,map_sum]; simp only [map_smul]
  rw [←he,←hx]
  exact tendsto_finsetSum _ (fun i _ => (((B.coord i).toContinuousLinearMap.continuous.continuousAt.tendsto.comp ha).smul (h (B i))))

lemma moving_zero {L : ℕ→A→E→ₗ[ℂ] ℂ} {L₀ : A→E→ₗ[ℂ] ℂ} {a : ℕ→E} (hL : ∀ b v, Tendsto (fun n=> L n b v) atTop (𝓝 (L₀ b v))) (h₀ : ∀ a≠0,∃ b,L₀ b a≠0) (hd : ∀ b,Tendsto (fun n=> L n b (a n)) atTop (𝓝 0)) :
   Tendsto a atTop (𝓝 0) := by
  by_contra h
  rw [Metric.tendsto_nhds] at h
  push Not at h
  obtain ⟨ε,hε,h⟩ := h
  have hε' : ∃ᶠ i in atTop, ε ≤ ‖a i‖ := by simpa only [Filter.Frequently, not_le,dist_zero_right] using h
  obtain ⟨s,hs,hp⟩ := extraction_of_frequently_atTop hε'
  let u n := (↑(‖a (s n)‖⁻¹):ℂ) • a (s n)
  have hu n : ‖u n‖=1 := by dsimp only [u]; rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (by positivity),inv_mul_cancel₀ (lt_of_lt_of_le hε (hp n)).ne']
  obtain ⟨y,-,v,hv,hy⟩ := tendsto_subseq_of_bounded (isCompact_closedBall (0:E) 2).isBounded (x:=u) (by intro i; simp [hu])
  have ht : (fun i => ‖u (v i)‖) = (fun _ => (1:ℝ)) := funext fun i=>hu _
  have h1 : (1:ℝ)=‖y‖ := tendsto_nhds_unique (ht.symm ▸ tendsto_const_nhds (x:=(1:ℝ))) hy.norm
  obtain ⟨b,hb⟩ := h₀ y (fun he => by simpa [he] using h1)
  let k n := s (v n)
  let hup := (hs.comp hv).tendsto_atTop
  have hh := (hd b).comp hup
  have hl : Tendsto (fun n=>L (k n) b (u (v n))) atTop (𝓝 0) := by
     apply Metric.tendsto_nhds.mpr; intro c hc
     let hh := Metric.tendsto_nhds.mp hh (c*ε) (mul_pos hc hε)
     apply hh.mono; intro n hn
     dsimp only [comp_apply] at hn; rw [dist_zero_right] at *
     dsimp only [u]; rw [map_smul,norm_smul,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
     calc
       _ ≤ ε⁻¹ * ‖L (k n) b (a (k n))‖ := mul_le_mul_of_nonneg_right (inv_anti₀ hε (hp _)) (norm_nonneg _)
       _ < ε⁻¹ * (c*ε) := mul_lt_mul_of_pos_left hn (inv_pos.mpr hε)
       _ = c := by field_simp
  apply hb
  exact Eq.symm (tendsto_nhds_unique hl (moving_linear hy (fun b' => (hL _ b').comp hup)))
end YM.Pert.Scale
