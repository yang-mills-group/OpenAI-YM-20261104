import YM.MSbar.Pole.Dimension.Overlay

/-! # Horizontal and radial interchange in genuine DR -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.Radial
open Function Set Filter MeasureTheory
open scoped Topology ContDiff Classical BigOperators Real
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Regardless of budget, this computation only reads the given fiber. -/
lemma recorded {f : ℝ × E→ℂ} {g : ℝ × F→ℂ} {x:E} {y:F} (h : ∀ t, f (t,x)=g (t,y)) [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] :
    dimensional f x=dimensional g y:=by
  have he (k : ℕ) : ∀ t : ℝ,higher^[k] f (t,x)=higher^[k] g (t,y) := by
    induction k with
    | zero => exact h
    | succ k ih =>
      intro t; simp only [iterate_succ_apply']
      change -(2:ℝ)⁻¹ • (∫ a in Ioc (0:ℝ) 1, deriv (fun s:ℝ => deriv (fun u:ℝ=>higher^[k] f (u,x)) s) (a*t))= -(2:ℝ)⁻¹ • (∫ a in Ioc (0:ℝ) 1, deriv (fun s:ℝ => deriv (fun u:ℝ=>higher^[k] g (u,y)) s) (a*t))
      simp_rw [ih]
  funext w; unfold dimensional Jstep; simp_rw [he]
variable {G : ℝ × ℂ → ℂ} (p : fullPlane G)
local notation "T" => Ioi (0:ℝ)
include p
lemma spend_plane {w : ℂ} (h : 2 ≤ w.re) :
    Integrable (fun u: ℝ × ℂ=> G u * (u.1:ℂ)^(w-1)) ((volume.restrict (Ioi (0:ℝ))).prod volume) := by
  rw [show ((volume.restrict (Ioi (0:ℝ))).prod (volume:Measure ℂ))=volume.restrict (T ×ˢ (univ:Set ℂ)) by
    rw [Measure.volume_eq_prod,← Measure.prod_restrict,Measure.restrict_univ]]
  let Z := T ×ˢ (univ:Set ℂ); let X := ticket (@id (ℝ × ℂ))
  have he : Bills Z 1 X G := by
    apply Bills.weakening (fast:=Moment (ticket (@id ℂ)))
    · exact (Packet.values p).mono fun z h=> ⟨mem_univ _,h.2⟩
    exact bill_byprice (p:=Moment _) fun x _ => ticket_product x
  obtain ⟨M,hM⟩ := exists_nat_gt w.re
  let B : ℝ × ℂ → ℂ:= fun u => (u.1:ℂ)^(w-1)
  have hh : Bills Z (1*X) 1 (fun u=> ‖B u‖) := by
    refine bill_single (l:=M) zero_le_one fun u hu=>?_
    have hp : 0<u.1:= hu.1
    have hb' : (w-1).re ≤ M:= by rw [Complex.sub_re]; simp; linarith
    change ‖‖(u.1:ℂ)^(w-1)‖‖ ≤ _; rw [norm_norm,Complex.norm_cpow_eq_rpow_re_of_pos hp]; simp only [mul_price,Price.one_apply,one_mul]
    by_cases hv : u.1≤1
    · exact (Real.rpow_le_one hp.le hv (by simp; linarith)).trans (one_le_pow₀ (X.large _))
    have hg := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hv) hb'
    refine hg.trans ?_; rw [Real.rpow_natCast]; apply pow_le_pow_left₀ hp.le
    calc
      _ ≤ ‖u.1‖ := le_abs_self _
      _ ≤ ‖u‖ := norm_fst_le _
      _ ≤ _ := by simp [X]
  haveI : (volume:Measure (ℝ × ℂ)).IsAddHaarMeasure := by rw [Measure.volume_eq_prod]; infer_instance
  apply rapid_pay (h:=(he.norm.spend hh).dominates fun x hx => ?_) (measurableSet_Ioi.prod MeasurableSet.univ)
  · refine ContinuousOn.aestronglyMeasurable ?_ (measurableSet_Ioi.prod MeasurableSet.univ)
    intro x hx
    exact ((Packet.smooth p _ ⟨mem_univ _,mem_univ _⟩).continuousAt.mul ((Complex.continuous_ofReal.comp continuous_fst).continuousAt.cpow continuousAt_const
        (show (x.1:ℂ)∈Complex.slitPlane from Complex.ofReal_mem_slitPlane.mpr hx.1))).continuousWithinAt
  change ‖G x * B x‖ ≤ ‖‖G x‖*‖B x‖‖
  simp

lemma gradation (h : Globular G) (w : ℂ) : (∫ x:ℂ, dimensional G x w) = (π:ℂ)*dimensional G 0 (w+2) := by
  obtain ⟨k,hk⟩ : ∃ k:ℕ,2≤(w+2+2*k).re := by
    obtain ⟨k,hk⟩:= exists_nat_gt (-w.re); refine ⟨k,?_⟩; simp; linarith
  have hr : w+2*((k+1:ℕ):ℂ)= w+2+2*k := by push_cast; ring
  let W:=w+2+2*k
  have he':EvenOn univ G:=h.even
  have hp : ∀ k:ℕ,fullPlane (higher^[k] G) ∧ Globular (higher^[k] G) := by
    intro k; induction k with
    | zero => exact ⟨p,h⟩
    | succ k ih => rw [iterate_succ_apply']; exact ⟨up_plane ih.1 ih.2,round_higher ih.1 ih.2⟩
  have hc : ContinuousOn (1:Price ℂ).val univ:= continuousOn_const
  simp_rw [reached (x:=0) isOpen_univ hc p he' (mem_univ _) (w+2) k hk]
  simp_rw [fun x : ℂ => reached isOpen_univ hc p he' (mem_univ x) w (k+1) (by rwa [hr])]
  unfold Jstep j
  simp_rw [hr]; rw [integral_const_mul,integral_integral_swap]
  · simp_rw [integral_mul_const]; let H:=higher^[k] G
    have ht (t:ℝ) : (∫ x:ℂ,higher^[k+1] G (t,x))=(π:ℂ)*H (t,0) := by rw [iterate_succ_apply']; exact across (hp k).1 (hp k).2 _
    simp_rw [ht,mul_assoc (π:ℂ)]; rw [integral_const_mul,mul_left_comm]
  let X (u : ℝ × ℂ) := (higher^[k+1]) G u * (u.1:ℂ)^(W-1)
  exact (integrable_swap_iff.mpr (show Integrable X ((volume.restrict (Ioi (0:ℝ))).prod volume) from spend_plane (hp (k+1)).1 hk))
end YM.MSbar.Pole.Radial
