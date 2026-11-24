import YM.MSbar.Pole.Analysis.Capacity

/-! Spend integrable budgets per Leibniz term, in particular without any
uniformity in the requested order. -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole
open Function Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators Classical
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Z : Type*} [MeasurableSpace Z]
variable {μ : Measure Z} {p q : Price E} {U : Set E} {F G H : Z → E → ℂ}
lemma leibniz (hmF : ∀ x∈U, AEStronglyMeasurable (fun z => F z x) μ)
    (hmG : ∀ x∈U, AEStronglyMeasurable (fun z => G z x) μ)
    (o : IsOpen U) (c : ContinuousOn p.val U)
    (hF : ∀ᵐ z ∂μ, ∀ x∈U, ContDiffAt ℝ ∞ (F z) x)
    (hG : ∀ᵐ z ∂μ, ∀ x∈U, ContDiffAt ℝ ∞ (G z) x)
    (hh : ∀ i j (k:ℕ), ∃ (b : Z → ℝ) (l : ℕ), (∀ᵐ z ∂μ,0 ≤ b z) ∧ Integrable b μ ∧ ∀ᵐ z ∂μ, ∀ x∈U,
      ‖iteratedFDeriv ℝ i (F z) x‖ * ‖iteratedFDeriv ℝ j (G z) x‖ * q x^k ≤ b z * p x^l) :
    Barrel μ U p q (fun z x => F z x*G z x) := by
  refine ⟨o,c,(hF.and hG).mono fun z hz x hx => (hz.1 x hx).mul (hz.2 x hx), fun x hx => (hmF x hx).mul (hmG x hx),fun i k => ?_⟩
  choose b l hb hc ha using (fun t : ℕ => hh t (i-t) k)
  let A:= Finset.range (i+1)
  let L := A.sup l
  let C (t : ℕ) : ℝ := (i.choose t)
  refine ⟨fun z=>∑ t∈A,C t*b t z,L,?_ ,integrable_finsetSum _ fun t _ => (hc t).const_mul _,?_⟩
  · filter_upwards [eventually_all_finset A |>.mpr (fun t _ => hb t)] with z hz; exact Finset.sum_nonneg fun t ht => mul_nonneg (by unfold C; positivity) (hz t ht)
  filter_upwards [hF,hG,eventually_all_finset A |>.mpr fun t _ => ha t, eventually_all_finset A|>.mpr (fun t _ => hb t)] with z hf hg hh he x hx
  have h' := norm_iteratedFDerivWithin_mul_le (o.contDiffOn_iff.mpr hf) (o.contDiffOn_iff.mpr hg) o.uniqueDiffOn hx (n:=i) (by exact_mod_cast (show (↑i:ℕ∞) ≤ ⊤ from le_top))
  simp_rw [iteratedFDerivWithin_of_isOpen _ o hx] at h'
  refine (mul_le_mul_of_nonneg_right h' (pow_nonneg (q.pos _).le _)).trans ?_
  rw [Finset.sum_mul,Finset.sum_mul]
  refine Finset.sum_le_sum (s:=A) (fun t ht => ?_)
  simp_rw [mul_assoc]; rw [← mul_assoc (b:=‖iteratedFDeriv ℝ (i-t) (G z) x‖) (c:=q x^k)]
  exact mul_le_mul_of_nonneg_left ((hh t ht x hx).trans (mul_le_mul_of_nonneg_left (p.snap x (Finset.le_sup ht)) (he t ht))) (by positivity)

lemma leibniz_small (hF : Barrel μ U p q F) (hmG : ∀ x∈U, AEStronglyMeasurable (fun z => G z x) μ)
    (hG : ∀ᵐ z ∂μ, ∀ x∈U, ContDiffAt ℝ ∞ (G z) x)
    (hh : ∀ i, ∃ C : ℝ, 0≤C∧∀ᵐ z ∂μ, ∀ x∈U, ‖iteratedFDeriv ℝ i (G z) x‖ ≤ C) :
    Barrel μ U p q (fun z x => F z x * G z x) := by
  refine leibniz hF.measurable hmG hF.roomy hF.scale hF.ambient hG fun i j k => ?_
  obtain ⟨C,hc,h⟩:= hh j
  obtain ⟨b,l,hb,hbi,hf⟩:= hF.receipt i k
  refine ⟨fun z=>b z*C,l,hb.mono fun _ ha => mul_nonneg ha hc, hbi.mul_const _,?_⟩
  filter_upwards [h,hb,hf] with z h ha he x hx
  rw [mul_right_comm,mul_right_comm (b:=C)]; exact mul_le_mul (he x hx) (h x hx) (norm_nonneg _) (mul_nonneg ha (pow_nonneg (p.pos _).le _))
end YM.MSbar.Pole
