import YM.Pert.Kinetic.PairData
noncomputable section
namespace YM.Pert.Kinetic
open Function Filter Set Lattice Wilson Exterior RG Precision
open Work.F03
open scoped Topology BigOperators Classical ContDiff InnerProductSpace
variable {n : Side} {G : Gauge} {σ C Λ : ℝ} {p : Clip} (W : PathData G) (hb : W.Bounds p σ C Λ) {m : ℝ} {a : fieldDir G n 1} (h : Slow a m)
include hb h
lemma term_cost (x : Site n) (v : ℕ) : |pair W a x true v - pair W a x false v| ≤ (W.loop v).budget σ * (1/σ)*m^3 := by
   unfold pair Atom.poly Atom.budget Atom.magnitude
   rw [←Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
   apply (Finset.abs_sum_le_sum_abs ..).trans; apply Finset.sum_le_sum; intro b _
   rw [← mul_sub,abs_mul]; simp_rw [Fin.prod_univ_two]
   rw [mul_assoc (|(W.loop v).coeff b|), mul_assoc |(W.loop v).coeff b|]; apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
   let T (z:Bool) (i:Fin 2) := slotAt ((W.loop v).leg i) a x z (b i)
   have ht i : |T true i - T false i| ≤ ((W.loop v).leg i).length * m^2 := by
      let y:= slotAt ((W.loop v).leg i) a x true - slotAt ((W.loop v).leg i) a x false
      refine (show |T true i - T false i| ≤ ‖(slotAt ((W.loop v).leg i) a x true - slotAt ((W.loop v).leg i) a x false)‖ from ?_).trans (h.varies _ _)
      exact le_trans (show |T true i - T false i| ≤ ‖y (b i)‖ from le_rfl) (PiLp.norm_apply_le y (b i))
   change |T true 0*T true 1 - T false 0*T false 1| ≤ _
   rw [show T true 0*T true 1 - T false 0*T false 1=(T true 0-T false 0)*T true 1 + T false 0*(T true 1-T false 1) by ring]
   apply (abs_add_le ..).trans
   rw [abs_mul,abs_mul]; apply le_trans (add_le_add (mul_le_mul (ht 0) (slot_bound h _ _ _ _) (abs_nonneg _) (by positivity)) (mul_le_mul (slot_bound h _ _ _ _) (ht 1) (abs_nonneg _) h.rate))
   have hh : (W.loop v).length = ((W.loop v).leg 0).length + ((W.loop v).leg 1).length := by unfold Atom.length;rw [Fin.sum_univ_two]
   have hM:= moment_cost hb.width ((W.loop v).length)
   have he : _ := hM; rw [hh,Nat.cast_add] at hM
   have H := mul_le_mul_of_nonneg_right hM (show 0 ≤ m^3 by have := h.rate; positivity)
   rw [hh,Nat.cast_add]; convert! H using 1 <;> ring
omit hb in lemma pair_size (x : Site n) (v : ℕ) (b : Bool) : |pair W a x b v| ≤ (W.loop v).magnitude*m^2 := by
    unfold pair Atom.poly Atom.magnitude; rw [Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum ?_); intro b _;rw [abs_mul,Fin.prod_univ_two,abs_mul, pow_two]; exact mul_le_mul_of_nonneg_left (mul_le_mul (slot_bound h _ ..) (slot_bound h _ ..) (abs_nonneg _) h.rate) (abs_nonneg _)
-- |F - F0| after exact complete frozen response.
def soloLoop (a : fieldDir G n 1) (x : Site n) := ∑' i,pair W a x true i
lemma solo_cost (x) : |soloLoop W a x| ≤ Λ/σ*m^3 := by
   have he(b): Summable (fun v=>pair W a x b v) := by
      apply Summable.of_norm_bounded (hb.two.2.1.mul_right (m^2))
      intro i; exact ((pair_size W h x i b)).trans (mul_le_mul_of_nonneg_right ((W.loop i).lower_budget _ hb.width) (sq_nonneg _)) -- missing hb argument
   unfold soloLoop; rw [← sub_zero (tsum ..), ← steady_null W hb a h x,← (he true).tsum_sub (he false)]
   refine (norm_tsum_le_tsum_norm ((he true|>.sub (he false)).norm)).trans ?_
   calc _ ≤ ∑' i,(W.loop i).budget σ*(1/σ)*m^3 := ((he true|>.sub (he false)).norm).tsum_le_tsum (term_cost W hb h _) ((hb.two.2.1.mul_right _).mul_right _)
        _ = (∑' i,(W.loop i).budget σ)*(1/σ)*m^3 := by simp only [tsum_mul_right]
        _ ≤ _ := by rw [one_div,div_eq_mul_inv]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb.two.2.2 (inv_nonneg.mpr hb.width.le)) (pow_nonneg h.rate _) -- fix
end YM.Pert.Kinetic
