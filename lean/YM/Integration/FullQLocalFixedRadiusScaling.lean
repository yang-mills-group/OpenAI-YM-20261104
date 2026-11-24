import YM.Integration.FullQLocalOutputScaling
import YM.Push.LOCAL_SPLITTING.Budget

/-! Fixed-radius contraction of the same complete marked packet.
The root guard supplies a marked variable in every charged row. Geometry,
paths, tests and radii are unchanged. Restoring variables still multiplies
each full defect coefficient by the inverse product of its variable scales. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FullQLocal.FixedRadiusScaling
open Function Finset Lattice Wilson RG Marker LocalComparison
open Comparison.Density.RenderM
open VariableScaling
open scoped Classical BigOperators

variable {G : Gauge} {V : Type} [DecidableEq V]
    {D : V → ComparisonDensity.Address.Orbit} {R : Census V}

private theorem product_le (c : V → ℂ) (t : ℝ) (ht : t ≤ 1)
    (hc : ∀ v, ‖c v‖ ≤ t) (s : Finset V) (v : V) (hv : v ∈ s) :
    (∏ u ∈ s, ‖c u‖) ≤ t := by
  rw [← Finset.mul_prod_erase s (fun u => ‖c u‖) hv]
  calc
    ‖c v‖ * (∏ u ∈ s.erase v, ‖c u‖) ≤ ‖c v‖ * 1 :=
      mul_le_mul_of_nonneg_left
        (Finset.prod_le_one (fun _ _ => norm_nonneg _)
          (fun u _ => (hc u).trans ht)) (norm_nonneg _)
    _ = ‖c v‖ := mul_one _
    _ ≤ t := hc v

private theorem rooted_scale {n : Side} (c : V → ℂ)
    (P : MarkedPackets D G n R) (w : V → ℝ) (g width : ℝ) (v : V) (i : ℕ) :
    (if v ∈ ((packets c P).mode i).val then
      match (packets c P).packet i with
      | none => 0
      | some T => Poly.toll w ((packets c P).mode i) *
          ‖(g : ℂ) ^ (packets c P).power i‖ * T.coin * Real.exp (width * T.fall)
    else 0) =
    (∏ u ∈ (P.mode i).val, ‖c u‖) *
      (if v ∈ (P.mode i).val then
        match P.packet i with
        | none => 0
        | some T => Poly.toll w (P.mode i) * ‖(g : ℂ) ^ P.power i‖ *
            T.coin * Real.exp (width * T.fall)
      else 0) := by
  by_cases hv : v ∈ (P.mode i).val
  · cases hi : P.packet i with
    | none => simp [packets, hi, hv]
    | some T =>
      simp only [packets, if_pos hv, hi, Option.map_some, token]
      ring
  · simp [packets, hv]

/-- Nonzero variable contraction pays the same radii and geometry with a
smaller root budget. No unguarded constant-mode price assertion is made. -/
theorem paid_contract {n : Side} (c : V → ℂ) (hc : ∀ v, c v ≠ 0)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hct : ∀ v, ‖c v‖ ≤ t)
    (P : MarkedPackets D G n R)
    {p : BudgetPoint} {address : V → Support n}
    {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n}
    {w : V → ℝ} {g width budget target : ℝ} {coverOffset coverSlope : ℕ}
    (hP : P.Paid p address region w g width budget coverOffset coverSlope)
    (hbudget : t * budget ≤ target) :
    (packets c P).Paid p address region w g width target coverOffset coverSlope := by
  have h := VariableScaling.paid c hc P hP
  refine
    { width_pos := h.width_pos
      positive := hP.positive
      coefficient := h.coefficient
      paths := h.paths
      addresses := h.addresses
      symmetry := h.symmetry
      reads := h.reads
      multilinear := h.multilinear
      roots := ?_
      cover := h.cover
      width_reserved := h.width_reserved }
  intro v
  apply Push.Local.sumBudget_mono
    (Push.Local.sumBudget_mul_left (hP.roots v) ht0)
  · intro i
    by_cases hv : v ∈ (P.mode i).val
    · cases hi : P.packet i with
      | none => simp [packets, hi, hv]
      | some T =>
        have hn := (hP.roots v).1 i
        simp only [if_pos hv, hi] at hn
        have hs := mul_nonneg (Finset.prod_nonneg (s := (P.mode i).val)
          (fun u _ => norm_nonneg (c u))) hn
        simp only [packets, if_pos hv, hi, Option.map_some, token]
        convert hs using 1 <;> first | rfl | ring
    · simp [packets, hv]
  · intro i
    by_cases hv : v ∈ (P.mode i).val
    · cases hi : P.packet i with
      | none => simp [packets, hi, hv]
      | some T =>
        have hn := (hP.roots v).1 i
        simp only [if_pos hv, hi] at hn
        have hs := mul_le_mul_of_nonneg_right
          (product_le c t ht1 hct (P.mode i).val v hv) hn
        simp only [packets, if_pos hv, hi, Option.map_some, token]
        convert hs using 1 <;> first | rfl | ring
    · simp [packets, hv]
  · exact hbudget

/-- A genuine finite bill determines the normalization; no new uniform-cost
hypothesis is inserted. Every original radius, cover and path is retained. -/
theorem paid_normalized {n : Side} (P : MarkedPackets D G n R)
    {p : BudgetPoint} {address : V → Support n}
    {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n}
    {w : V → ℝ} {g width budget : ℝ} {coverOffset coverSlope : ℕ}
    (hP : P.Paid p address region w g width budget coverOffset coverSlope)
    (H : ℝ) (hH : 1 ≤ H) (hbudget : budget ≤ H) :
    (packets (fun _ : V => (H : ℂ)⁻¹) P).Paid p address region w g width 1
      coverOffset coverSlope := by
  have hpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hc : ∀ _ : V, (H : ℂ)⁻¹ ≠ 0 := fun _ =>
    inv_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne')
  have hle : H⁻¹ ≤ 1 := by
    simpa only [one_div] using (div_le_one hpos).mpr hH
  have hn : ∀ _ : V, ‖(H : ℂ)⁻¹‖ ≤ H⁻¹ := by
    intro v
    simpa only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
      using (le_refl (H⁻¹))
  have hb : H⁻¹ * budget ≤ 1 := by
    simpa only [div_eq_mul_inv, mul_comm] using (div_le_one hpos).mpr hbudget
  exact paid_contract (fun _ : V => (H : ℂ)⁻¹) hc H⁻¹
    (inv_nonneg.mpr hpos.le) hle hn P hP hb

end YM.Integration.FullQLocal.FixedRadiusScaling
end
