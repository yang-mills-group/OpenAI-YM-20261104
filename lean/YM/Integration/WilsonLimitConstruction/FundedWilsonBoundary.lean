import YM.Integration.WilsonLimitConstruction.FundedWilsonGerm
import YM.Integration.WilsonLimitConstruction.FundedWilsonHaar
import YM.Integration.WilsonLimitConstruction.FundedCensusVacuum

/-! The variable-coupling Wilson curve hits the literal original ultraviolet
density, including every inserted original observable. A continuous correction
to the inverse square reaches every coupling beyond its endpoint value. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedWilsonBoundary

open Filter Set Lattice Wilson RG Exterior PhysicalNext.Repeat.Legato
open FundedWilsonGerm
open scoped Topology
variable {G : Gauge}

theorem hits {a b : ℝ} (ha : 0 < a) (P : ℝ → ℝ)
    (hP : ContinuousOn P (Icc 0 a)) (hb : (a^2)⁻¹ + P a ≤ b) :
    ∃ t ∈ Ioc 0 a, (t^2)⁻¹ + P t = b := by
  obtain ⟨u,hu,hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr ha.le) hP
  let K := max 1 (b - P u)
  have hK : 1 ≤ K := le_max_left _ _
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  let s := min a K⁻¹
  have hs : 0 < s := lt_min ha (inv_pos.mpr hK0)
  have hsa : s ≤ a := min_le_left _ _
  have hKs : s * K ≤ 1 := (le_div_iff₀ hK0).mp (by simpa only [one_div] using (min_le_right a K⁻¹))
  have hs1 : s ≤ 1 := (le_mul_of_one_le_right hs.le hK).trans hKs
  have hbound : K ≤ (s^2)⁻¹ := by
    rw [← one_div,le_div_iff₀ (sq_pos_of_pos hs)]
    calc K * s^2 = (s*K)*s := by ring
         _ ≤ 1*1 := mul_le_mul hKs hs1 hs.le zero_le_one
         _ = 1 := one_mul _
  have hhi : b ≤ (s^2)⁻¹ + P s := by
    have hval : P u ≤ P s := hmin (show s ∈ Icc 0 a from ⟨hs.le,hsa⟩)
    have hk : b - P u ≤ K := le_max_right _ _
    linarith
  have hcont : ContinuousOn (fun t : ℝ => (t^2)⁻¹ + P t) (Icc s a) :=
    ((continuousOn_id.pow 2).inv₀ fun t ht => pow_ne_zero 2 (hs.trans_le ht.1).ne').add
      (hP.mono (Icc_subset_Icc hs.le le_rfl))
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc' hsa hcont (show b ∈ Icc _ _ from ⟨hb,hhi⟩)
  exact ⟨t,⟨hs.trans_le ht.1,ht.2⟩,he⟩

theorem funded (R : Run G) (N p : ℕ) (B : fieldDir G (R.family.side N p) 1)
    (C : Curve B) (P : ℝ → ℝ) {t : ℝ} (ht : t ≠ 0)
    (hβ : (t^2)⁻¹ + P t = R.family.beta N p) :
    (R.family.path.rep N p N).eval (ray B t) = Real.exp (-corrected C P t) := by
  have htop : (R.family.path.rep N p N).eval = bare (R.family.beta N p) := (R.makes.wilson.starts N p).2
  rw [htop, ← hβ]
  exact exact_bare C P ht

theorem inserted (R : Run G) (N p d : ℕ) (v : R.family.label d)
    (hd : R.family.ref d ≤ N) (B : fieldDir G (R.family.side N p) 1)
    (C : Curve B) (P : ℝ → ℝ) {t : ℝ} (ht : t ≠ 0)
    (hβ : (t^2)⁻¹ + P t = R.family.beta N p) :
    let U := ray B t
    ((R.family.factory d N p).entries N ((R.family.factory d N p).terminal.symm v)).density 0
      (R.family.localSection d) (R.family.path.rep N p N) U =
      (R.family.S.a N : ℂ)^d * (Real.exp (-corrected C P t) : ℝ) * R.family.O N p v 0 U := by
  intro U
  have he := (R.makes.calibrated d N p hd).encode ((R.family.factory d N p).terminal.symm v) U
  change _ = _ * ((R.family.path.rep N p N).eval U : ℂ) * R.family.O N p v 0 U at he
  rw [show (R.family.path.rep N p N).eval U = _ from funded R N p B C P ht hβ] at he
  exact he

/-- The parameter is selected before the field direction or the source. -/
theorem purchase (R : Run G) (N p : ℕ) {a : ℝ} (ha : 0 < a) (P : ℝ → ℝ)
    (hP : ContinuousOn P (Icc 0 a)) (hβ : (a^2)⁻¹ + P a ≤ R.family.beta N p) :
    ∃ t ∈ Ioc 0 a, (t^2)⁻¹ + P t = R.family.beta N p ∧
      ∀ B : fieldDir G (R.family.side N p) 1, ∃ C : Curve B,
        (R.family.path.rep N p N).eval (ray B t) = Real.exp (-corrected C P t) ∧
        ∀ k, iteratedDeriv k C.value 0 / (k.factorial : ℝ) =
          iteratedDeriv (k+2) (action B) 0 / ((k+2).factorial : ℝ) := by
  obtain ⟨t,ht,he⟩ := hits ha P hP hβ
  refine ⟨t,ht,he,fun B => ?_⟩
  obtain ⟨C⟩ := FundedWilsonGerm.purchase B
  exact ⟨C,funded R N p B C P ht.1.ne' he,coefficient C⟩

/-- The uncorrected bare physical coupling and its actual funded regulator. -/
theorem original (R : Run G) (N p : ℕ) (B : fieldDir G (R.family.side N p) 1)
    (C : Curve B) :
    let t := (Real.sqrt (R.family.beta N p))⁻¹
    (R.family.path.rep N p N).eval (ray B t) = Real.exp (-C.value t) := by
  intro t
  have hb : 0 < R.family.beta N p :=
    lt_of_lt_of_le (half_pos (zero_lt_one.trans (R.family.path.levels.fits.delayed _)))
      (R.makes.wilson.represents N p N le_rfl).band.1
  have ht : t ≠ 0 := (inv_pos.mpr (Real.sqrt_pos.mpr hb)).ne'
  have he : (t ^ 2)⁻¹ + (0:ℝ) = R.family.beta N p := by
    rw [add_zero]
    dsimp only [t]
    rw [inv_pow, inv_inv,Real.sq_sqrt hb.le]
  simpa only [corrected,zero_mul, add_zero] using funded R N p B C (fun _ => 0) ht he

end YM.Integration.WilsonLimitConstruction.FundedWilsonBoundary
end
