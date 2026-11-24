import YM.Integration.FVA1Physical.Wilson.MovingBarrier

/-! All-power cost for the full tagged Haar history outside a fixed
small-field chart, uniformly for a neighborhood of retained boundary fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Set MeasureTheory Filter RG Lattice YM.Wilson Tree Precision RGComparison.Core16 RGComparison.Core16.Descent
open PertExtension PertExtension.Chart PertExtension.Series.Tested
open scoped Classical Topology
variable {G : Gauge} {n c : Side} (d : Descent n c)

def movingRegion (g : ℝ) (a : ℕ → ℝ) (t : d.Tags) (O : Config G n → ℝ)
    (V : Config G c) (U : Set (Fields G d)) : ℝ :=
  (g^Module.finrank ℝ (Coordinates G d))⁻¹ *
    ∫ x in U, d.integrand (offset a g) t O V x ∂d.measure G

/-- A common power bound for all signed tests bounded by B, all reset clocks
in the supplied offset band, all tags, and all small retained backgrounds.
The dimension and torus enter the constant. -/
theorem moving_exterior (h : d.Room G) (Z : ChartRatio G) (hZ : LocalRatio Z) {r : ℝ}
    (hr : 0 < r) (hs : r ≤ small G Z) (M B : ℝ) (hB : 0 ≤ B) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ g : ℝ, 0 < g →
      ∀ (a : ℕ → ℝ), d.Band M a → ∀ (V : Config G c), QuietLinks V ε →
      ∀ (t : d.Tags) (O : Config G n → ℝ), (∀ U, ‖O U‖ ≤ B) →
        ‖movingRegion d g a t O V (chamber G d.Links r)ᶜ‖ ≤ C*g^k := by
  obtain ⟨ε,K,hε,hK,barrier⟩ := moving_barrier d h Z hr hs
  let E := Module.finrank ℝ (Coordinates G d)
  let U := (chamber G d.Links r)ᶜ
  have hU : MeasurableSet U := (Chart.Ratio.chamber_open hZ hs (U:=d.Links)).isClosed_compl.measurableSet
  let A := Real.exp (M*ceiling n d)*B
  have hA : 0 ≤ A := mul_nonneg (Real.exp_pos _).le hB
  refine ⟨ε,hε,?_⟩
  intro k
  obtain ⟨D,hD,power⟩ := PertExtension.Series.Radial.bounded_exp hK (k+E)
  refine ⟨A*D,mul_nonneg hA hD,?_⟩
  intro g hg a ha V hv t O hO
  have capped (x : Fields G d) (hx : x ∈ U) :
      ‖d.integrand (offset a g) t O V x‖ ≤ A * Real.exp (-K/g^2) := by
    let w := d.probability t x
    have hw : 0 ≤ w := probability_nonneg .. 
    have hw' : w ≤ 1 := by
      rw [← total_probability (G:=G) (room_ok d h) x]
      exact Finset.single_le_sum (fun i _ => probability_nonneg d i x) (Finset.mem_univ t)
    by_cases hp : 0 < w
    · have hxK := barrier V hv t x hx hp
      have drift : -d.account a t V x ≤ M*ceiling n d := (neg_le_abs _).trans
        ((total_charge t ha V x).trans (mul_le_mul_of_nonneg_left (action_bound t V x) (nonnegativeBand ha)))
      have hprep : ‖d.probability t x * Real.exp (-d.account a t V x) * O (d.fine V x)‖ ≤ A := by
        rw [norm_mul,norm_mul,Real.norm_of_nonneg hw,Real.norm_of_nonneg (Real.exp_pos _).le]
        exact mul_le_mul ((mul_le_mul hw' (Real.exp_le_exp.mpr drift) (Real.exp_pos _).le zero_le_one).trans_eq (one_mul _))
          (hO _) (norm_nonneg _) (Real.exp_pos _).le
      have exact_integrand : d.integrand (offset a g) t O V x =
          (d.probability t x * Real.exp (-d.account a t V x) * O (d.fine V x)) *
          Real.exp (-d.action t V x / g^2) := by
        rw [integrand,account_offset,neg_add,Real.exp_add,show
          -(g⁻¹^2*d.action t V x) = -d.action t V x/g^2 by rw [inv_pow,div_eq_mul_inv]; ring]
        ring
      rw [exact_integrand,norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le]
      exact mul_le_mul hprep (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (neg_le_neg hxK) (sq_nonneg _)))
        (Real.exp_pos _).le hA
    · have zero : d.probability t x=0 := le_antisymm (le_of_not_gt hp) hw
      simp only [integrand,zero,zero_mul,norm_zero]
      exact mul_nonneg hA (Real.exp_pos _).le
  have integral : ‖∫ x in U, d.integrand (offset a g) t O V x ∂d.measure G‖ ≤ A*Real.exp (-K/g^2) :=
    (norm_integral_le_of_norm_le (g:=fun _=>A*Real.exp (-K/g^2)) (integrable_const _)
      ((ae_restrict_mem hU).mono capped)).trans
    ((setIntegral_le_integral (μ:=d.measure G) (f:=fun _=>A*Real.exp (-K/g^2)) (integrable_const _)
       (Eventually.of_forall fun _=>mul_nonneg hA (Real.exp_pos _).le)).trans_eq (by simp))
  have scalar : (g^E)⁻¹ * Real.exp (-K/g^2) ≤ D*g^k := by
    apply le_of_mul_le_mul_left (a:=g⁻¹^k) ?_ (pow_pos (inv_pos.mpr hg) _)
    calc
      _ = g⁻¹^(k+E) * Real.exp (-K*(g⁻¹)^2) := by rw [inv_pow,inv_pow,inv_pow,pow_add,mul_inv,←mul_assoc,div_eq_mul_inv]
      _ ≤ D := le_trans (by gcongr; linarith) (power g⁻¹ (inv_pos.mpr hg).le)
      _ = _ := by rw [inv_pow,mul_left_comm,inv_mul_cancel₀ (pow_pos hg _).ne',mul_one]
  change ‖(g^E)⁻¹ * _‖ ≤ _
  rw [norm_mul,Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg hg.le _))]
  exact (mul_le_mul_of_nonneg_left integral (inv_nonneg.mpr (pow_nonneg hg.le _))).trans <|
    (mul_left_comm _ A _).le.trans ((mul_le_mul_of_nonneg_left scalar hA).trans_eq (mul_assoc ..).symm)

end YM.Integration.FVA1Physical.Wilson
