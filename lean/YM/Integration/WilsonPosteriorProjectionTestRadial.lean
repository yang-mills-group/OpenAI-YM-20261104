import YM.Integration.WilsonPosteriorProjectionTestTensor

/-! The full nonlinear original test applied to one measured function on
actual group links and the independently provided polynomial chart. All
chain-rule ranks refer to one pair of functions on one torus. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPosteriorProjectionTestRadial

open Set Function Filter Finset Lattice Wilson RG Source Labels Next.Foundations Precision Tree Exterior
open MSbar MSbar.Cacao MSbar.Whisk MSbar.Lis MSbar.Rolling Push.Uniform
open WilsonPosteriorProjectionTestGrowth
open scoped Classical Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge}

private theorem order {k : ℕ} (r : OrderedFinpartition k) : ∑ i, (r.partSize i-1) ≤ k := by
  have h : ∑ i, r.partSize i = k := by
    simpa only [Fintype.card_fin,Fintype.card_sigma] using Fintype.card_congr r.equivSigma
  exact (Finset.sum_le_sum fun i _ => Nat.sub_le (r.partSize i) 1).trans_eq h

theorem ratio (H : Hol G) (d k : ℕ) (J : Jet G) (hk : 0<k) (s : ℕ) (ks : k ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : Side) (b : Site n) (g θ ε : ℝ), 0<g → 0≤θ → θ≤1 → 0≤ε →
      ∀ (a : ℕ→ℝ) (φ : Config G n→ℝ) (bank : Positions (Primary n G)→ℝ),
      let F := φ ∘ postcard G n g
      ContDiffAt ℝ k F 0 → ContDiffAt ℝ k bank 0 →
      (∀ q, 0<q → q≤k → 0 ≤ a q ∧ Yarn q (fun l =>
        |buoy F 0 l-buoy bank 0 l| * spread (Measuring.chart n G) {b} (a q) s l) ≤ ε) →
      |iteratedDeriv k (φ ∘ H.testLinks d b (θ • J)) 0 -
       iteratedDeriv k (bank ∘ WilsonPosteriorProjectionTestGrowth.curve H d b (θ • J) g) 0| ≤ C*(max 1 (g⁻¹*θ))^k*ε := by
  choose C pos price using fun r : OrderedFinpartition k =>
    WilsonPosteriorProjectionTestTensor.actual H d J r.partSize s ((order r).trans ks)
  refine ⟨∑ r,C r,Finset.sum_nonneg fun r _ => (pos r).le,?_⟩
  intro n b g θ ε hg hθ θ1 hε a φ bank F hf hb paid
  let Z := WilsonPosteriorProjectionTestGrowth.curve H d b (θ • J) g
  have zero : Z 0=0 := center H d b _ g
  have smooth : ContDiffAt ℝ k Z 0 := (regular H d b _ g).of_le le_top
  have physical : φ ∘ H.testLinks d b (θ • J) =ᶠ[𝓝 0] F ∘ Z :=
    (WilsonPosteriorProjectionTestGrowth.physical H d b _ hg.ne').fun_comp φ
  rw [physical.iteratedDeriv_eq,iteratedDeriv_vcomp_eq_sum_orderedFinpartition (zero.symm ▸ hf) smooth le_rfl,
    iteratedDeriv_vcomp_eq_sum_orderedFinpartition (zero.symm ▸ hb) smooth le_rfl,zero,
    ←Finset.sum_sub_distrib, Finset.sum_mul,Finset.sum_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro r _
  obtain ⟨width,wires⟩ := paid r.length (r.length_pos hk) r.length_le
  have qk : (r.length : WithTop ℕ∞) ≤ k := Nat.cast_le.mpr r.length_le
  have term := price r n b g θ (a r.length) hg hθ θ1 width F bank (hf.of_le qk) (hb.of_le qk)
  have loss : (g⁻¹*θ)^r.length ≤ (max 1 (g⁻¹*θ))^k :=
    (pow_le_pow_left₀ (mul_nonneg (inv_pos.mpr hg).le hθ) (le_max_right ..) _).trans
      (pow_le_pow_right₀ (le_max_left ..) r.length_le)
  apply term.trans
  apply (mul_le_mul_of_nonneg_left wires (mul_nonneg (pos r).le
    (pow_nonneg (mul_nonneg (inv_pos.mpr hg).le hθ) _))).trans
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left loss (pos r).le) hε


theorem measured (H : Hol G) (d k : ℕ) (J : Jet G) (hk : 0<k) (s : ℕ) (ks : k ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : Side) (b : Site n) (g θ ε : ℝ), 0<g → g≤1 → 0≤θ → θ≤1 → 0≤ε →
      ∀ (a : ℕ→ℝ) (φ : Config G n→ℝ) (bank : Positions (Primary n G)→ℝ),
      let F := φ ∘ postcard G n g
      ContDiffAt ℝ k F 0 → ContDiffAt ℝ k bank 0 →
      (∀ q, 0<q → q≤k → 0 ≤ a q ∧ Yarn q (fun l =>
        |buoy F 0 l-buoy bank 0 l| * spread (Measuring.chart n G) {b} (a q) s l) ≤ ε) →
      |iteratedDeriv k (φ ∘ H.testLinks d b (θ • J)) 0 -
       iteratedDeriv k (bank ∘ WilsonPosteriorProjectionTestGrowth.curve H d b (θ • J) g) 0| ≤ C*g⁻¹^k*ε := by
  obtain ⟨C,C0,price⟩ := ratio H d k J hk s ks
  refine ⟨C,C0,?_⟩
  intro n b g θ ε hg g1 hθ θ1 hε a φ bank F hf hb paid
  apply (price n b g θ ε hg hθ θ1 hε a φ bank hf hb paid).trans
  have upper : max 1 (g⁻¹*θ) ≤ g⁻¹ :=
    max_le ((one_le_inv₀ hg).mpr g1) (mul_le_of_le_one_right (inv_pos.mpr hg).le θ1)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (zero_le_one.trans (le_max_left ..)) upper _) C0) hε

end YM.Integration.WilsonPosteriorProjectionTestRadial
end


