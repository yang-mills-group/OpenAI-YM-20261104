import YM.WilsonMS.Beta.PaidMS
/-!
# UV boundary on the Leg4 MS kernels

Utilities for isolated members of `Archive`: off course not used. Keep the
counterterm constant at dim=4 without assigning it by any convenient theory.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.BetaValue
open Function Filter Set Finset MeasureTheory Metric
open LoopRank Lattice MS Plane Koszul Heat Flux Landau Tone Momentum Real Frame Wire Color Detect
  Native
open Book Convolve City Logarithm Signal Landau.Detect.Mark Wind High Knobs Rider
open LogTime LogTime.IntervalFamily Outlook Land Arc Wire Rock Path Oceans Plum Alps Garment Color
  Pearl
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {b : Bool} {n : ℕ} {B : Local.Physical.Deck G} {M : Booked B}
variable (F : MS_Data G M) (x t : ℝ) (w : Legs (Lane4 G))
set_option quotPrecheck false
local notation "V" => Archive 4 F.bulk
local notation "𝒁" => (spaceD G).meter

abbrev crown (w : Legs (Lane4 G)) :=
  fieldDim wfield w

abbrev apex (w : Legs (Lane4 G)) :=
  sail (ray w) 0

lemma dimension0 : crown (apex w) = crown w :=
  (sail_dim _ _).trans (ray_dim _)

lemma apex_here : sail (ray (apex w)) x = apex w := by
  simp only [apex, ray_go, List.map_map, Function.comp_def, zero_smul, smul_zero]

lemma fullness : (apex w).length = w.length :=
  (sail_len _ _).trans (ray_len _)
section coast

lemma η (hn : 0 < n) (hx : Course true w) (hp : 0 < w.length) :
    HasDerivAt (fun t => V n (x, t) w) (ledgerR F n (x, t) w) t := by
  obtain h :=
    ((archive_disc F).master.road ℝ (ray w) n hn
            (fun _ => by
              rw [ray_len]
              exact hp)
            (ray_course hx)).2.2
      x t 1 0
  let L (i : ℝ) := V n (x, i) w
  let A := ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => ℝ) ℂ (fun _ => 1)
  convert! (A.hasFDerivAt.comp_hasDerivAt _ h) using 1
  · ext1 y
    change _ = iteratedDeriv 0 (fun u => V n (x, y) (sail (ray w) u)) 1
    rw [iteratedDeriv_zero]
    simp
  change _ = iteratedDeriv 0 (fun v => (ledgerR F n (x, t)) (sail (ray w) v)) 1
  rw [iteratedDeriv_zero]
  simp

lemma UV_boundary (h : 4 < crown w) : Tendsto (fun t : ℝ => V n (x, t) w) atBot (𝓝 0) := by
  let X₀ y := V n (y, 0)
  obtain ⟨N, hN⟩ :=
    (show Ready X₀ from ((archive_disc F).master.poly n).linear (LinearMap.proj (0 : ℝ)))
  let d := crown w - 4
  simp_rw [archive_plowed F n _ x w]
  change Tendsto (fun t : ℝ => exp t ^ d • X₀ (x + t) (sail (ray w) (exp t))) _ _
  simp_rw [interpret hN, evaluate, Finset.sum_apply, Finset.smul_sum]
  let P (i : ℕ) (t : ℝ) := Port.τ d t * (((plate N i).eval (x + t) : ℝ) : ℂ)
  have hh (i : ℕ) : Tendsto (P i) atBot (𝓝 0) := by
    have hx := (pos_exp (plate N i) x (show (0 : ℝ) < d from by exact_mod_cast sub_pos.mpr h))
    simp only [Complex.ofReal_intCast, Port.τ_amt] at hx
    exact hx
  have hz (i : ℕ) :
    Tendsto (fun t : ℝ => exp t ^ d • ((plate N i).eval (x + t) • X₀ i) (sail (ray w) (exp t))) atBot
      (𝓝 0) := by
    have h :=
      (hh i).mul ((breathing F n i 0 w).continuous.continuousAt.tendsto.comp tendsto_exp_atBot)
    rw [zero_mul] at h
    apply h.congr
    intro t
    simp only [P, Function.comp_apply, Port.τ, Pi.smul_apply, Complex.real_smul, mul_assoc]
    rfl
  simpa using (tendsto_finsetSum (Finset.range N) fun i _ => hz i)

lemma UV_zero_patch (n : ℕ) (h : 4 = crown w) :
    Tendsto (fun t => V n (x, t) w - V n (x, t) (apex w)) atBot (𝓝 0) := by
  let W := apex w
  let X₀ y := V n (y, 0)
  obtain ⟨N, hN⟩ :=
    (show Ready X₀ from ((archive_disc F).master.poly n).linear (LinearMap.proj (0 : ℝ)))
  have he (t : ℝ) :
    V n (x, t) w - V n (x, t) W =
      ∑ i ∈ Finset.range N, (plate N i).eval (x + t) • (fieldVal (X₀ i) (ray w) (exp t) - X₀ i W) := by
    rw [archive_plowed F n t x w, archive_plowed F n t x W,
      show fieldDim wfield w - 4 = 0 from (sub_eq_zero.mpr h.symm),
      show fieldDim wfield W - 4 = 0 from (sub_eq_zero.mpr (h ▸ dimension0 w)), apex_here]
    simp only [zpow_zero, one_smul, smul_sub, Finset.sum_sub_distrib]
    change X₀ _ _ - X₀ _ _ = _
    nth_rw 1 [interpret hN]
    nth_rw 1 [show X₀ (x + t) = _ from interpret hN (x + t)]
    simp_rw [evaluate, Finset.sum_apply]
    rfl
  change Tendsto (fun t => V n (x, t) w - V n (x, t) W) _ _
  simp_rw [he]
  let f (i : ℕ) := fieldVal (X₀ (i : ℝ)) (ray w)
  have ht (i : ℕ) :
    Tendsto (fun t => (plate N i).eval (x + t) • (f i (exp t) - X₀ i W)) atBot (𝓝 0) := by
    have hd : HasDerivAt (f i) (deriv (f i) 0) 0 :=
      ((breathing F n i 0 w).differentiable (by simp) 0).hasDerivAt
    obtain hh :=
      hd.tendsto_slope_zero_right.comp
        (show Tendsto exp atBot (𝓝[>] 0) from
          tendsto_nhdsWithin_iff.mpr ⟨tendsto_exp_atBot, .of_forall exp_pos⟩)
    obtain hx := (pos_exp (plate N i) x zero_lt_one).mul hh
    rw [zero_mul] at hx
    apply hx.congr
    intro t
    rw [amount_mint]
    change (↑(exp (1 * t)) : ℂ) * _ * (exp t)⁻¹ • (f i (0 + exp t) - f i 0) = _
    rw [zero_add, one_mul, mul_comm (↑(exp t) : ℂ), mul_assoc, ← Complex.real_smul, ←
      Complex.real_smul, smul_inv_smul₀ (exp_pos _ |>.ne')]
    rfl
  simpa only [Finset.sum_const_zero] using (tendsto_finsetSum (Finset.range N) fun i _ => ht i)
end coast
end YM.WilsonMS.BetaValue
