import YM.Integration.NativeOriginalMainBondJets

/-! A fixed polynomial price for the full original main-action one-bond jets.
The cap occurs only in the numerical estimate; original paths and width remain
unchanged. Every constant depends on G and derivative order, before the Run. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeOriginalMainBondPrice
open RG Precision

open Lattice RG Exterior MatchingLedger.Mountain Push.Uniform
open Comparison.RG02.Assembly
open scoped BigOperators ContDiff Classical

private def richCoeff (G : Gauge) (k : ℕ) : ℝ :=
  (k.factorial : ℝ) * (1 + 4 * (2 : ℝ)^k)^k * (1 + Miner.amount G k)^k

private def heightCoeff (G : Gauge) (k : ℕ) : ℝ :=
  |Work.F02.slotConst G| * ‖Work.F02.colorReal G‖ * richCoeff G k

private def valueCoeff (G : Gauge) (k j : ℕ) : ℝ :=
  |Work.F02.slotConst G|^j * richCoeff G k

private def pairCoeff (G : Gauge) (k : ℕ) : ℝ :=
  Miner.beam * (2 : ℝ)^k * (heightCoeff G k)^2

private def compassCoeff (G : Gauge) (k : ℕ) : ℝ :=
  Real.exp 4 * Miner.ironFee G k * Fintype.card PlaqAxes +
    ((Fintype.card PlaqAxes : ℝ) * pairCoeff G k +
      (valueCoeff G k 3 + valueCoeff G k 4))

private def countCoeff : ℝ := Real.exp 1 * (Nat.factorial 6 : ℝ) * 4^6 * 2^4

def coefficient (G : Gauge) (k : ℕ) : ℝ :=
  1 + (k.factorial : ℝ)⁻¹ * compassCoeff G k * countCoeff

private theorem richCoeff_pos (G : Gauge) (k : ℕ) : 0 < richCoeff G k := by
  have h : 0 < Miner.amount G k := outer_pos G k (Miner.paintStamp G k).1
  unfold richCoeff
  positivity

private theorem heightCoeff_nn (G : Gauge) (k : ℕ) : 0 ≤ heightCoeff G k := by
  have h := richCoeff_pos G k
  unfold heightCoeff
  positivity

private theorem valueCoeff_nn (G : Gauge) (k j : ℕ) : 0 ≤ valueCoeff G k j := by
  have h := richCoeff_pos G k
  unfold valueCoeff
  positivity

private theorem compassCoeff_nn (G : Gauge) (k : ℕ) : 0 ≤ compassCoeff G k := by
  have h3 := valueCoeff_nn G k 3
  have h4 := valueCoeff_nn G k 4
  unfold compassCoeff pairCoeff Miner.beam Miner.ironFee
  positivity

private theorem countCoeff_pos : 0 < countCoeff := by unfold countCoeff; positivity

/-- This coefficient is fixed before all path data, widths, Runs and periods. -/
theorem coefficient_pos (G : Gauge) (k : ℕ) : 0 < coefficient G k := by
  have h := compassCoeff_nn G k
  have hc := countCoeff_pos
  unfold coefficient
  positivity

private theorem capped_inverse {sigma : ℝ} (hs : 0 < sigma) :
    (NativeOriginalMainBondJets.priceWidth sigma)⁻¹ ≤ 2 * (1 + sigma⁻¹) := by
  have hi : 0 ≤ sigma⁻¹ := (inv_pos.mpr hs).le
  unfold NativeOriginalMainBondJets.priceWidth
  by_cases h : sigma / 2 ≤ 1
  · rw [min_eq_left h]
    have he : (sigma / 2)⁻¹ = 2 * sigma⁻¹ := by
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    rw [he]
    linarith
  · rw [min_eq_right (le_of_lt (lt_of_not_ge h)), inv_one]
    linarith

private theorem richness_le (G : Gauge) (k : ℕ) {sigma : ℝ} (hs : 0 < sigma) :
    Miner.richness G k (NativeOriginalMainBondJets.priceWidth sigma) ≤
      richCoeff G k * (1 + sigma⁻¹)^k := by
  let mu := NativeOriginalMainBondJets.priceWidth sigma
  let Z := 1 + sigma⁻¹
  have hm : 0 < mu := lt_min (half_pos hs) zero_lt_one
  have hZ : 1 ≤ Z := by
    have h := (inv_pos.mpr hs).le
    dsimp only [Z]
    linarith
  have hr : mu / 2 ≤ Work.F02.radius mu := by
    have he := Real.add_one_le_exp (mu / 2)
    unfold Work.F02.radius
    linarith
  have hri : (Work.F02.radius mu)⁻¹ ≤ 2 * mu⁻¹ := by
    calc
      _ = 1 / Work.F02.radius mu := (one_div _).symm
      _ ≤ 1 / (mu / 2) := one_div_le_one_div_of_le (half_pos hm) hr
      _ = 2 * mu⁻¹ := by simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, one_mul]
  have hi : (Work.F02.radius mu)⁻¹ ≤ 4 * Z :=
    hri.trans (by have h := capped_inverse hs; change mu⁻¹ ≤ 2 * Z at h; linarith)
  have hb : 1 + (2 : ℝ)^k / Work.F02.radius mu ≤ (1 + 4 * (2 : ℝ)^k) * Z := by
    rw [div_eq_mul_inv]
    have h := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ (2 : ℝ)^k)
    nlinarith
  have ha : 0 < Miner.amount G k := outer_pos G k (Miner.paintStamp G k).1
  have hp := pow_le_pow_left₀ (by positivity [Work.F02.radius_pos hm]) hb k
  change (k.factorial : ℝ) * (1 + (2 : ℝ)^k / Work.F02.radius mu)^k *
      (1 + Miner.amount G k)^k ≤ richCoeff G k * Z^k
  calc
    _ ≤ (k.factorial : ℝ) * ((1 + 4 * (2 : ℝ)^k) * Z)^k *
        (1 + Miner.amount G k)^k :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity)
    _ = _ := by rw [mul_pow]; unfold richCoeff; ring

private theorem compass_le (G : Gauge) (k : ℕ) {sigma C : ℝ}
    (hs : 0 < sigma) (hC : 0 ≤ C) :
    Miner.compass₀ G k C (NativeOriginalMainBondJets.priceWidth sigma) ≤
      compassCoeff G k * (1 + C)^2 * (1 + sigma⁻¹)^(2*k) := by
  let mu := NativeOriginalMainBondJets.priceWidth sigma
  let Z := 1 + sigma⁻¹
  let R := Z^k
  let T := (1 + C) * R
  have hm : 0 < mu := lt_min (half_pos hs) zero_lt_one
  have hZ : 1 ≤ Z := by
    have h := (inv_pos.mpr hs).le
    dsimp only [Z]
    linarith
  have hR : 1 ≤ R := one_le_pow₀ hZ
  have hT : 1 ≤ T := by
    have h := mul_nonneg hC (zero_le_one.trans hR)
    dsimp only [T]
    nlinarith
  have hT2 : T ≤ T^2 := by nlinarith
  have h1 : 1 ≤ T^2 := hT.trans hT2
  have hCR : C * R ≤ T := by dsimp [T]; nlinarith
  have hh := heightCoeff_nn G k
  have hv (j : ℕ) := valueCoeff_nn G k j
  have hr := richness_le G k hs
  have hheight : Miner.height G k mu ≤ heightCoeff G k * R := by
    calc
      _ ≤ (|Work.F02.slotConst G| * ‖Work.F02.colorReal G‖) *
          (richCoeff G k * R) :=
        mul_le_mul_of_nonneg_left hr (mul_nonneg (abs_nonneg _) (norm_nonneg _))
      _ = _ := by unfold heightCoeff; ring
  have hvalue (j : ℕ) : Miner.value G k j mu ≤ valueCoeff G k j * R := by
    calc
      _ ≤ |Work.F02.slotConst G|^j * (richCoeff G k * R) :=
        mul_le_mul_of_nonneg_left hr (by positivity)
      _ = _ := by unfold valueCoeff; ring
  have hCH : C * Miner.height G k mu ≤ heightCoeff G k * T := by
    calc
      _ ≤ C * (heightCoeff G k * R) := mul_le_mul_of_nonneg_left hheight hC
      _ = heightCoeff G k * (C * R) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hCR hh
  have hpair : Miner.garnet G k C mu ≤ pairCoeff G k * T^2 := by
    have hp := pow_le_pow_left₀ (mul_nonneg hC (Miner.height_nn G k hm)) hCH 2
    calc
      _ ≤ (Miner.beam * (2 : ℝ)^k) * (heightCoeff G k * T)^2 :=
        mul_le_mul_of_nonneg_left hp (by unfold Miner.beam; positivity)
      _ = _ := by unfold pairCoeff; ring
  have hCV (j : ℕ) : C * Miner.value G k j mu ≤ valueCoeff G k j * T^2 := by
    calc
      _ ≤ C * (valueCoeff G k j * R) := mul_le_mul_of_nonneg_left (hvalue j) hC
      _ = valueCoeff G k j * (C * R) := by ring
      _ ≤ valueCoeff G k j * T := mul_le_mul_of_nonneg_left hCR (hv j)
      _ ≤ _ := mul_le_mul_of_nonneg_left hT2 (hv j)
  let A := Real.exp 4 * Miner.ironFee G k * Fintype.card PlaqAxes
  have hA : 0 ≤ A := by unfold A Miner.ironFee; positivity
  have hAT : A ≤ A * T^2 := by simpa only [mul_one] using mul_le_mul_of_nonneg_left h1 hA
  have h := add_le_add hAT
    (add_le_add (mul_le_mul_of_nonneg_left hpair (by positivity : 0 ≤ (Fintype.card PlaqAxes : ℝ)))
      (add_le_add (hCV 3) (hCV 4)))
  change Miner.compass₀ G k C mu ≤ compassCoeff G k * (1+C)^2 * Z^(2*k)
  calc
    _ ≤ A*T^2 + ((Fintype.card PlaqAxes : ℝ) * (pairCoeff G k*T^2) +
        (valueCoeff G k 3*T^2 + valueCoeff G k 4*T^2)) := h
    _ = compassCoeff G k * T^2 := by unfold compassCoeff A; ring
    _ = _ := by dsimp only [T, R]; rw [mul_pow, ← pow_mul, Nat.mul_comm k 2]; ring

private theorem count_le {sigma : ℝ} (hs : 0 < sigma) :
    countCost (NativeOriginalMainBondJets.priceWidth sigma / 2) ≤
      countCoeff * (1 + sigma⁻¹)^6 := by
  let mu := NativeOriginalMainBondJets.priceWidth sigma
  let Z := 1 + sigma⁻¹
  have hm : 0 < mu := lt_min (half_pos hs) zero_lt_one
  have hcap : mu ≤ 1 := min_le_right _ _
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hi : (mu / 2)⁻¹ ≤ 4 * Z := by
    have h := capped_inverse hs
    have he : (mu / 2)⁻¹ = 2 * mu⁻¹ := by
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    rw [he]
    change mu⁻¹ ≤ 2 * Z at h
    linarith
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (mu / 2)⁻¹) hi 6
  have he : Real.exp ((mu / 2) * 2) ≤ Real.exp 1 :=
    Real.exp_monotone (by linarith)
  calc
    _ = Real.exp ((mu / 2) * 2) * (Nat.factorial 6 : ℝ) * ((mu/2)⁻¹)^6 * 2^4 := by
      unfold countCost
      rw [div_eq_mul_inv, inv_pow]
    _ ≤ Real.exp 1 * (Nat.factorial 6 : ℝ) * (4*Z)^6 * 2^4 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul_of_nonneg_right he (by positivity)) hp
          (by positivity) (by positivity)) (by positivity)
    _ = countCoeff * Z^6 := by rw [mul_pow]; unfold countCoeff; ring

/-- Full native price, with fixed degree and no upper-bound premise on width. -/
theorem price_le (G : Gauge) (k : ℕ) {C sigma : ℝ} (hC : 0 ≤ C) (hs : 0 < sigma) :
    NativeOriginalMainBondJets.price G k C sigma ≤
      coefficient G k * (1+C)^2 * (1+sigma⁻¹)^(2*k+6) := by
  let Z := 1 + sigma⁻¹
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hc := compassCoeff_nn G k
  have hcount := countCoeff_pos
  have hm : 0 < NativeOriginalMainBondJets.priceWidth sigma := lt_min (half_pos hs) zero_lt_one
  calc
    _ ≤ ((k.factorial : ℝ)⁻¹ * (compassCoeff G k * (1+C)^2 * Z^(2*k))) *
        (countCoeff * Z^6) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (compass_le G k hs hC) (by positivity))
        (count_le hs) (count_pos (half_pos hm)).le (by positivity)
    _ = ((k.factorial : ℝ)⁻¹ * compassCoeff G k * countCoeff) *
        (1+C)^2 * Z^(2*k+6) := by rw [pow_add]; ring
    _ ≤ coefficient G k * (1+C)^2 * Z^(2*k+6) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      unfold coefficient
      linarith

/-- The same original Run and genuine one-bond field, with a coefficient
chosen before the Run and every cutoff, period and retained level. -/
theorem atRun {G : Gauge} (k : ℕ) (R : PhysicalNext.Repeat.Legato.Run G)
    (hG : G.Simple) (N period m : ℕ) (hm : m ≤ N) :
    ‖jet (fun A : fieldDir G (R.family.side m period) 1 =>
          mainTerm (R.family.path.levels.params m).clip
            (R.family.path.rep N period m).path (represent A)) k
        (NativeNormalizedBondTest.actualField R hG m period) -
      jet (fun A : fieldDir G (R.family.side m period) 1 =>
          mainTerm (R.family.path.levels.params m).clip
            (R.family.path.rep N period m).path (represent A)) k 0‖ ≤
      coefficient G k * (1+(R.family.path.levels.params m).paths)^2 *
        (1+(R.family.path.levels.params m).width⁻¹)^(2*k+6) := by
  have hc : R.family.path.Conv N period m := R.makes.wilson.represents N period m hm
  have hp : (R.family.path.rep N period m).path.Bounds
      (R.family.path.levels.params m).clip (R.family.path.levels.params m).width
      (R.family.path.levels.params m).paths (R.family.path.levels.clock.loopCap m) := by
    rw [← hc.clip]
    exact hc.good.paths
  exact (NativeOriginalMainBondJets.atRun R hG k N period m hm).trans
    (price_le G k (Extra.Iteration.Cost.nonneg hp.three) hp.width)

end YM.Integration.NativeOriginalMainBondPrice
end
