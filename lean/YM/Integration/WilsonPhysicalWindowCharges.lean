import YM.Integration.WilsonPhysicalWindowDepth

/-! Sum the genuine one-step thermal and Haar posterior tariffs on the
entire physical ultraviolet window, uniformly in period and later cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalWindowCharges

open Filter Real Finset Lattice Wilson RG RG16 RG16.Literal RG16.Guarding Pert.Asymptotics
open PhysicalNext.Repeat.Legato WilsonPhysicalExteriorMeshStops
open scoped Topology BigOperators

variable {G : Gauge}

def bill (C : Family G) (q N n i : ℕ) : ℝ :=
  5*(C.path.levels.clock.hatBeta (i+1))^(-(q:ℝ)/2) + 2*(regulatorRun C N n (i+1))^q

private def coeff (q : ℕ) := 5*exp (q:ℝ) + 3*(2*exp 1)^q

private lemma positive_coeff (q : ℕ) : 0 ≤ coeff q := by unfold coeff; positivity

private lemma heat (C : Family G) (q i : ℕ) :
    (C.path.levels.clock.hatBeta i)^(-(q:ℝ)/2) = exp (q:ℝ)*coin C q i := by
  have ht : 0 < C.path.levels.clock.hatBeta i := zero_lt_one.trans (C.path.levels.fits.delayed i)
  rw [Real.rpow_def_of_pos ht,coin,← Real.exp_add]
  unfold Lambda
  congr 1
  ring

private theorem charges (R : Run G) (hG : G.Simple) (q : ℕ) {N n k i : ℕ}
    (ki : k ≤ i) (iN : i ≤ N) :
    (5*(R.family.path.levels.clock.hatBeta i)^(-(q:ℝ)/2) + 2*(regulatorRun R.family N n i)^q ≤
      coeff q * (regulatorRun R.family N n k)^q) ∧
    (regulatorRun R.family N n i)^q ≤ coeff q * (regulatorRun R.family N n k)^q := by
  let C := R.family
  let g := regulatorRun C N n
  have gk := (buys_at C R.makes (p:=n) (ki.trans iN) (q:ℝ) (by positivity)).1
  have gi := (buys_at C R.makes (p:=n) iN (q:ℝ) (by positivity)).2
  simp only [Real.rpow_natCast] at gk gi
  have base : 1 ≤ exp 1/2 := by linarith only [Real.add_one_le_exp (1:ℝ)]
  have paid : coin C q i ≤ (g k)^q :=
    (coin_down C hG (x:=(q:ℝ)) (by positivity) ki).trans
      ((le_mul_of_one_le_left (coin_pos C q k).le (one_le_pow₀ base)).trans gk)
  have hot : (C.path.levels.clock.hatBeta i)^(-(q:ℝ)/2) ≤ exp (q:ℝ) * (g k)^q :=
    (heat C q i).le.trans (mul_le_mul_of_nonneg_left paid (Real.exp_pos _).le)
  have field : (g i)^q ≤ (2*exp 1)^q * (g k)^q :=
    gi.trans (mul_le_mul_of_nonneg_left paid (by positivity))
  have nonneg : 0 ≤ (g k)^q := pow_nonneg (g_pos R.makes (ki.trans iN)).le _
  have both : 0 ≤ (2*exp 1)^q * (g k)^q := mul_nonneg (by positivity) nonneg
  change _ ≤ coeff q * (g k)^q ∧ (g i)^q ≤ coeff q * (g k)^q
  unfold coeff
  constructor
  · change 5*(C.path.levels.clock.hatBeta i)^(-(q:ℝ)/2) + 2*(g i)^q ≤ _
    linarith only [hot,field,both]
  · have heat0 := mul_nonneg (Real.exp_pos (q:ℝ)).le nonneg
    linarith only [field,both,heat0]

theorem summed (R : Run G) (hG : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit)
    {c : ℝ} (hc : c ≤ 2) (p : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ N n, let u := ultraviolet R.family c k
      u < N → (regulatorRun R.family N n (u+1))^(p+1) +
        ∑ i ∈ Finset.Ico k u, bill R.family (p+1) N n i ≤ ε * (regulatorRun R.family N n k)^p := by
  let u := ultraviolet R.family c
  let L := Lambda R.family.path.levels
  let A := (1+3/log 3) * coeff (p+1)
  have A0 : 0 ≤ A := mul_nonneg (by positivity) (positive_coeff _)
  have reserve := WilsonDyadicReportingPrice.reserve (C:=R.family) hG R.makes A 2 ε A0 hε
  filter_upwards [WilsonPhysicalWindowDepth.counted R hG slow hc,reserve,
    (lambda_leads R.family hG).eventually (eventually_gt_atTop (1:ℝ))] with k room money large
  intro N n
  dsimp only
  intro live
  change u k < N at live
  change k < u k ∧ ((u k-k:ℕ):ℝ) ≤ (3/log 3)*(L k)^2 at room
  let g := regulatorRun R.family N n k
  let price := coeff (p+1) * g^(p+1)
  have pos : 0 ≤ g := (g_pos R.makes (room.1.le.trans live.le)).le
  have hp : 0 ≤ price := mul_nonneg (positive_coeff _) (pow_nonneg pos _)
  have last : (regulatorRun R.family N n (u k+1))^(p+1) ≤ price :=
    (charges R hG (p+1) (n:=n) (k:=k) (i:=u k+1) (by omega) live).2
  have each : ∀ i ∈ Finset.Ico k (u k), bill R.family (p+1) N n i ≤ price := by
    intro i hi
    obtain ⟨low,high⟩ := Finset.mem_Ico.mp hi
    exact (charges R hG (p+1) (n:=n) (k:=k) (i:=i+1) (by omega) (by omega)).1
  have tally : (∑ i ∈ Finset.Ico k (u k), bill R.family (p+1) N n i) ≤
      ((u k-k:ℕ):ℝ)*price := (Finset.sum_le_sum each).trans_eq (by simp)
  have length : 1 + ((u k-k:ℕ):ℝ) ≤ (1+3/log 3)*(L k)^2 := by
    have initial : 1 ≤ (L k)^2 := one_le_pow₀ (le_of_lt large)
    linarith only [room.2,initial]
  have paid : A * (L k)^2 * g ≤ ε := by
    simpa only [Real.rpow_two] using money n N (room.1.le.trans live.le)
  calc
    _ ≤ price + ((u k-k:ℕ):ℝ)*price := add_le_add last tally
    _ = (1+((u k-k:ℕ):ℝ))*price := by ring
    _ ≤ ((1+3/log 3)*(L k)^2)*price := mul_le_mul_of_nonneg_right length hp
    _ = (A*(L k)^2*g)*g^p := by dsimp [price,A]; rw [pow_succ]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right paid (pow_nonneg pos _)

end YM.Integration.WilsonPhysicalWindowCharges

