import YM.Integration.WilsonReportDetectorMesh
import YM.Pier.Scene.Enamel

/-! Numerical size and true separation of the original finite signed
report windows at the chosen mesh. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportColumnSuppression
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Extraction Table Cells
open Next.Rank OPE OPE.Strobe OPE.Strobe.Panoramic RG12 RG17 RG17.Panoramic
open Push.GridApprox PhysicalNext.Repeat.Legato
open scoped Topology Classical BigOperators
variable {G : Gauge} {R : Run G}

private theorem powers {b D : ℝ} (p q : ℕ) (bpos : 0 < b)
    (hl : (p+(q+1):ℕ) ≤ Real.log b) (hD : (Real.log b)^2 ≤ D) :
    Real.exp (-2*D)*b^p ≤ 1/b^(q+1) := by
  have hn := Nat.cast_nonneg (α:=ℝ) (p+(q+1))
  have hb := hn.trans hl
  have sale := mul_le_mul_of_nonneg_right hl hb
  apply (le_div_iff₀ (pow_pos bpos _)).mpr
  calc
    Real.exp (-2*D)*b^p*b^(q+1) = Real.exp (-2*D)*b^(p+(q+1)) := by rw [pow_add]; ring
    _ = Real.exp (-2*D+((p+(q+1):ℕ):ℝ)*Real.log b) := by
      rw [Real.exp_add,←Real.log_pow,Real.exp_log (pow_pos bpos _)]
    _ ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [sale,hD,sq_nonneg (Real.log b)])

theorem price (hG : G.Simple) (pace : WilsonWindowReportingPace.Slow R.kit) {B : ℕ} (hB : 0<B)
    (g : ℝ→ℝ) (hg : Trace.Pilot.Coupling G g) (p q : ℕ) {c ε : ℝ} (hc : 0<c) (he : 0<ε)
    {m : ℝ→ℕ} (land : Tendsto m RG17.home atTop) (placed : m=WilsonMeasuredWindow.stop R.family.path.levels hG B) :
    ∀ᶠ r in RG17.home,∀ k : ℕ,m r ≤ k →
      c*(Real.exp (-2*((R.family.path.levels.budget k).B:ℝ))*R.family.path.levels.clock.hatBeta k^p) ≤ ε*(g r)^q := by
  have money := WilsonReportDetectorMesh.small hG pace hB g hg q hc he
  dsimp only at money
  rw [←placed] at money
  have log := (Real.tendsto_log_atTop.comp (Station.hat_rate R.family.path.levels hG)).comp land
  filter_upwards [money,log.eventually_ge_atTop ((p+(q+1):ℕ):ℝ)] with r bill hot k deep
  let β := R.family.path.levels.clock.hatBeta
  let D := ((R.family.path.levels.budget k).B:ℝ)
  have low : 0 < β (m r) := (R.family.path.levels.fits.delayed (m r)).trans' zero_lt_one
  have mono : Monotone β := WilsonStartup.Timing.hat_mono R.family.path.levels (Gauge.slopeConstant_pos hG).le
  have upper := mono deep
  have ht : ((p+(q+1):ℕ):ℝ) ≤ Real.log (β k) :=
    hot.trans (Real.log_le_log low upper)
  calc
    _ ≤ c*(1/(β k)^(q+1)) := mul_le_mul_of_nonneg_left
      (powers p q (low.trans_le upper) ht (Nat.le_ceil _)) hc.le
    _ ≤ c/(β (m r))^(q+1) := by
      rw [mul_one_div]
      exact div_le_div_of_nonneg_left hc.le (pow_pos low _) (pow_le_pow_left₀ low.le upper _)
    _ ≤ _ := bill

/-- Two radius-B original windows are strictly smaller than the separation
B^8 supplied by the common reporting mesh. The grade extent is fixed before k. -/
theorem width (hG : G.Simple) (d : ℕ) : ∀ᶠ k : ℕ in atTop,
    2*omen R.family d k (R.family.path.levels.budget k).B < (R.family.path.levels.budget k).B^8 := by
  let e := Extra.Multi.BasisCost.extent (R.family.localSection d)
  have hot := Real.tendsto_log_atTop.comp (Station.hat_rate R.family.path.levels hG)
  filter_upwards [hot.eventually_ge_atTop ((max 16 e:ℕ):ℝ)] with k high
  let b := (R.family.path.levels.budget k).B
  let l := Real.log (R.family.path.levels.clock.hatBeta k)
  have price : l^2 ≤ (b:ℝ) := Nat.le_ceil _
  have h1 : (16:ℝ) ≤ l := (show (16:ℝ) ≤ ((max 16 e:ℕ):ℝ) by exact_mod_cast le_max_left 16 e).trans high
  have h2 : (e:ℝ) ≤ l := (show (e:ℝ) ≤ ((max 16 e:ℕ):ℝ) by exact_mod_cast le_max_right 16 e).trans high
  have L := mul_le_mul_of_nonneg_right h1 (by linarith only [h1] : 0 ≤ l)
  have hb : 16 ≤ b := by exact_mod_cast (show (16:ℝ) ≤ b by nlinarith only [h1,price,L])
  have fee : e ≤ b := by exact_mod_cast (show (e:ℝ) ≤ b by nlinarith only [h1,h2,price,L])
  have b2 := Nat.mul_le_mul_right b hb
  have b3 := Nat.mul_le_mul_right (b*b) hb
  change 2*(e+(b*(4*b+2)+2*b+8)) < b^8
  have third : 2*(e+(b*(4*b+2)+2*b+8)) < b^3 := by nlinarith only [hb,fee,b2,b3]
  exact third.trans_le (Nat.pow_le_pow_right (by omega) (by decide))

theorem separate {m k t o p : ℕ} {r : ℝ} (hr : 0<r) (ht : 1 ≤ t)
    {X : Points 2} (hX : AtShore t X) (E : EnvelopeRange R m k t o r)
    (x : Fin 2→Site (R.family.side k p)) (near : Neighbor R X r (r/(t:ℝ)/4) x) (d : ℕ)
    (paid : 2*omen R.family d k (R.family.path.levels.budget k).B < (R.family.path.levels.budget k).B^8) :
    let a := omen R.family d k (R.family.path.levels.budget k).B
    Disjoint (window (x 0) a) (window (x 1) a) := by
  have wide := (fitsSnap R ht hX hr E x near).2.1 0 1 (by decide)
  have apart := paid.trans_le (E.extra.trans wide)
  apply Set.disjoint_left.mpr
  intro y left right
  have h := separation_triangle (x 0) y (x 1)
  rw [separation_comm y (x 1)] at h
  exact (not_le_of_gt apart) (h.trans ((Nat.add_le_add (sparrow.mp left) (sparrow.mp right)).trans_eq (by omega)))

end YM.Integration.WilsonReportColumnSuppression
end

