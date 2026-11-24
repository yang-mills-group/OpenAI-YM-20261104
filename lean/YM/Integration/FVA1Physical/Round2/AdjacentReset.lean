import YM.Integration.FVA1Physical.Round2.WilsonPolynomial

/-! Identify the field/coupling substitution used for polynomial Wilson
banks with the RG02 adjacent-coupling prescription on precisely the same
germ. Here the coupling germ itself is supplied with its own finite jet. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2
open Function Filter Finset Lattice RG MSbar MSbar.Rolling MSbar.Bakery MSbar.Cacao MSbar.Wave
open MSbar.Bakery.Portal Comparison.RG02 PertExtension.Series PertExtension.Series.Tested
open scoped BigOperators Classical ContDiff Topology
variable {σ : Type} [Fintype σ]

def transportedRead (H : ℝ → ℝ) (V : PowerSeries (Pot σ)) (r : ℕ) (x : View σ) (t : ℝ) : ℝ :=
  taste r (picture (H t • x) V) (t/H t)

theorem transportedRead_smooth {H : ℝ → ℝ} (V : PowerSeries (Pot σ)) (r : ℕ) (x : View σ)
    (hs : ContDiffAt ℝ ω H 0) (h₀ : H 0 ≠ 0) : ContDiffAt ℝ ω (transportedRead H V r x) 0 := by
  unfold transportedRead taste picture
  simp only [PowerSeries.coeff_map]
  exact ContDiffAt.sum fun i _ => ((contDiffAt_id.div hs h₀).pow i).mul
    ((Cacao.vent _).contDiffAt.comp 0 (hs.smul contDiffAt_const))

theorem ticket_bill {H : ℝ → ℝ} {b : PowerSeries ℝ} (V : PowerSeries (Pot σ)) (r : ℕ)
    (h₀ : H 0 = 1) (hb : PowerSeries.coeff 0 b = 1) (hs : ContDiffAt ℝ ω H 0)
    (hH : Approx H b r) (degree : Expanse V 1 r) (x : View σ) {i : ℕ} (hi : i ≤ r) :
    bill (transportedRead H V r x) i = MvPolynomial.eval x (PowerSeries.coeff i (ticket b V)) := by
  let f := transportedRead H V r x
  have sm := transportedRead_smooth V r x hs (h₀.trans_ne one_ne_zero)
  have paid : Grade (fun t => f t - taste r (picture x (ticket b V)) t) (r+1) :=
    decks V r hb degree (fun _ (_ : Unit) => x) (Price.fromConst x) hH
  apply sub_eq_zero.mp
  apply magnitude (n := r) (f := fun j => bill f j - MvPolynomial.eval x (PowerSeries.coeff j (ticket b V))) _ i hi
  apply (Price.cut paid (certified sm r)).egress
  filter_upwards with t _ _
  unfold taste picture
  simp only [PowerSeries.coeff_map, mul_sub, sum_sub_distrib]
  dsimp only [f]
  ring

/-- RG02 takes the old coupling per new coupling and scales its field by
that ratio's inverse. `H` is the reciprocal ratio in the scene convention. -/
def sceneGerm (H : ℝ → ℝ) (hs : ContDiffAt ℝ ω H 0) (h₀ : H 0 = 1) : Adjacent.UnitCost where
  rating t := (H t)⁻¹
  smooth := hs.inv (h₀.trans_ne one_ne_zero)
  origin := by simp [h₀]

def displayed (V : PowerSeries (Pot σ)) : Adjacent.Display (View σ) := fun i x =>
  (MvPolynomial.eval x (PowerSeries.coeff i V) : ℝ)

theorem ticket_adjacent {H : ℝ → ℝ} {b : PowerSeries ℝ} (V : PowerSeries (Pot σ)) (r : ℕ)
    (h₀ : H 0 = 1) (hb : PowerSeries.coeff 0 b = 1) (hs : ContDiffAt ℝ ω H 0)
    (hH : Approx H b r) (degree : Expanse V 1 r) (x : View σ) {i : ℕ} (hi : i ≤ r) :
    Adjacent.born (displayed V) (sceneGerm H hs h₀) 0 r i x = displayed (ticket b V) i x := by
  have eqn : (fun t => Adjacent.ages (displayed V) 0 r t ((sceneGerm H hs h₀).rating t) x) =
      Complex.ofRealCLM ∘ transportedRead H V r x := by
    funext t
    simp [Adjacent.ages,Adjacent.cover,sceneGerm,displayed,transportedRead,taste,picture,div_eq_mul_inv]
  unfold Adjacent.born
  rw [eqn,Moving.Path.motion,← Assembly.jet_apply_left Complex.ofRealCLM _ i
    ((transportedRead_smooth V r x hs (h₀.trans_ne one_ne_zero)).of_le le_top) 1]
  have paid := ticket_bill V r h₀ hb hs hH degree x hi
  exact congrArg Complex.ofReal paid
end YM.Integration.FVA1Physical.Round2
