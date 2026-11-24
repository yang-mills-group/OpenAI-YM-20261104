import YM.Integration.WilsonRootedTwoDateCoolingRows
import YM.Integration.WilsonRootedTwoDateThermal

/-! The whole higher dated signed normalized OPE is kept while the new source's actual local masks are imposed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedTwoDateProduct
open Filter Function Finset MeasureTheory Lattice Wilson RG Marker Precision OPE.Therm
open PhysicalNext.Repeat.Legato LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open MergeProof MergeProof.Accent ActualPolynomialContraction ManuscriptQLocalMeasuredMarkDifference
open WilsonLimitConstruction Push.AbsoluteSums.Animals RG.Shoot Pert.Asymptotics
open private rent from YM.Integration.WilsonPhysicalHistoryKioskHeatOrder
open scoped Classical Topology BigOperators
universe u
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
    {B : MS.Local.Physical.Deck G} {R : Run G} {N p m : ℕ}
local notation "w₁" => fun _ : V => (1:ℝ)
variable (old : Seed R B V N p (m+1)) (fresh : Seed R B V N p m) (hG : G.Simple)

/-- This signed defect is the full difference of the two genuinely interacting normalized fields at the lower date. -/
def defect (U : Config G (R.family.side (m+1) p)) := old.response hG (Nat.le_succ (m+1)) U *
  (fresh.response hG (le_refl (m+1)) U - fresh.masked hG U)

theorem exact_defect (U : Config G (R.family.side (m+1) p)) :
    integrand old fresh hG U-old.response hG (Nat.le_succ (m+1)) U*fresh.masked hG U = defect old fresh hG U :=
  (mul_sub _ _ _).symm

omit [Nonempty V] in
private theorem subtract (x y : Poly (Stock.census V)) : Poly.price (w₁) (x-y) ≤ Poly.price (w₁) x+Poly.price (w₁) y := by
  simpa only [sub_eq_add_neg,←neg_one_smul ℂ y,Poly.adapted,norm_neg,norm_one,one_mul] using Poly.addition (fun _=>zero_lt_one) x (-y)

theorem priced (ho : old.visible) (hf : fresh.visible) :
    let μ := scene R.family.path N p (m+1)
    let K := old.cost*|expMod (Fintype.card V) fresh.rowBound|
    Integrable (fun U=>Poly.price (w₁) (defect old fresh hG U)) μ ∧
      ∫ U,Poly.price (w₁) (defect old fresh hG U) ∂μ ≤ K*(∫ U,Poly.price (w₁) (fresh.whole hG U-fresh.clipped hG U) ∂μ) := by
  let μ := scene R.family.path N p (m+1)
  letI : IsProbabilityMeasure μ := probability (H:=R.family.path) (p:=p) R.makes.wilson fresh.below
  let K := old.cost*|expMod (Fintype.card V) fresh.rowBound|
  have L : 0≤old.cost := (Poly.nonnegative (fun _=>zero_lt_one) _).trans
    (old.point hG ho (w₁) (fun _=>zero_lt_one) (fun _=>le_refl 1) (Nat.le_succ (m+1)) (1 : Config G _))
  have point (U : Config G (R.family.side (m+1) p)) : Poly.price (w₁) (defect old fresh hG U) ≤
      K*Poly.price (w₁) (fresh.whole hG U-fresh.clipped hG U) := by
    have first := old.point hG ho (w₁) (fun _=>zero_lt_one) (fun _=>le_refl 1) (Nat.le_succ (m+1)) U
    have later := fresh.row_price hG hf U
    exact (Poly.multiplication (fun _=>zero_lt_one) ..).trans <|
      (mul_le_mul first later (Poly.nonnegative (fun _=>zero_lt_one) _) L).trans_eq (mul_assoc _ _ _).symm
  have raw := fresh.measurable_rows hG
  have loss : Integrable (fun U=>Poly.price (w₁) (fresh.whole hG U-fresh.clipped hG U)) μ := by
    apply Integrable.of_bound ((Poly.price_cont (w₁)).measurable.comp (raw.1.sub raw.2)).aestronglyMeasurable (fresh.rowBound+fresh.rowBound)
    apply ae_of_all
    intro U
    change ‖Poly.price (w₁) (fresh.whole hG U-fresh.clipped hG U)‖ ≤ _
    rw [Real.norm_of_nonneg (Poly.nonnegative (fun _=>zero_lt_one) _)]
    exact (subtract _ _).trans (add_le_add (fresh.rows hG U).1 (fresh.rows hG U).2)
  have major := loss.const_mul K
  have hO := (old.integrable hG ho (Nat.le_succ (m+1))).aestronglyMeasurable
  have hF := (fresh.integrable hG hf (le_refl (m+1))).aestronglyMeasurable
  have hC := (Poly.pass_cont.measurable.comp raw.2).aestronglyMeasurable (μ:=μ)
  have meas : AEStronglyMeasurable (fun U=>Poly.price (w₁) (defect old fresh hG U)) μ :=
    (Poly.price_cont (w₁)).comp_aestronglyMeasurable (hO.mul (hF.sub hC))
  have genuine := major.mono' meas (ae_of_all _ fun U=>by rw [Real.norm_of_nonneg (Poly.nonnegative (fun _=>zero_lt_one) _)];exact point U)
  refine ⟨genuine,(integral_mono genuine major point).trans_eq ?_⟩
  exact integral_const_mul K _

/-- On the one funded campaign the entire signed interacting replacement has every requested
power, before any two independent source data, torus or test are submitted. -/
theorem cooled {ε : ℝ} {T : Campaign R} {W : Campaign.Pillars R T}
    (paid : FundedOriginalProperties.{u} hG ε W) (u v : V→MS.Rake.Label B) (q : ℕ) {δ : ℝ} (pay : 0<δ) :
    ∀ᶠ m:ℕ in atTop, ∀ N p (old : Seed R B V N p (m+1)) (fresh : Seed R B V N p m),old.labels=u → fresh.labels=v →
      Integrable (fun U=>Poly.price (w₁) (defect old fresh hG U)) (scene R.family.path N p (m+1)) ∧
      ∫ U,Poly.price (w₁) (defect old fresh hG U) ∂scene R.family.path N p (m+1) ≤ δ*(regulatorRun R.family N p (m+1))^q := by
  let A := MarkedPackets.uniformModelCost (ActualOriginalQLayout.rankCap R u) (Fintype.card V) 1 *
    |expMod (Fintype.card V) ((Fintype.card V:ℝ)*((2:ℝ)^(ActualOriginalQLayout.rankCap R v)*1))| * rowFee R v
  let D : ℝ := 625*(Fintype.card PlaqAxes:ℝ)
  have axes : 0<Fintype.card PlaqAxes := Fintype.card_pos
  have one : (1:ℝ)≤(Fintype.card PlaqAxes:ℝ) := by exact_mod_cast axes
  have D1 : 1≤D := by dsimp [D];linarith
  have weather : Poetry R.family.path.levels := paid.2.1.paid.stoves
  filter_upwards [integrated_rows hG weather v,(tendsto_add_atTop_nat 1).eventually (rent R hG 0 q (abs_nonneg A) pay),
    eventually_ge_atTop (ActualOriginalQLayout.referenceLevel R u),eventually_ge_atTop (ActualOriginalQLayout.referenceLevel R v)] with m bill hot ou fv N p old fresh ore ore'
  have ho : old.visible := by unfold Seed.visible;rw [ore];omega
  have hf : fresh.visible := by unfold Seed.visible;rw [ore'];omega
  obtain ⟨good,bound⟩ := priced old fresh hG ho hf
  have nO : 0≤old.cost := (Poly.nonnegative (fun _=>zero_lt_one) _).trans
    (old.point hG ho (w₁) (fun _=>zero_lt_one) (fun _=>le_refl 1) (Nat.le_succ (m+1)) (1 : Config G _))
  have κ : 0 ≤ R.family.path.levels.clock.forcedAllowance (m+1) := (Real.exp_pos _).le
  have idA : old.cost*|expMod (Fintype.card V) fresh.rowBound| * rowFee R v=A := by
    unfold Seed.cost Seed.rowBound;rw [ore,ore']
  have last := (hot N fresh.below p)
  simp only [pow_zero,div_one] at last
  refine ⟨good,bound.trans ?_⟩
  refine (mul_le_mul_of_nonneg_left (bill N p fresh ore') (mul_nonneg nO (abs_nonneg _))).trans ?_
  rw [←mul_assoc,idA]
  exact (mul_le_mul_of_nonneg_right ((le_abs_self A).trans (le_mul_of_one_le_right (abs_nonneg A) D1)) κ).trans last

end YM.Integration.WilsonRootedTwoDateProduct
