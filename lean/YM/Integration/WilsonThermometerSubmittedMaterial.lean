import YM.Integration.WilsonThermometerProgramSubmittedWords
import YM.Integration.WilsonPositionProgramPortfolio
import YM.QuadraticLocal.Fk.Offer
import YM.Next.MULTISOURCE.First

/-! The actual thermometer on one independent block, with one vacancy shared by
every separately filed whole word. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerSubmittedMaterial
open Function Filter Finset MeasureTheory Precision PhysicalNext.Repeat.Legato Lattice Wilson Exterior Tree Pressure RG Source Labels Marker Multi
open Next.SectorChange PertExtension.Series Comparison.RG02 Comparison.RG02.Cumulants
open Further.PhysicalPeriodLimitF933 FVA1Physical.TwoReset
open RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Kick AllOrder AllOrder.Floe QuadraticLocal QuadraticLocal.Earn
open WilsonThermometerProgramSubmittedWords
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} (R : Run G) {V T : Type} [Fintype V] [LinearOrder V] (d : V → ℕ)
    {n f : Side} (o : V → Site n) (h : n.val ∣ f.val) (s : (Stock.census V).Mode)
    (g τ : ℝ) (v : (j : V) → R.family.label (d j)) (t : V → T → ℂ) (x : T)
    (L : Layout G) (pay : Finset Age)
local notation "I" => Choice R d n f s.val
local notation "D" => (fun j : ↥s.val => d j.val)
local notation "degree" q => depthF (live R d s.val q) (D) (axis R d s.val q)
local notation "B" q => Boot.scout R (live R d s.val q) (D) (axis R d s.val q) (coords R d o h s.val q)
local notation "weight" q => (∏ j : ↥s.val, dose R d g τ v t x j.val (q j).2)
local notation "W" => WilsonThermometerNumericalBank.bank R d o g τ v t h x L pay
local notation "J" => Stock.census Unit
local notation "base" q => Bare.Signals.flare (J) (fun _ (_ : ℝ) (U : Config G f) =>
  ((B q).Vt f U : ℂ)) (fun _ => degree q)

def catalog (q : I) : Bulk.Colors (Stock.census Unit) G f := QuadraticLocal.Fk.grant L pay (base q)

private theorem qualified (book : Legal pay L) (q : I) :
    Bulk.Well (catalog R d o h s L pay q) := by
  apply (QuadraticLocal.Fk.well L pay book (base q) _).1
  apply Bare.Signals.flare_well
  · exact fun _ => (B q).prepared f
  · exact fun _ _ => RG.Envelope.compactC (Complex.continuous_ofReal.comp ((B q).payment f))
  · exact fun _ _ k U => congrArg (fun z:ℝ => (z:ℂ)) ((B q).rooted f k U)

private lemma ordinary (q : I) (U : Config G f) (u : ℝ) :
    (Poly.pass (Integral.markedLog u U (catalog R d o h s L pay q))).part ((J).fire ()) =
      ((u:ℂ) ^ (degree q))⁻¹ * ((B q).Vt f U : ℂ) := by
  change (Poly.pass (Integral.markedLog u U (base q))).part _ = _
  rw [Bare.Signals.singleton]
  rw [Multi.first_pass () _ (Multi.lambda_quiet _),Multi.lambda_part]
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow]

variable {c : Side} {S : StepData c f} {p : Clip} {P : PathData G} {O : ChartRatio G}
    (K : Bulk.Kernel S p P O) (F : Forest S.ratio) (tag : S.Choices)
    (A : fieldDir G c 1) (c₀ : ℝ)

/-- Every proper and full mode retains its independently situated submitted words on
the same finite Wick drink. The identity holds on the entire held-field space. -/
theorem registered (D₀ : BudgetPoint) (k : ℕ) (legal : Legal pay L) (σ : ℝ)
    (positive : ∀ j, 0 < d j) (w : V → ℝ) {rent : ℝ} {order slots shelf : ℕ}
    (fleet : Scene.Armada (WilsonOriginalStarGradedScene.words R d o σ g τ v t positive)
      w d σ rent order slots shelf) (rate : 0<σ) :
    ∀ e≤k, Laplace.detail (Order.ratio (Bulk.Fk K F tag (W) A k)) s e =
    ∑ q : I, (weight q) * Laplace.detail (Order.ratio (Bulk.Fk K F tag
      (catalog R d o h s L pay q) A k)) ((J).fire ()) e := by
  let M := WilsonOriginalStarGradedScene.words R d o σ g τ v t positive
  have staff := Air.license M (fun j=>(M j).paint x) d w fleet rate (fun j=>fleet.honor j x)
  have hired := (copy_standard h M d (fun j=>(M j).paint x) L pay staff legal).1
  apply WilsonPositionProgramPortfolio.normalized K F tag (W) (catalog R d o h s L pay)
    s ((J).fire ()) (fun q => weight q) A 0 D₀ k
  · rw [← WilsonThermometerNumericalBank.same R d o σ g τ v t positive h x L pay]
    exact hired
  · exact qualified R d o h s L pay legal
  · intro q u U
    simp only [Integral.model, Poly.part_smul, Integral.markedLog,
      Poly.pass_part _ (Multi.part_lit_quiet _)]
    rfl
  · intro u hu U
    simp only [Integral.model, Poly.part_smul,
      WilsonThermometerProgramSubmittedWords.submitted R d o g τ v t h x u U L pay s hu.ne',
      ordinary R d o h s L pay, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by
      change _ * ((weight q) * _) = (weight q) * (_ * _)
      rw [mul_left_comm]
      rfl

end YM.Integration.WilsonThermometerSubmittedMaterial
