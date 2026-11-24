import YM.Integration.WilsonRootedTwoDateSource
import YM.Integration.ManuscriptQLocalRawMaskCalendar
import YM.Integration.OriginalMarkedBirthStencil

/-! Source and rooted cost of the complete later row before its physical conditional is taken. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedTwoDateProduct
open Filter Function Finset MeasureTheory Lattice Wilson RG Marker Precision OPE.Therm
open PhysicalNext.Repeat.Legato LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open MergeProof MergeProof.Accent ActualPolynomialContraction ManuscriptQLocalMeasuredMarkDifference
open scoped Classical Topology BigOperators
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
    {B : MS.Local.Physical.Deck G} {R : Run G} {N p m : ℕ}
local notation "w₁" => fun _ : V => (1:ℝ)
local notation "g₀" => Pert.Asymptotics.regulatorRun R.family N p (m+1)
local notation "Y₀" => R.family.path.rep N p (m+1)

namespace Seed
variable (a : Seed R B V N p m) (hG : G.Simple)
local notation "Q₀" => ActualOriginalQInitialInput.packets R hG a.labels a.request a.schedule a.datum a.prescription a.roots a.scale a.degree

def whole (U : Config G (R.family.side (m+1) p)) := (Q₀).read (testInclusion _ a.test) (g₀) U
def clipped (U : Config G (R.family.side (m+1) p)) := ManuscriptQLocalOriginalConditionalTail.source (Q₀) (Y₀).p (g₀) a.test 1 U
def masked (U : Config G (R.family.side (m+1) p)) := Poly.pass (a.clipped hG U)
def rowBound : ℝ := (Fintype.card V:ℝ)*((2:ℝ)^(ActualOriginalQLayout.rankCap R a.labels)*1)

omit [Nonempty V] in
theorem rows (U : Config G (R.family.side (m+1) p)) :
    Poly.price (w₁) (a.whole hG U) ≤ a.rowBound ∧ Poly.price (w₁) (a.clipped hG U) ≤ a.rowBound := by
  have H := OriginalMarkedBirthStencil.paid R hG a.labels a.request a.schedule a.datum a.prescription a.roots a.scale a.degree OriginalMarkedBirthStencil.mesh (g₀)
  exact ⟨(ManuscriptQLocalOriginalFineMaskLoss.original_rows (Q₀) H a.test U).2,
    (ManuscriptQLocalOriginalFineMaskLoss.regular_rows (Q₀) H a.test (Y₀).p U).2⟩

omit [Nonempty V] in
theorem measurable_rows : Measurable (a.whole hG) ∧ Measurable (a.clipped hG) :=
  ⟨ManuscriptQLocalOriginalFineMaskLoss.full_borel (Q₀) a.test,ManuscriptQLocalOriginalFineMaskLoss.mask_borel (Q₀) a.test (Y₀).p⟩

theorem row_price (visible : a.visible) (U : Config G (R.family.side (m+1) p)) :
    Poly.price (w₁) (a.response hG (le_refl (m+1)) U-a.masked hG U) ≤
      |expMod (Fintype.card V) a.rowBound| * Poly.price (w₁) (a.whole hG U-a.clipped hG U) := by
  rw [a.fresh_read hG visible U]
  have bound := a.rows hG U
  exact (passing (fun _=>zero_lt_one) bound.1 bound.2).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Poly.nonnegative (fun _=>zero_lt_one) _))
end Seed

omit [DecidableEq V] [Nonempty V] in
/-- The explicit positive largest local stencil and squared rank cost are independent of the cutoff and the torus. -/
def rowFee (R : Run G) (u : V→MS.Rake.Label B) : ℝ := ((Fintype.card PlaqAxes*4:ℕ):ℝ)*81*
  Real.exp (ActualOriginalQPointCover.bound R u:ℝ)*((Fintype.card V:ℝ)*((2:ℝ)^(ActualOriginalQLayout.rankCap R u)*1))

omit [Nonempty V] in
theorem integrated_rows (hG : G.Simple) (weather : Poetry R.family.path.levels) (u : V→MS.Rake.Label B) :
    ∀ᶠ m:ℕ in atTop,∀ N p (a : Seed R B V N p m),a.labels=u →
      ∫ U,Poly.price (w₁) (a.whole hG U-a.clipped hG U) ∂scene R.family.path N p (m+1) ≤
        rowFee R u*R.family.path.levels.clock.forcedAllowance (m+1) := by
  filter_upwards [(tendsto_add_atTop_nat 1).eventually (ManuscriptQLocalIncidentMasks.hot weather hG R.makes.wilson 1)] with m heat N p a names
  let μ := scene R.family.path a.datum.cutoff a.datum.period (a.datum.level+1)
  letI : IsProbabilityMeasure μ := probability (H:=R.family.path) (p:=a.datum.period) R.makes.wilson a.datum.below
  let q := OriginalMarkedBirthStencil.mesh
  let M := ActualOriginalQInitialInput.packets R hG a.labels a.request a.schedule a.datum a.prescription a.roots a.scale a.degree
  have H := OriginalMarkedBirthStencil.paid R hG a.labels a.request a.schedule a.datum a.prescription a.roots a.scale a.degree q (Pert.Asymptotics.regulatorRun R.family N p (m+1))
  have cover : Real.exp (q.supportExponent*(ActualOriginalQPackets.packetCover a.prescription
      (ActualOriginalQPointSetup.pointDatum R a.request p (m+1) a.roots) a.labels (a.scale-R.family.S.scale N) a.degree N q:ℝ)) ≤
      Real.exp (ActualOriginalQPointCover.bound R a.labels:ℝ) := by
    apply Real.exp_le_exp.mpr
    rw [show q.supportExponent=1 from rfl,one_mul]
    change (↑(ActualOriginalQPackets.packetCover a.prescription (ActualOriginalQPointSetup.pointDatum R a.request a.datum.period (a.datum.level+1) a.roots) a.labels (a.scale-R.family.S.scale a.datum.cutoff) a.degree a.datum.cutoff q):ℝ) ≤ (ActualOriginalQPointCover.bound R a.labels:ℝ)
    exact
      (Nat.cast_le.mpr (OriginalMarkedBirthStencil.covered R a.labels a.request a.datum a.prescription a.roots a.scale a.degree q) : (_:ℝ)≤_)
  have hκ : 0 ≤ R.family.path.levels.clock.forcedAllowance (m+1) := (Real.exp_pos _).le
  have cap := ManuscriptQLocalOriginalFineMaskLoss.integrated (n:=R.family.side (a.datum.level+1) a.datum.period) M H a.test μ (R.family.path.rep a.datum.cutoff a.datum.period (a.datum.level+1)).p (pow_nonneg hκ 1) cover
    (fun _=>heat N a.below p _)
  simp only [pow_one] at cap
  rw [←names]
  apply cap.trans
  unfold rowFee ManuscriptQLocalOriginalFineMaskLoss.bound
  have rank : M.rankCap=ActualOriginalQLayout.rankCap R a.labels := rfl
  rw [rank]
  rw [show q.B=1 from rfl,show q.supportExponent=1 from rfl]
  apply le_of_eq
  norm_num only [Nat.cast_one,div_one]
  ring

end YM.Integration.WilsonRootedTwoDateProduct
