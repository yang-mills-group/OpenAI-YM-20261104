import YM.Integration.WilsonLimitConstruction.FundedSpringFineInlet
import YM.Integration.RunFundedPeriodAction
import YM.Integration.SelectedPlanClearedNumerator
import YM.Integration.FullQLocalNumericStepData
import YM.WilsonCoeffUV.Kinetic.Alpha

/-! A genuine two-stage vacuum Plan whose fine list is the very list of
the actual input and whose coarse list is the native paid signed period
source.  Its finite beta polynomial is cut directly from the same original
physical clock. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedSpringPeriodPlan
open Function Filter Lattice Laurent Bloch Wilson RG Precision Exterior Tree Matrix PowerSeries Marker
open IterationFour IterationFour.Vacuum Comparison.RG02 Comparison.RG02.Assembly
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open WilsonCoeffUV.Bank.Mosaic FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open scoped Topology ContDiff BigOperators Classical
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V}
variable (R : Run G) {J : Request V} {A : NumericSchedule R.family J}
variable {d : LocalFormal.Datum R.family Γ} (F : FundedSpringFineInlet.Inlet J A d)
variable (Z : SeriesA G) (σ C : ℝ)
local notation "n" => R.family.side d.level d.period
local notation "B₀" => A.outputNorm d.level
local notation "L₀" => R.family.path.levels
local notation "P₀" => R.alloy.B.kin

def rows (i : ℕ) : List (Piece G (R.family.side i d.period)) :=
  if hi : i=d.level then hi.symm ▸ Z.map (FundedCorrectedPeriod.piece (n) (B₀) σ C)
  else if hf : i=d.level+1 then hf.symm ▸ F.layers
  else []

omit [Fintype V] in
private theorem current : rows R F Z σ C d.level=Z.map (FundedCorrectedPeriod.piece (n) (B₀) σ C) := by
  unfold rows
  split
  · rfl
  · rename_i h
    exact (h rfl).elim

omit [Fintype V] in
private theorem next_level : rows R F Z σ C (d.level+1)=F.layers := by
  unfold rows
  split
  · rename_i h
    omega
  · split
    · rfl
    · rename_i h
      exact (h rfl).elim

variable (D : RunFundedPeriodAction.PeriodData Z J.order σ C)

/-- The true coarse/fine lists, the native inverse-temperature coefficients,
and the same alpha purchased on this Run. -/
def plan (D : RunFundedPeriodAction.PeriodData Z J.order σ C) : Plan R.family d.cutoff d.period J.order where
  layers := rows R F Z σ C
  orders i _ := by
    by_cases hi : i=d.level
    · subst i
      rw [current]; exact D.grades (n) (B₀)
    by_cases hf : i=d.level+1
    · subst i
      rw [next_level]; exact F.orders
    · simp [rows,hi,hf,Render.gradings]
  coefficient i k := coeff (k+2) (pitch (L₀) R.metals.O d.cutoff i)
  alpha i := (P₀).alpha d.cutoff i

omit [Fintype V]

theorem fine : (plan R F Z σ C D).layers (d.level+1)=F.layers := next_level R F Z σ C
theorem coarse :
    (plan R F Z σ C D).layers d.level=Z.map (FundedCorrectedPeriod.piece (n) (B₀) σ C) :=
  current R F Z σ C

theorem constant (hG : G.Simple) :
    (plan R F Z σ C D).coefficient d.level 0=(plan R F Z σ C D).alpha d.level :=
  (alpha_stable hG R.alloy.B.ratio R.alloy.B.support d.below.le).2 d.below

/-- Retains the genuine geometrical output norm. The posted width sees the
actual nonzero catalogue. -/
theorem permits (h : 20<(n).val) (hs : (B₀).supportExponent/(B₀).B≤σ/4)
    (hc : 2≤(B₀).B) (Y : Activities G (n)) (hy : ∀s x,Y.Moves s x) :
    Render.permits ((plan R F Z σ C D).layers d.level) (B₀) := by
  rw [coarse]
  exact D.paid (n) h (B₀) hs hc Y hy

/-- At every field, the analytic vacuum numerator of this *same actual Plan*
contains the complete native finite period source with precisely its true
coarse coupling and inverse-temperature scaling. -/
theorem numerator (z : ℝ × fieldDir G (n) 1) :
    let P := plan R F Z σ C D
    let a := ActualAnalyticPlanVacuum.radicand R P d.level z.1
    let g := ActualAnalyticPlanVacuum.coupling R P d.level z.1
    let U := represent z.2
    let K := (R.family.path.rep d.cutoff d.period d.level).path
    SelectedPlanClearedNumerator.numerator R P d.level z =
      ((a * mainTerm ((L₀).params d.level).clip K U +
        z.1^2 * Precision.loop K U + a*FundedPeriodAction.rendered (n) Z g U : ℝ):ℂ) := by
  dsimp only
  unfold SelectedPlanClearedNumerator.numerator ActualAnalyticPlanVacuum.vacuum
  rw [coarse,D.restored]
  unfold ActualAnalyticPlanVacuum.kinetic ActualAnalyticPlanVacuum.radicand
  congr 1
  ring

end YM.Integration.WilsonLimitConstruction.FundedSpringPeriodPlan
