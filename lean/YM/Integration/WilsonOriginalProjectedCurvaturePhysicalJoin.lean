import YM.Integration.WilsonOriginalProjectedCurvatureIntake
import YM.Integration.WilsonOriginalEarnedGalleryJoin

/-! The original independent Q-cohort on the actual earlier full signed gallery.
Every rejected new row has its original mask and every old compatible hard
factor remains in its original density. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalProjectedCurvaturePhysicalJoin
open Function Finset Lattice Wilson RG Source Labels Marker Ac
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Comparison.Density.RenderM MergeProof.Accent FVA1
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureCredits
open WilsonOriginalProjectedCurvaturePassport WilsonOriginalProjectedCurvatureEnvelope WilsonOriginalProjectedCurvatureSalary
open Extra.Trajectories QuadraticLocal
open scoped Classical BigOperators
variable {G : Gauge} {B : MS.Local.Physical.Deck G} {J : Type}
  {V : Type} [DecidableEq V] [Fintype V] {R : Run G} {p L n : ℕ} {hn : n ≤ L}
  (Q : MS.Land.Prescription B) (D : ActualRunQlocalNativeTuple.Datum R p L n hn V)
  (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ) (N : ℕ)
  (σ : ℝ) (extra : V → ℕ)
local notation "Y" => R.family.path.rep N p L
local notation "g₀" => Pert.Asymptotics.regulatorRun R.family N p L
local notation "X" => WilsonOriginalProjectedCurvatureLamps.cohort Q D u μ orders N σ extra
local notation "S" => QuadraticLocal.Earn.rendered X (Y).p g₀
local notation "Γ" => Stock.census V

local notation "q₀" x:max U:max => Mach (Γ) (fun i =>
  ActualRunQlocalNativeTuple.reader D i (testInclusion (ActualRunQlocalNativeTuple.orbit D) x i) *
  ActualOriginalCalibratedColumns.weightedObservable R B Q (u i) μ
    (R.family.side L p) (ActualRunQlocalNativeTuple.root D i) U (orders i))
local notation "excluded" => WilsonOriginalProjectedCurvatureIntake.missed Q D u μ orders N σ extra
local notation "new" => WilsonOriginalProjectedCurvatureIntake.picture Q D u μ orders N σ extra
theorem field (prior : QuadraticLocal.Gallery (tastes D) J (WilsonOriginalProjectedCurvaturePassport.paper D u).origin
      (R.family.path.rep N p L) (Stock.census V))
    {w:V→ℝ} {C t:ℝ} {d:ℕ} (paid:prior.E.Paid w d t C)
    (positive:0≤t) (prices:∀ i,0<w i) (hL:L≤N) (x:tastes D) (U:Config G (R.family.side L p)) :
    (new prior).density x U = prior.density x U * Poly.pass (q₀ x U - excluded x U) := by
  have combine := WilsonOriginalEarnedGalleryJoin.field prior (S) paid positive prices x U
  have low := WilsonOriginalProjectedCurvatureIntake.masked_sum Q D u μ orders N σ extra x U hL
  exact combine.trans (congrArg (fun z : Poly (Γ) => prior.density x U * Poly.pass z)
    (eq_sub_iff_add_eq.mpr low))

theorem accepted (prior : QuadraticLocal.Gallery (tastes D) J (WilsonOriginalProjectedCurvaturePassport.paper D u).origin
      (R.family.path.rep N p L) (Stock.census V))
    {w:V→ℝ} {C t:ℝ} {d:ℕ} (paid:prior.E.Paid w d t C)
    (positive:0≤t) (prices:∀ i,0<w i) (hL:L≤N) (x:tastes D) (U:Config G (R.family.side L p))
    (h:∀i, (S).clear i ∨ Healthy (Y).p.threshold ((S).ground i) U) :
    (new prior).density x U = prior.density x U * Poly.pass (q₀ x U) := by
  have same := field Q D u μ orders N σ extra prior paid positive prices hL x U
  rw [WilsonOriginalProjectedCurvatureIntake.clear Q D u μ orders N σ extra x U h,sub_zero] at same
  exact same

end YM.Integration.WilsonOriginalProjectedCurvaturePhysicalJoin
