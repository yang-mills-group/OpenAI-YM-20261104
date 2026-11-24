import YM.Integration.WilsonOriginalProjectedCurvaturePhysicalJoin

/-! Restore exactly the true excluded new masks in the complete signed finite
density. The original field, old marked gas, and all sites are kept fixed. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalProjectedCurvatureMaskCompletion
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
theorem original (prior : QuadraticLocal.Gallery (tastes D) J (WilsonOriginalProjectedCurvaturePassport.paper D u).origin
      (R.family.path.rep N p L) (Stock.census V))
    {w:V→ℝ} {C t:ℝ} {d:ℕ} (paid:prior.E.Paid w d t C)
    (positive:0≤t) (prices:∀ i,0<w i) (hL:L≤N) (x:tastes D) (U:Config G (R.family.side L p)) :
    (new prior).density x U * Poly.pass (excluded x U) = prior.density x U * Poly.pass (q₀ x U) := by
  have low := WilsonOriginalProjectedCurvatureIntake.masked_sum Q D u μ orders N σ extra x U hL
  have quiet := (S).quiet_of_hasSum x U (hasSum_fintype _).summable
  have q := congrArg (fun z : Poly (Γ) => z.part (Γ).quiet) low
  change ((S).log x U + excluded x U).part (Γ).quiet = (q₀ x U).part (Γ).quiet at q
  have miss : (excluded x U).part (Γ).quiet=0 := by
    rw [Poly.part_plus,quiet,zero_add,mute] at q
    exact q
  have stay := WilsonOriginalEarnedGalleryJoin.field prior (S) paid positive prices x U
  calc
    _ = (prior.density x U * Poly.pass ((S).log x U)) * Poly.pass (excluded x U) :=
      congrArg (fun z : Poly (Γ) => z * Poly.pass (excluded x U)) stay
    _ = prior.density x U * (Poly.pass ((S).log x U) * Poly.pass (excluded x U)) := mul_assoc _ _ _
    _ = prior.density x U * Poly.pass ((S).log x U + excluded x U) :=
      congrArg (fun z : Poly (Γ) => prior.density x U*z) (Next.Rank.Exponential.pass_add _ _ quiet miss).symm
    _ = _ := congrArg (fun z : Poly (Γ) => prior.density x U*Poly.pass z) low
end YM.Integration.WilsonOriginalProjectedCurvatureMaskCompletion
