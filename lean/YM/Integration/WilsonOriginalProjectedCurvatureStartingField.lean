import YM.Integration.WilsonOriginalScalarGallery
import YM.Integration.WilsonOriginalProjectedCurvatureMaskCompletion
import YM.Integration.ActualOriginalQInput

/-! Initial enrollment of the actual independently booked finite Q on the
original interacting vacuum, including its full original forced gas. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalProjectedCurvatureStartingField
open Function Finset Lattice Wilson RG Source Labels Marker Ac
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Comparison.Density.RenderM MergeProof.Accent FVA1
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureCredits
open WilsonOriginalProjectedCurvaturePassport WilsonOriginalProjectedCurvatureEnvelope WilsonOriginalProjectedCurvatureSalary
open MergeProof MergeProof.Replicums
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

theorem lease (hL:L≤N) : Hard.Rent (Y).activities.forced (Y).activities.K (Y).p (Y).p.supportExponent
    (R.family.path.levels.clock.forcedAllowance L) :=
  Hard.rentValid (R.makes.wilson.represents N p L hL).good.labels.forced
    (R.makes.wilson.represents N p L hL).good.labels.boundK

local notation "previous" hL:max => WilsonOriginalScalarGallery.before («X»:=tastes D)
  (o:=(WilsonOriginalProjectedCurvaturePassport.paper D u).origin) («Γ»:=Γ) (lease (R:=R) (p:=p) (N:=N) hL)
theorem eligible (hL:L≤N) (w:V→ℝ) :
    (previous hL).Pays w (Y).p.supportExponent 0 (R.family.path.levels.clock.forcedAllowance L) :=
  WilsonOriginalScalarGallery.paid (lease (R:=R) (p:=p) (N:=N) hL)

variable [Nonempty V]
theorem original (hG:G.Simple) (hL:L≤N) (ready:∀s:Slot u,R.family.ref s.2.size≤L)
    (w:V→ℝ) (hw:∀i,0<w i) (x:tastes D) (U:Config G (R.family.side L p)) :
    let input := (ActualOriginalQInput.input Q D u μ orders hG N hL).leaf
      (testInclusion (ActualRunQlocalNativeTuple.orbit D) x)
    (new (previous hL)).density x U * Poly.pass (excluded x U) = input.density U := by
  intro input
  have e := WilsonOriginalProjectedCurvatureMaskCompletion.original Q D u μ orders N σ extra (previous hL)
    (eligible (R:=R) D u N hL w).budget (Y).p.exponent_pos.le hw hL x U
  have old := WilsonOriginalScalarGallery.density (o:=(WilsonOriginalProjectedCurvaturePassport.paper D u).origin)
    («Γ»:=Γ) (lease (R:=R) (p:=p) (N:=N) hL) hw x U
  have born := ActualOriginalQInput.density_full Q D u μ orders hG N hL ready
    (testInclusion (ActualRunQlocalNativeTuple.orbit D) x) U
  change input.density U=((Y).eval U:ℂ) • Poly.pass (q₀ x U) at born
  rw [old,smul_mul_assoc,one_mul] at e
  exact e.trans born.symm

theorem accepted (hG:G.Simple) (hL:L≤N) (ready:∀s:Slot u,R.family.ref s.2.size≤L)
    (w:V→ℝ) (hw:∀i,0<w i) (x:tastes D) (U:Config G (R.family.side L p))
    (pass:∀i,(S).clear i ∨ Healthy (Y).p.threshold ((S).ground i) U) :
    (new (previous hL)).density x U =
      ((ActualOriginalQInput.input Q D u μ orders hG N hL).leaf
        (testInclusion (ActualRunQlocalNativeTuple.orbit D) x)).density U := by
  have e := original Q D u μ orders N σ extra hG hL ready w hw x U
  rw [WilsonOriginalProjectedCurvatureIntake.clear Q D u μ orders N σ extra x U pass,Next.Rank.Exponential.pass_zero,mul_one] at e
  exact e

end YM.Integration.WilsonOriginalProjectedCurvatureStartingField
