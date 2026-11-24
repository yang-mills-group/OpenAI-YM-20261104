import YM.Integration.WilsonOriginalProjectedCurvatureLamps
import YM.Next.RANK.Exponential

/-! At the actual measured date, join the independent registered point layer
to a complete previously paid gallery. Its excluded terms keep their own
original masks before one passes to a surviving physical branch. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalProjectedCurvatureIntake
open Function Finset Lattice Wilson RG Source Labels Marker Ac
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Comparison.Density.RenderM MergeProof.Accent FVA1
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureCredits
open WilsonOriginalProjectedCurvaturePassport WilsonOriginalProjectedCurvatureEnvelope WilsonOriginalProjectedCurvatureSalary
open Extra.Trajectories QuadraticLocal
open scoped Classical BigOperators
variable {G : Gauge} {B : MS.Local.Physical.Deck G}
  {V : Type} [DecidableEq V] [Fintype V] {R : Run G} {p L n : ℕ} {hn : n ≤ L}
  (Q : MS.Land.Prescription B) (D : ActualRunQlocalNativeTuple.Datum R p L n hn V)
  (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ) (N : ℕ)
  (σ : ℝ) (extra : V → ℕ)
local notation "Group" => Funded Q D u μ orders N σ
local notation "Y" => R.family.path.rep N p L
local notation "g₀" => Pert.Asymptotics.regulatorRun R.family N p L
local notation "X" => WilsonOriginalProjectedCurvatureLamps.cohort Q D u μ orders N σ extra
local notation "S" => QuadraticLocal.Earn.rendered X (Y).p g₀
local notation "Γ" => Stock.census V
variable {J : Type}
local notation "old" => QuadraticLocal.Gallery (tastes D) J (paper D u).origin (Y) (Γ)
variable (b : old)

def picture (delta : V → ℕ) (prior : old) : QuadraticLocal.Gallery (tastes D) (Group ⊕ J) (paper D u).origin (Y) (Γ) :=
  ⟨(QuadraticLocal.Earn.rendered (WilsonOriginalProjectedCurvatureLamps.cohort Q D u μ orders N σ delta) (R.family.path.rep N p L).p g₀).join prior.E,prior.K⟩

def missed (x:tastes D) (U:Config G (R.family.side L p)) : Poly (Γ) :=
  ∑ i : Group, if (S).clear i ∨ Healthy (Y).p.threshold ((S).ground i) U then 0 else
    Poly.send ((S).mode i) ((S).nominal x i U)

local notation "q₀" x:max U:max => Mach (Γ) (fun i =>
  ActualRunQlocalNativeTuple.reader D i (testInclusion (ActualRunQlocalNativeTuple.orbit D) x i) *
  ActualOriginalCalibratedColumns.weightedObservable R B Q (u i) μ
    (R.family.side L p) (ActualRunQlocalNativeTuple.root D i) U (orders i))
local notation "Z" => picture Q D u μ orders N σ extra b
local notation "rejected" => missed Q D u μ orders N σ extra

theorem masked_sum (x:tastes D) (U:Config G (R.family.side L p)) (hL:L≤N) :
    (S).log x U + rejected x U = q₀ x U := by
  rw [← WilsonOriginalProjectedCurvatureLamps.original Q D u μ orders N σ extra (Y).p x U hL,
    QuadraticLocal.Lamps.log,tsum_fintype,missed,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : (S).clear i
  · simp [Lamps.frame,Lamps.light,h]
  · by_cases hU : Healthy (Y).p.threshold ((S).ground i) U
    · simp [Lamps.frame,Lamps.light,h,hU]
    · simp [Lamps.frame,Lamps.light,h,hU,Poly.send_zero]

theorem clear (x:tastes D) (U:Config G (R.family.side L p))
    (accept:∀i : Group, (S).clear i ∨ Healthy (Y).p.threshold ((S).ground i) U) :
    rejected x U = 0 := by simp [missed,accept]

end YM.Integration.WilsonOriginalProjectedCurvatureIntake
