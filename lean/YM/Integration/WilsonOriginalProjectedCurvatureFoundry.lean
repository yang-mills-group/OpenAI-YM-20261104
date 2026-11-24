import YM.Integration.WilsonOriginalProjectedCurvatureStartingField
import YM.QuadraticLocal.Class.Foundry

/-! Reinsert the independently filed signed curvature row on its own bad-field
event in the original forced gas of the received physical representation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalProjectedCurvatureFoundry
open Function Finset Lattice Wilson RG Source Labels Marker Ac
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Comparison.Density.RenderM MergeProof.Accent FVA1
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureCredits
open WilsonOriginalProjectedCurvaturePassport WilsonOriginalProjectedCurvatureEnvelope WilsonOriginalProjectedCurvatureSalary
open MergeProof MergeProof.Replicums QuadraticLocal QuadraticLocal.Earn
open scoped Classical BigOperators
variable {G : Gauge} {R : Run G} {B : MS.Local.Physical.Deck G}
  {p L n : ℕ} {hn : n≤L} {V : Type} [DecidableEq V] [Fintype V]
  (Q : MS.Land.Prescription B) (D : ActualRunQlocalNativeTuple.Datum R p L n hn V)
  (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ) (N : ℕ) (σ : ℝ) (extra : V → ℕ)
local notation "Y" => R.family.path.rep N p L
local notation "g₀" => Pert.Asymptotics.regulatorRun R.family N p L
local notation "X" => WilsonOriginalProjectedCurvatureLamps.cohort Q D u μ orders N σ extra
local notation "Γ" => Stock.census V
local notation "q₀" x:max U:max => Mach (Γ) (fun i =>
  ActualRunQlocalNativeTuple.reader D i (testInclusion (ActualRunQlocalNativeTuple.orbit D) x i) *
  ActualOriginalCalibratedColumns.weightedObservable R B Q (u i) μ
    (R.family.side L p) (ActualRunQlocalNativeTuple.root D i) U (orders i))

theorem uncut (hL:L≤N) (x:tastes D) (U:Config G (R.family.side L p)) :
    Spill.Foundry.uncut X g₀ x U=q₀ x U := by
  rw [Spill.Foundry.uncut,tsum_fintype]
  exact WilsonOriginalProjectedCurvatureLamps.original Q D u μ orders N σ extra (Y).p x U hL

theorem rejected (x:tastes D) (U:Config G (R.family.side L p)) :
    (Spill.shifts X (Y).p g₀).log x U =
      WilsonOriginalProjectedCurvatureIntake.missed Q D u μ orders N σ extra x U := by
  rw [Canopy.ShiftRows.log,tsum_fintype]
  rfl

theorem original [Nonempty V] (P:Rep G (R.family.side L p)) {w:V→ℝ} {t:V→ℕ}
    {f b z c θ d :ℝ} {q h v:ℕ} (existing:Hard.Install P.activities P.p f b)
    (hA:Scene.Armada X w t σ c q h v)
    (hI:Invoice.Supports P.p z (P.p.supportExponent+1) g₀ σ θ) (hd:1≤d)
    (financed:Spill.allOver P.p^(q+v+1)*
        (Invoice.price P.p z (q+v+1) h (P.p.supportExponent+1) θ G*c)≤b*d)
    (hg:g₀=ConnectedActivityE6.Coat.gStep P.beta) (same:P.eval=(Y).eval)
    (hG:G.Simple) (hL:L≤N) (ready:∀s:Slot u,R.family.ref s.2.size≤L) :
    ∃ incoming:Tint.Incoming (paper D u) P (tastes D) Empty (Γ),
      incoming.hard.Paid w P.p.B P.p.supportExponent (d^h*f) ∧
      ∀ (x:tastes D) (U:Config G (R.family.side L p)),
        let input := (ActualOriginalQInput.input Q D u μ orders hG N hL).leaf
          (testInclusion (ActualRunQlocalNativeTuple.orbit D) x)
        (Tint.Patrol.picture X incoming).density x U=input.density U := by
  obtain ⟨F,a,⟨W⟩,rent⟩:=existing.room
  refine ⟨Spill.Foundry.intake P X g₀ W rent,
    Spill.Foundry.prices P X g₀ W rent hA hI hd financed,?_⟩
  intro x U input
  obtain ⟨_,_,value⟩:=Spill.Foundry.value P X g₀ W rent hA hI hd financed hg x U
  have born:=ActualOriginalQInput.density_full Q D u μ orders hG N hL ready
    (testInclusion (ActualRunQlocalNativeTuple.orbit D) x) U
  change input.density U=((Y).eval U:ℂ) • Poly.pass (q₀ x U) at born
  rw [value,uncut Q D u μ orders N σ extra hL x U,same,born]

end YM.Integration.WilsonOriginalProjectedCurvatureFoundry
