import YM.Integration.WilsonOriginalProjectedCurvatureFoundry
import YM.Integration.WilsonOriginalProjectedCurvatureTableau

/-! The original hard rebooking carries the genuine marked test null spaces into the next step. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalProjectedCurvatureAffiliated
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

theorem original [Nonempty V] (P:Rep G (R.family.side L p)) {w:V→ℝ} {t:V→ℕ}
    {f b z c θ d :ℝ} {q h v:ℕ} (existing:Hard.Install P.activities P.p f b)
    (hA:Scene.Armada X w t σ c q h v)
    (hI:Invoice.Supports P.p z (P.p.supportExponent+1) g₀ σ θ) (hd:1≤d)
    (financed:Spill.allOver P.p^(q+v+1)*
        (Invoice.price P.p z (q+v+1) h (P.p.supportExponent+1) θ G*c)≤b*d)
    (hg:g₀=ConnectedActivityE6.Coat.gStep P.beta) (same:P.eval=(Y).eval)
    (hG:G.Simple) (hL:L≤N) (ready:∀s:Slot u,R.family.ref s.2.size≤L) :
    ∃ incoming:Tint.Incoming (paper D u) P (tastes D) Empty (Γ),
      Affinity.Taut (paper D u).support (WilsonOriginalProjectedCurvatureTableau.actors D)
        (fun i=>(WilsonOriginalProjectedCurvatureTableau.nulls D i).restrictScalars ℝ) incoming.old ∧
      Affinity.Crown (paper D u).support (WilsonOriginalProjectedCurvatureTableau.actors D)
        (fun i=>(WilsonOriginalProjectedCurvatureTableau.nulls D i).restrictScalars ℝ) incoming.hard ∧
      (∀ radius grade, incoming.old.Paid w grade radius 0) ∧
      incoming.hard.Paid w P.p.B P.p.supportExponent (d^h*f) ∧
      ∀ (x:tastes D) (U:Config G (R.family.side L p)),
        let input := (ActualOriginalQInput.input Q D u μ orders hG N hL).leaf
          (testInclusion (ActualRunQlocalNativeTuple.orbit D) x)
        (Tint.Patrol.picture X incoming).density x U=input.density U := by
  obtain ⟨F,a,⟨W⟩,rent⟩:=existing.room
  have registered:=Spill.Foundry.retention P g₀ W rent
    (WilsonOriginalProjectedCurvatureTableau.real D Q u μ orders N σ extra)
  refine ⟨Spill.Foundry.intake P X g₀ W rent,registered.1,registered.2,
    (fun radius grade=>Spill.Foundry.empty_lit P _ radius grade),Spill.Foundry.prices P X g₀ W rent hA hI hd financed,?_⟩
  intro x U input
  obtain ⟨_,_,value⟩:=Spill.Foundry.value P X g₀ W rent hA hI hd financed hg x U
  have born:=ActualOriginalQInput.density_full Q D u μ orders hG N hL ready
    (testInclusion (ActualRunQlocalNativeTuple.orbit D) x) U
  change input.density U=((Y).eval U:ℂ) • Poly.pass (q₀ x U) at born
  rw [value,WilsonOriginalProjectedCurvatureFoundry.uncut Q D u μ orders N σ extra hL x U,same,born]

end YM.Integration.WilsonOriginalProjectedCurvatureAffiliated
