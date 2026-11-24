import YM.Integration.FVA1Physical.MixedResets.SchoolTerm
import YM.Integration.FVA1Physical.Round2.CP5CommonRent

/-! The prescribed physical ultraviolet marked source on the *same* admitted
mixed course. The width is the numerical supplier's presold choice, independent
of cutoff, period and location. The graduate starts at the very X and K on
which the physical source identity holds. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalMarkedDefect

open Function Filter Finset Lattice Wilson RG RG.Supply Pressure Input Org Precision
open Next.Scheduling Next.Scheduling.Clock AnalyticBridge VerifiedReset ConnectedActivityE6 PhysicalNext Repeat
open Progress.DirectedRecipe Payments Push AbsoluteSums PriceCompiler
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV Pane ThroughLaunch
open Roost Legato Graces Extra.Iteration Extra.Histories
open Integration.LocalComparison VowsR QuadraticLocal.Mentor QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Affinity
open QuadraticLocal.Advent QuadraticLocal.Advent.Sycamore Marker QuadraticLocal.Tint QuadraticLocal.Syl RG3.Annuncia
open Next.Foundations FVA1Physical.Round2.Curvature FVA1Physical.Round2.CP5 FVA1Physical.MixedResets
open scoped Classical BigOperators

variable {G:Gauge} {I W:Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]
    {E:I→Type} [∀ i,AddCommGroup (E i)] [∀ i,Module ℝ (E i)]
    (R:PhysicalNext.Repeat.Legato.Run G) {m b n k N d:ℕ} (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
    (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
    (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:(j:ℕ)→RG.Rep G (R.family.side j n))
    {φ:ℕ→ℕ} (clock:Offices.Books D R.rolls Q φ) (school:School k)
    (ahead:Mentor.Forecast D R.rolls Q φ clock) {sx d₀ s:ℕ} {ε Hc zP η δ:ℝ}
    (lo:m≤b) (stop:b≤N) (K:∀ j:ℕ,∀ h:m≤j,j<N→Oak.Lesson R hk D Q π Γ h (N:=N))
    (marks:Census I) (u:W→I) (labels:I→ CoverLabel G d) (test:∀ i,E i→ₗ[ℝ]ℂ)
    (allowed:∀ i,Set (E i)) [Nonempty (Wallet (fun i=>allowed (u i)))]

set_option quotPrecheck false
local notation "C" => Replica u marks
local notation "Tests" => Wallet (fun j=>allowed (u j))
local notation "price" => (fun i=>fieldToll (nativeGrade (labels i)))
local notation "kernels" => (fun i=>(test i).ker)
local notation "gf" => Coat.gStep (Ψ b).beta
local notation "periods" => (fun j h hj=>K j h (lt_of_lt_of_le hj stop))

/-- The independent UV input, all original occupied weights and its complete
funded successor history. For a single mark use `I=W=Unit`, `u=id`; the
formula uses the actual charged place, its prescribed grade and its physical
fine coupling. No identification of separately chosen histories occurs. -/
theorem bought_birth
    (exam : Exams R hk D Q π Γ Ψ clock ahead stop school s sx d₀ Hc ε zP η δ lo K)
    (bounded : ∀ i x, x ∈ allowed i → ‖test i x‖ ≤ 1)
    (order : fieldHorizon (labels ∘ u) ≤ school.order) (load : Fintype.card W ≤ school.pieces)
    (names : (∑ j:W,fieldToll (nativeGrade (labels (u j)))) ≤ school.horizon) :
    let σ := Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J b)
    let original := engineering_fleet C (labels ∘ u) σ (fun j=>test (u j))
      (fun j=>allowed (u j)) (fun j=>bounded (u j))
    let w := original.choose
    0 < w ∧ ∀ o : I → Site (R.family.side b n),
      let P := stencilPassport labels o
      ∃ X : (Σ j:W,Fin (fieldCount (labels (u j)))) → Row (QuadraticLocal.Tariff.clone u P) C G Tests,
      ∃ F : Tint.Incoming (QuadraticLocal.Tariff.clone u P) (Ψ b) Tests Empty C,
        let initial := Boot.release R Ψ (fun j=>allowed (u j)) X F
        Academy.Prepared (φ:=φ) R D Ψ u allowed kernels (fun _=>w) price school ε Set.univ P X d₀ F ∧
        (∀ (t:Tests) U (S : (C).Mode), ((Tint.Patrol.picture X F).density t U).part S =
          ((Ψ b).eval U:ℂ)*(∏ j∈S.val, test (u j) (t j).val)*
            ∏ j∈S.val, ((gf^(nativeGrade (labels (u j))))⁻¹:ℝ) •
              (localSection G (labels (u j)).1.val).places (Pi.single (labels (u j)).2 1) (o (u j)) U) ∧
        ∃ (P' : (j:ℕ)→j≤b→Passport (R.family.side j n) I)
          (history : Academy.physicalCourse R P P')
          (H : (j:ℕ)→m≤j→j≤b→Pupil (Ψ j) C Tests),
          Graduate R hk D Q π Γ Ψ clock ahead stop periods u allowed kernels (fun _=>w) price school
            P' ε η s H sx δ initial P rfl history lo := by
  intro σ original w
  have source := graded_travel_at_rent R hk D Q π Γ Ψ clock school ahead lo stop K marks u labels test
    allowed Set.univ exam.paid bounded order load names
  refine ⟨source.1,?_⟩
  intro o P
  obtain ⟨X,F,prep,field,_⟩ := source.2 o
  let initial := Boot.release R Ψ (fun j=>allowed (u j)) X F
  obtain ⟨P',hist,H,bought⟩ := exam.support I W marks u E allowed kernels (fun _=>w) price
    (fun _=> source.1) P initial rfl prep.reachable
  exact ⟨X,F,prep,field,P',hist,H,bought⟩

end YM.Integration.WilsonPhysicalMarkedDefect

