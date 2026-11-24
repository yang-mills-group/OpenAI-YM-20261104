import YM.Integration.FVA1Physical.Round2.CP5BareFields
import YM.Integration.FVA1Physical.Round2.CP5EngineeringFleet
import YM.QuadraticLocal.Tariff.Labeling

/-! Enter the actual signed reclosure with the engineering-normalized
physical basis. Each individual replica retains its physical grade, its
test and its original slot on the initial density and every subsequent
step in the donated course. The purchase is made before positions. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.CP5
open Function Filter Finset Lattice YM.Wilson RG RG.Supply Pressure Input Org Precision
open Next.Scheduling Next.Scheduling.Clock AnalyticBridge VerifiedReset ConnectedActivityE6 PhysicalNext Repeat
open Progress.DirectedRecipe Payments Push AbsoluteSums PriceCompiler
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV Pane ThroughLaunch
open Roost Legato Graces Extra.Iteration Extra.Histories
open Integration.LocalComparison VowsR QuadraticLocal.Mentor QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Affinity
open QuadraticLocal.Advent QuadraticLocal.Advent.Sycamore Marker QuadraticLocal.Tint QuadraticLocal.Syl RG3.Annuncia
open Next.Foundations YM.Integration.FVA1Physical.Round2.Curvature
open scoped Classical BigOperators
variable {G:Gauge} {I W:Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]
variable {E:I→Type} [∀ i,AddCommGroup (E i)] [∀ i,Module ℝ (E i)]
variable (R:PhysicalNext.Repeat.Legato.Run G) {m b n k N d:ℕ}
variable (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
variable (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
variable (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:(j:ℕ)→RG.Rep G (R.family.side j n))
variable {φ:ℕ→ℕ} (Y:Offices.Books D R.rolls Q φ) (school:School k) (Qa:Mentor.Forecast D R.rolls Q φ Y)
variable {x₀ d₀ qx:ℕ} {ε Hc zP η δ:ℝ} (hm:m≤b) (hb:b≤N)
variable (K:∀ j:ℕ,∀ h:m≤j,j<N→Oak.Lesson R hk D Q π Γ h (N:=N))
variable (J:Census I) (u:W→I) (a:I → CoverLabel G d) (test:∀ i,E i→ₗ[ℝ]ℂ)
variable (A:∀ i,Set (E i)) [Nonempty (Wallet (fun i=>A (u i)))] (Sx:Set W)
local notation "JJ" => Replica u J
local notation "Tests" => Wallet (fun j=>A (u j))
local notation "tolls" => (fun i=>fieldToll (nativeGrade (a i)))
local notation "birth" => (Coat.gStep (Ψ b).beta)
local notation "kernels" => (fun i=>(test i).ker)
local notation "program" => (fun j h hj=>K j h (lt_of_lt_of_le hj hb))

def GradedTravel (w:ℝ) (o:I→Site (R.family.side b n)) : Prop :=
  let P := stencilPassport a o
  ∃ X:(Σ j:W, Fin (fieldCount (a (u j))))→Row (QuadraticLocal.Tariff.clone u P) JJ G Tests,
  ∃ V:Tint.Incoming (QuadraticLocal.Tariff.clone u P) (Ψ b) Tests Empty JJ,
    let entry := Boot.release R Ψ (fun j=>A (u j)) X V
    Academy.Prepared (φ:=φ) R D Ψ u A kernels (fun _=>w) tolls school ε Sx P X d₀ V ∧
    (∀ (t:Tests) U (s:(Replica u J).Mode), ((Tint.Patrol.picture X V).density t U).part s =
      ((Ψ b).eval U:ℂ) * (∏ j∈s.val,test (u j) (t j).val) *
        ∏ j∈s.val,((birth^(nativeGrade (a (u j))))⁻¹:ℝ) •
          (localSection G (a (u j)).1.val).places (Pi.single (a (u j)).2 1) (o (u j)) U) ∧
    ∃ (P':(j:ℕ)→j≤b→Passport (R.family.side j n) I) (coherent:Academy.physicalCourse R P P')
      (H:(j:ℕ)→m≤j→j≤b→Pupil (Ψ j) JJ Tests),
      Academy.Package R hk D Q π Γ Ψ Y u A kernels (fun _=>w) tolls school Qa x₀ ε Sx
        program entry hb H P rfl P' coherent η qx δ hm

theorem graded_travel
    (L:Boot.Marquee.Labeling R hk D Q π Γ Ψ Y school Qa x₀ d₀ ε Hc zP η δ qx hm hb K)
    (bounded:∀ i x,x∈A i→‖test i x‖≤1)
    (order:fieldHorizon (a ∘ u) ≤ school.order) (load:Fintype.card W ≤ school.pieces)
    (names:(∑ j:W,fieldToll (nativeGrade (a (u j)))) ≤ school.horizon) :
    ∃ w:ℝ, 0<w ∧ ∀ o:I→Site (R.family.side b n),
      GradedTravel (x₀:=x₀) (d₀:=d₀) (ε:=ε) (η:=η) (δ:=δ) (qx:=qx)
        R hk D Q π Γ Ψ Y school Qa hm hb K J u a test A Sx w o := by
  let σ := Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J b)
  obtain ⟨w,hw,fleet⟩ := engineering_fleet JJ (a ∘ u) σ (fun j=>test (u j))
    (fun j=>A (u j)) (fun j=>bounded (u j))
  refine ⟨w,hw,fun o=>?_⟩
  let P := stencilPassport a o
  obtain ⟨X₀,funds,tab,reads,modes⟩ := fleet _ (o ∘ u)
  let X : (Σ j:W, Fin (fieldCount (a (u j)))) → Row (QuadraticLocal.Tariff.clone u P) JJ G Tests := X₀
  let h := L.support I W J u E A kernels (fun _=>w) tolls (fun _=>hw) Sx P
  obtain ⟨V,prep⟩ := h.2 _ X (fleet_enlarge funds order load names) tab
  let entry := Boot.release R Ψ (fun j=>A (u j)) X V
  have voyage := h.1 entry rfl prep.reachable
  refine ⟨X,V,prep,?_,voyage⟩
  intro t U s
  let field (j:W) : ℂ := (test (u j) (t j).val) * (((birth^(nativeGrade (a (u j))))⁻¹:ℝ) •
    (localSection G (a (u j)).1.val).places (Pi.single (a (u j)).2 1) (o (u j)) U)
  have same (j:W) : field j=∑ z:Fin (fieldCount (a (u j))),(X ⟨j,z⟩).nominal birth t U := by
    refine Eq.trans ?_ (reads j t birth U)
    change _ * (((birth^(nativeGrade (a (u j))))⁻¹:ℝ) • _) = _
    rw [Complex.real_smul]
    exact mul_left_comm _ _ _
  refine (congrArg (fun z:Poly JJ=>z.part s) (prep.orientation.face t U).2.2).trans ?_
  rw [identified_rows JJ (QuadraticLocal.Tariff.clone u P) _ X modes birth t U field same,
    Poly.part_smul,Extra.Trajectories.pass_fire]
  unfold field
  rw [prod_mul_distrib,mul_assoc]

end YM.Integration.FVA1Physical.Round2.CP5
