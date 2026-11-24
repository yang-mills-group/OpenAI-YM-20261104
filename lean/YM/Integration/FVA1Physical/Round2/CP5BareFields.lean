import YM.Integration.FVA1Physical.Round2.CP5PhysicalFleet
import YM.Integration.FVA1Physical.Round2.CP5FieldProduct
import YM.Integration.FVA1Physical.Round2.CP5SourceSum
import YM.QuadraticLocal.Class.Registration

/-! Apply the donor's exact forced-partner construction to the real field
stencils. Its full unnormalized marker density has the original vacuum and
the exponential of precisely the prescribed test-weighted field insertions. -/
set_option autoImplicit false
set_option maxHeartbeats 1700000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.CP5
open Function Filter Finset Lattice YM.Wilson RG RG.Supply Pressure Input Org Precision
open Next.Scheduling Next.Scheduling.Clock AnalyticBridge VerifiedReset ConnectedActivityE6 PhysicalNext Repeat
open Progress.DirectedRecipe Payments Push AbsoluteSums PriceCompiler
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV Pane ThroughLaunch
open Roost Legato Graces Extra.Iteration Extra.Histories
open Integration.LocalComparison VowsR QuadraticLocal.Mentor QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Affinity
open QuadraticLocal.Advent.Sycamore Marker QuadraticLocal.Tint QuadraticLocal.Syl
open Next.Foundations YM.Integration.FVA1Physical.Round2.Curvature
open scoped Classical BigOperators
variable {G:Gauge} {I:Type} [Fintype I] [DecidableEq I] {d:ℕ} {n:Side}
variable {E:I→Type} [∀ i,AddCommGroup (E i)] [∀ i,Module ℝ (E i)]

theorem uncut_fields (R:Census I) (a:I → CoverLabel G d) (o:I→Site n) (test:∀ i,E i→ₗ[ℝ]ℂ)
    (A:∀ i,Set (E i)) (X:(Σ i,Fin (fieldCount (a i)))→Row (stencilPassport a o) R G (Wallet A))
    (mode:∀ p,(X p).mode=R.fire p.1)
    (reads:∀ i t g (U:Config G n),test i (t i).val*(localSection G (a i).1.val).places (Pi.single (a i).2 1) (o i) U =
      ∑ j:Fin (fieldCount (a i)),(X ⟨i,j⟩).nominal g t U) (g:ℝ) (t:Wallet A) (U:Config G n) :
    Spill.Foundry.uncut X g t U = fieldLog R a o test A t U :=
  identified_rows R (stencilPassport a o) _ X mode g t U _ (fun i=>reads i t g U)

theorem physical_bare_fields (R:PhysicalNext.Repeat.Legato.Run G) {m n j k N φ₀:ℕ}
    (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
    (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
    (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:(j:ℕ)→RG.Rep G (R.family.side j n))
    (con:Concourse R.alloy R.kit R.T π Γ m N n k Ψ) {φ:ℕ→ℕ}
    (C:VowsR.LawScroll G φ) (Q0:QuadraticLocal.Mentor.Offices.Books D R.rolls Q φ)
    (lic:VowsR.Chamber C R.kit D Q Q0) (hm:m≤j) (top:j≤N)
    (warm:Spill.Raffle.Warm G D R.alloy.delay φ) (hv:Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N))
    (J:Census I) (a:I → CoverLabel G d) (test:∀ i,E i→ₗ[ℝ]ℂ) (A:∀ i,Set (E i))
    (bounded:∀ i x,x∈A i→‖test i x‖≤1) (school:School k)
    (order:fieldHorizon a ≤ school.order) (load:Fintype.card I ≤ school.pieces)
    (names:Fintype.card I ≤ school.horizon) (floor:Boot.need φ₀ school ≤ R.alloy.B.a.clock.J j) :
    ∃ w:ℝ, 0<w ∧ ∀ o:I → Site (R.family.side j n),
      ∃ X:(Σ i,Fin (fieldCount (a i)))→Row (stencilPassport a o) J G (Wallet A),
      ∃ Y:Tint.Incoming (stencilPassport a o) (Ψ j) (Wallet A) Empty J,
        Boot.Bare (φ:=φ) R D Ψ A (fun i=>(test i).ker) (fun _=>w) (fun _=>1) school X φ₀ Y ∧
        ∀ t U, (Tint.Patrol.picture X Y).density t U =
           ((Ψ j).eval U:ℂ) • Poly.pass (fieldLog J a o test A t U) := by
  let σ:=Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J j)
  obtain ⟨w,hw,fleet⟩ := physical_analytic_fleet J a σ test A bounded
  refine ⟨w,hw,fun o=>?_⟩
  obtain ⟨X,funds,tab,reads,modes⟩ := fleet _ o
  have stronger : Scene.Armada X (fun _=>w) (fun _=>1) σ 1 school.order school.pieces school.horizon :=
    fleet_enlarge funds order load names
  obtain ⟨Y,hY⟩ := Boot.launching R hk D Q π Γ Ψ con C Q0 lic hm top A (fun i=>(test i).ker)
    (fun _=>w) (fun _=>1) school X stronger tab warm hv φ₀ floor
  refine ⟨X,Y,hY,fun t U=>?_⟩
  rw [(hY.face t U).2.2,uncut_fields J a o test A X (fun p=>(modes p).1) reads]

end YM.Integration.FVA1Physical.Round2.CP5
